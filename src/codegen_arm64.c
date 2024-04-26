/*
  RPCEmu - An Acorn system emulator

  Copyright (C) 2005-2010 Sarah Walker

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

// aarch64 calling convention:
// x31   : sp/zero
// x30   : lr
// x29   : fp
// x19-28: callee-saved
// x18   : pr (or callee-saved)
// x17   : ip1 (scratch)
// x16   : ip0 (scratch)
// x9-15 : caller-saved
// x8    : xr (indirect result location)
// x0-x7 : arguments
//
// sp is always 16byte aligned at interfaces

// x28 -> ARMState
// x27 -> vwaddrl
// x26 -> vraddrl
// w25 = emulated PC
// x19-x24 are available, if stacked on entry
// x0-x17 are available for use without needing to stack anything
// (but will be corrupted by any function the generated code calls out to)

// Load/save arm64 condition flags (NZCV bits are 31:28):
// MRS xN, NZCV
// MSR NZCV, xN

#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "rpcemu.h"
#include "arm.h"
#include "arm_common.h"
#include "codegen_arm64.h"
#include "mem.h"

/* Condition codes */
#define CC_EQ 0
#define CC_NE 1
#define CC_CS 2
#define CC_CC 3
#define CC_MI 4
#define CC_PL 5
#define CC_VS 6
#define CC_VC 7
#define CC_HI 8
#define CC_LS 9
#define CC_GE 10
#define CC_LT 11
#define CC_GT 12
#define CC_LE 13
#define CC_AL 14
#define CC_NV 15

// Pointless compatibility
int lastflagchange;

// Each code block has the following structure:
//
// +0       Function epilogue (e bytes)
// +e       Unused space between end of epilogue and BLOCKSTART (x bytes)
// +e+x     Function prologue (p bytes)
// +e+x+p   Function body (b bytes)
// +e+x+p+b Function cleanup (c bytes)
//
// and the total block size is 1792 bytes, so with fixed-size e/x/p/c,
// b is at most 1792 - (e+x+p+c) bytes, and e+x == BLOCKSTART
uint8_t rcodeblock[BLOCKS][1792] __attribute__ ((aligned (4096)));
// codeblockaddr stores the address of each block
static const void *codeblockaddr[BLOCKS];
// codeblockpc maps blocknum to emulated address
uint32_t codeblockpc[0x8000];
// codeblocknum maps blocknum to block pointer
int codeblocknum[0x8000];
// codeblockpresent flags whether codeblocks exist for a page
static uint8_t codeblockpresent[0x10000];

// current block pointers (they're indices, clearly)
static int blockpoint, blockpoint2;
// blocks maps block pointer to blocknum
static uint32_t blocks[BLOCKS];

// codeblockpos is the offset of the next free byte in the current codeblock
static int codeblockpos;
// block_enter is the codeblockpos immediately after the block prologue
static int block_enter;
// codeblockpos of the last forward branch (whose destination was unknown
// when generated) -- it must be filled in later
static int lastjumppos;

// count of instructions emulated so far in this execution
static int tempinscount;
// running count of bytes to increment the emulated PC by
static int pcinc;

static inline void
addlong(uint32_t a)
{
	memcpy(&rcodeblock[blockpoint2][codeblockpos], &a, sizeof(uint32_t));
	codeblockpos += 4;
}

static inline void
addptr64(const uintptr_t a)
{
	memcpy(&rcodeblock[blockpoint2][codeblockpos], &a, sizeof(uintptr_t));
	codeblockpos += 8;
}

/**
 * Write an arm64 instruction to the current codeblock.
 *
 * \param i opcode to write
 *
 * We assume little-endian operation.
 */
static inline void
gen_instr(uint32_t i)
{
	rcodeblock[blockpoint2][codeblockpos++] = i & 0xff;
	rcodeblock[blockpoint2][codeblockpos++] = (i >> 8) & 0xff;
	rcodeblock[blockpoint2][codeblockpos++] = (i >> 16) & 0xff;
	rcodeblock[blockpoint2][codeblockpos++] = (i >> 24) & 0xff;
}

/**
 * Generate a conditional branch within the current codeblock.
 *
 * \param condition Branch condition code (CC_*)
 * \param destination Offset within codeblock of instruction to branch to
 */
static inline void
gen_inblock_branch(int condition, int destination)
{
	int rel = destination - codeblockpos;

	// B.cond rel
	gen_instr(0x54000000 |
		  ((rel >> 2) & 0x7ffff) << 5 | // imm19
		  (condition & 0xf));
}

/**
 * Complete a pending conditional branch within the current codeblock.
 */
static inline void
gen_pending_branch(void)
{
	if (lastjumppos != 0) {
		int rel = codeblockpos - lastjumppos;
		uint32_t instr =
			(rcodeblock[blockpoint2][lastjumppos]) |
			(rcodeblock[blockpoint2][lastjumppos+1] << 8) |
			(rcodeblock[blockpoint2][lastjumppos+2] << 16) |
			(rcodeblock[blockpoint2][lastjumppos+3] << 24);
		instr |= ((rel >> 2) & 0x7ffff) << 5; // imm19
		rcodeblock[blockpoint2][lastjumppos] = instr & 0xff;
		rcodeblock[blockpoint2][lastjumppos+1] = (instr >> 8) & 0xff;
		rcodeblock[blockpoint2][lastjumppos+2] = (instr >> 16) & 0xff;
		rcodeblock[blockpoint2][lastjumppos+3] = (instr >> 24) & 0xff;
		lastjumppos = 0;
	}
}

/**
 * Compute a PC-relative address and place it in the specified register.
 *
 * \param addr Absolute address to relativise
 * \param reg Register into which to place PC-relative address
 */
static inline void
gen_pcrel(const void *addr, int reg)
{
	const char *pc = (const char *) &rcodeblock[blockpoint2][codeblockpos];
	ptrdiff_t rel = ((const char *) addr) - pc;

	if (-1048576 <= rel && rel <= 1048575) {
		// ADR x<reg>, rel
		gen_instr(0x10000000 |
			  (((uint32_t) (rel & 0x3)) << 29) | // immlo
			  (((uint32_t) (rel >> 2) & 0x7fff) << 5) | // immhi
			  (reg & 0x1f)); // rd
	} else {
		uintptr_t addrpage = (((uintptr_t) addr) >> 12) << 12;
		uintptr_t pcpage = (((uintptr_t) pc) >> 12) << 12;
		ptrdiff_t pageoff = ((const char *) addrpage) - ((const char *) pcpage);
		ptrdiff_t bytesoff = ((const char *) addr) - ((const char *) addrpage);

		// ADRP x<reg>, pageoff
		gen_instr(0x90000000 |
			  (((uint32_t) (pageoff >> 12) & 0x3) << 29) | // immlo
			  (((uint32_t) (pageoff >> 14) & 0x7fff) << 5) | // immhi
			  (reg & 0x1f)); // rd

		// ADD x<reg>, x<reg>, #bytesoff
		gen_instr(0x91000000 |
			  ((bytesoff & 0xfff) << 10) | // imm12
			  ((reg & 0x1f) << 5) | // rn
			  (reg & 0x1f)); // rd
	}
}

/**
 * Initialise codeblock structures
 */
void initcodeblocks(void)
{
	int c;

	// Clear all blocks
	memset(codeblockpc, 0xff, sizeof(codeblockpc));
	memset(blocks, 0xff, sizeof(blocks));
	for (c = 0; c < BLOCKS; c++) {
		codeblockaddr[c] = &rcodeblock[c][0];
	}
	blockpoint = 0;

	// Set memory pages containing rcodeblock[]s executable -
	// necessary when NX/XD feature is active on CPU(s)
	set_memory_executable(rcodeblock, sizeof(rcodeblock));
}

/**
 * Reset codeblock structures
 */
void resetcodeblocks(void)
{
	int c;

	blockpoint = 0;

	for (c = 0; c < BLOCKS; c++) {
		if (blocks[c] != 0xffffffff) {
			codeblockpc[blocks[c] & 0x7fff] = 0xffffffff;
			codeblocknum[blocks[c] & 0x7fff] = 0xffffffff;
			blocks[c] = 0xffffffff;
		}
	}
}

/**
 * Clear a cache page
 *
 * \param a Address of page to clear
 */
void cacheclearpage(uint32_t a)
{
	int c, d;

	if (!codeblockpresent[a & 0xffff]) {
		return;
	}
	codeblockpresent[a & 0xffff] = 0;
	d = HASH(a << 12);
	for (c = 0; c < 0x400; c++) {
		if ((codeblockpc[c + d] >> 12) == a) {
			codeblockpc[c + d] = 0xffffffff;
		}
	}
}

/**
 * Emit instructions to update the emulated PC
 */
void generateupdatepc(void)
{
	while (pcinc > 0) {
		int to_add = pcinc < 4096 ? pcinc : 4095;

		// ADD w25, w25, #to_add
		gen_instr(0x11000339 | (to_add << 10));

		pcinc -= to_add;
	}
}

/**
 * Advance emulated PC, emitting update instructions if needed
 */
void generatepcinc(void)
{
	lastjumppos = 0;
	tempinscount++;
	pcinc += 4;
	if (pcinc == 124) {
		generateupdatepc();
	}
	if (codeblockpos >= 1200) {
		blockend = 1;
	}
}

/**
 * Emit instructions to update the emulated instruction counter
 */
void generateupdateinscount(void)
{
	if (tempinscount != 0) {
		// x0 -> inscount
		gen_pcrel(&inscount, 0);

		gen_instr(0xb9400001); // LDR w1, [x0]

		while (tempinscount > 0) {
			int to_add = tempinscount < 4096 ? tempinscount : 4095;

			// ADD w1, w1, #to_add
			gen_instr(0x11000021 | (to_add << 10));

			tempinscount -= to_add;
		}

		gen_instr(0xb9000001); // STR w1, [x0]
	}
}

/**
 * Emit instructions to test the conditions for an emulated
 * conditional instruction
 *
 * \param opcode ARM32 opcode to emulate
 * \param pcpsr Pointer to emulated PSR
 */
void generateflagtestandbranch(uint32_t opcode, uint32_t *pcpsr)
{
	//XXX: optimise?

	gen_pcrel(&flaglookup[opcode>>28][0],	// x17 -> &flaglookup[opcode>>28][0]
		  17);
	if (pcpsr == &arm.reg[15]) {
		gen_instr(0x2a1903e0);		// MOV w0, w25
	} else {
		gen_pcrel(pcpsr, 0);		// x0 -> pcpsr
		gen_instr(0xb9400000);		// LDR w0, [x0]
	}
	gen_instr(0x531c7c00);			// LSR w0, w0, #28
	gen_instr(0x38606a20);			// LDRB w0, [x17, x0]
	lastjumppos = codeblockpos;
	gen_instr(0xb4000000);			// CBZ x0, ?
}

/**
 * Emit instructions to emulate opcode
 *
 * \param addr Address of instruction implementation
 * \param opcode ARM32 opcode to emulate
 * \param pcpsr Pointer to emulated PSR
 */
void generatecall(OpFn addr, uint32_t opcode, uint32_t *pcpsr)
{
	//XXX: implement recompilation

	/* Fall back to C implementation */
	gen_instr(0x52a00000 |			// MOVZ w0, (opcode & 0xffff0000)
		  ((opcode & 0xffff0000) >> 11));
	gen_instr(0x52800001 |			// MOVZ w1, (opcode & 0xffff)
		  ((opcode & 0xffff) << 5));
	gen_instr(0x2a010000);			// ORR w0, w0, w1

	gen_instr(0xb9003f99);			// STR w25, [x28, #(15*4)]
	gen_pcrel(addr, 17);			// x17 -> addr
	gen_instr(0xd63f0220);			// BLR x17
	gen_instr(0xb9403f99);			// LDR w25, [x28, #(15*4)]

	if (!flaglookup[opcode >> 28][(*pcpsr) >> 28] &&
			(opcode & 0x0e000000) == 0x0a000000) {
		generateupdatepc();
		gen_inblock_branch(CC_AL, 0);	// B <epilogue>
	}

	gen_pending_branch();
}

/**
 * Emit instructions to check if an IRQ^Wabort occurred and exit if so
 */
void generateirqtest(void)
{
	//XXX: nothing to do if last instruction was recompiled?

	// x0 contains the result of the last OpFn executed

	// CBNZ x0, <epilogue>
	gen_instr(0xb5000000 |
		  ((-codeblockpos >> 2) & 0x7ffff) << 5); // imm19

	gen_pending_branch();
}

/**
 * Emit instructions to terminate the current codeblock
 *
 * \param opcode ARM32 opcode of last instruction in the codeblock
 */
void endblock(uint32_t opcode)
{
	NOT_USED(opcode);

	generateupdatepc();
	generateupdateinscount();

	// if (--linecyc < 0) { goto epilogue; }
	gen_pcrel(&linecyc, 0);			// x0 -> linecyc
	gen_instr(0xb9400001);			// LDR w1, [x0]
	gen_instr(0x71000421);			// SUBS w1, w1, #1
	gen_instr(0xb9000001);			// STR w1, [x0]
	gen_inblock_branch(CC_MI, 0);		// B.MI <epilogue>

	// if (arm.event & 0xff) { goto epilogue; }
	gen_instr(0xb9400380 |			// LDR w0, [x28, #event]
		  ((offsetof(ARMState, event) >> 2) & 0xfff) << 10);
	gen_instr(0x72001c1f);			// TST w0, #ff
	gen_inblock_branch(CC_NE, 0);		// B.NE <epilogue>

	gen_pcrel(&codeblockpc[0], 11);		// x11 -> codeblockpc
	gen_pcrel(&codeblocknum[0], 10);	// x10 -> codeblocknum
	gen_pcrel(&codeblockaddr[0], 9);	// x9 -> codeblockaddr

	// addr = pc - 8;
	// noflags = addr & arm.r15_mask;
	gen_instr(0xb9400381 |			// LDR w1, [x28, #r15_mask]
		  ((offsetof(ARMState, r15_mask) >> 2) & 0xfff) << 10);
	gen_instr(0x51002320);			// SUB w0, w25, #8
	gen_instr(0x0a010001);			// AND w1, w0, w1

	// blocknum = HASH(addr)
	gen_instr(0x53024000);			// UBFX w0, w0, #2, #15

	// if (codeblockpc[blocknum] != noflags) { goto epilogue; }
	gen_instr(0xb8606962);			// LDR w2, [x11, x0]
	gen_instr(0x6b01005f);			// CMP w2, w1
	gen_inblock_branch(CC_NE, 0);		// B.NE <epilogue>

	// nextblock = codeblockaddr[codeblocknum[blocknum]];
	gen_instr(0xb8606942);			// LDR w2, [x10, x0]
	gen_instr(0xf8625920);			// LDR x0, [x9, w2, UXTW #3]

	// goto (nextblock+block_enter)
	gen_instr(0x91000000 |			// ADD x0, x0, #block_enter
		  ((block_enter & 0xfff) << 10));
	gen_instr(0xd61f0000);			// BR x0
}

/**
 * (Re)Initialise a codeblock
 *
 * \param l Logical address of first emulated instruction
 */
void initcodeblock(uint32_t l)
{
	int blocknum = HASH(l);

	codeblockpresent[(l >> 12) & 0xffff] = 1;
	blockpoint++;
	blockpoint &= (BLOCKS - 1);
	if (blocks[blockpoint] != 0xffffffff) {
		// Block in-use: invalidate prior usage
		codeblockpc[blocks[blockpoint] & 0x7fff] = 0xffffffff;
		codeblocknum[blocks[blockpoint] & 0x7fff] = 0xffffffff;
	}

	codeblockpc[blocknum] = l;
	codeblocknum[blocknum] = blockpoint;
	blocks[blockpoint] = blocknum;
	blockpoint2 = blockpoint;

	// Block epilogue
	codeblockpos = 0;
	gen_instr(0xb9003f99);			// STR w25, [x28, #(15*4)]
	gen_instr(0xa8c16bf9);			// LDP x25, x26, [sp], 16
	gen_instr(0xa8c173fb);			// LDP x27, x28, [sp], 16
	gen_instr(0xa8c17bfd);			// LDP x29, x30, [sp], 16
	gen_instr(0xd65f03c0);			// RET

	// Block prologue
	assert(codeblockpos <= BLOCKSTART);
	codeblockpos = BLOCKSTART;
	gen_instr(0xa9bf7bfd);			// STP x29, x30, [sp, -16]!
	gen_instr(0x910003fd);			// MOV x29, sp
	gen_instr(0xa9bf73fb);			// STP x27, x28, [sp, -16]!
	gen_instr(0xa9bf6bf9);			// STP x25, x26, [sp, -16]!
	gen_pcrel(&arm, 28);			// x28 -> arm
	gen_pcrel(&vwaddrl[0], 27);		// x27 -> vwaddrl
	gen_pcrel(&vraddrl[0], 26);		// x26 -> vraddrl
	gen_instr(0xb9403f99);			// LDR w25, [x28, #(15*4)]
	block_enter = codeblockpos;
}
