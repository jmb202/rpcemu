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

#define isblockvalid(l) (dcache)

//XXX: what is the meaning of all these magic numbers?
#define BLOCKS 1024

extern uint8_t rcodeblock[BLOCKS][1792];
extern uint32_t codeblockpc[0x8000];
extern int codeblocknum[0x8000];

extern uint8_t flaglookup[16][16];

#define BLOCKSTART 32

#define HASH(l) (((l)>>2)&0x7FFF)
