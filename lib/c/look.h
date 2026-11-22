/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * look: irreducible leaves by certificate lookup, the Lean leaf solver `lookJ tabAll`.
 * A port of lib/python/zzn/look.py (same choices, same paths). The table is read once, on first
 * use, from the file named by the environment variable ZZN_LOOK_DATA, else from the path compiled
 * in as ZZN_LOOK_DATA_DEFAULT (the Makefile sets the absolute path of lib/data/look.json.gz).
 * Loading is thread-safe (C11 call_once); the loaded table is shared, read-only, and kept until
 * the process exits.
 */
#ifndef ZZN_LOOK_H
#define ZZN_LOOK_H

#include "zzn.h"

#ifdef __cplusplus
extern "C" {
#endif

/* What the lookup chose (look.py's trace): the canonical symmetry (index in `allSym`, bits 32 tr,
 * 16 rx, 8 ry, 4 r0, 2 r1, 1 sw), the slice index, and the entry: kind 0 a template pair, kind 1
 * a stored solution, with its index in the slice. slice = kind = index = -1 when there is no
 * answer. */
typedef struct { int sym, slice, kind, index; } zzn_look_info;

/* Load the table if not yet loaded: 0 on success, -1 if it cannot be loaded (a one-line message
 * goes to stderr, once). */
int zzn_look_load(void);

/* `lookJ tabAll` on in (Lean's x = row, y = column): 1 with *a (s0 -> t0) and *b (s1 -> t1)
 * filled (free a->cells, b->cells), 0 if the lookup has no answer, ZZN_INTERNAL if the table
 * cannot be loaded. The answer is not checked here. info may be NULL. */
int zzn_look_j(const zzn_instance *in, zzn_path *a, zzn_path *b, zzn_look_info *info);

#ifdef __cplusplus
}
#endif
#endif
