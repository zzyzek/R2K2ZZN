# Two-color Zig-Zag Numberlink on rectangles: the proof in prose

This document gives the whole argument in prose. The paper (`paper/`) presents it with figures and
the algorithm in pseudocode, `docs/ALGORITHM.md` is a shorter reference, and the Lean proof
(`proof/`) checks it. Terms are defined in §1.

**Status.**
- **Theorem A** (passes ⇒ solvable, for both sides ≥ 11) and **Theorem B** (every catalogue entry
  is sound) are proved, and checked in Lean (`proof/README.md`):
  - `passes_iff_solvable`: for both sides ≥ 11, passing the catalogue is equivalent to
    solvability;
  - `solvableB_iff`: a decision procedure proved correct for every rectangle; thin rectangles use
    a plug DP proved sound and complete (`thinBF_iff`).
- The finite computations are certificates checked by the Lean kernel (`proof/`, the paper,
  Section 9).
- The decision procedure's running time is also proved in Lean, in a step-counting model:
  `ZZN.T.solvableBT_time` bounds its steps by `Cdec · (RC + R + C + 1)`. The constant `Cdec` (about
  10^756) comes from a crude count of plug DP states.
- The construction (§8) is a Lean function, `ZZN.solveZZN`, proved sound and complete. Its steps
  are bounded by `ZZN.T.solveZZNT_time`, a polynomial of degree 5 in the longer side with a
  constant of about 10^3500, from the same state count.
- The Lean version organizes the finite computations differently from §5 below. Band
  compressions (deleting two free lines whose neighbourhood is empty) leave irreducible instances
  only in boxes with sides 11–16; sides 17–22 are proved to have none (`ZZN/BoxK/None.lean`). The
  21 boxes are covered by slice certificates, one per set of four endpoint rows, up to the box's
  symmetries (`proof/BoxKGen`, `docs/DISCHARGE.html`).

---

## 1. Definitions

- **Instance.** An N0 × N1 grid (N0 rows, N1 columns) with four distinct cells s0, t0 (color 0,
  in the figures green) and s1, t1 (color 1, orange), the *endpoints*.
- **Solution.** Two vertex-disjoint paths, s0–t0 and s1–t1, that together visit every cell. The
  instance is *solvable* if it has one.
- **Checkerboard color.** Cell (r, c) is black if r + c is even, white otherwise.
- **Passes.** No entry of the forbidden-pattern catalogue fires. The catalogue is listed in the
  paper (Table 1 and Appendix C); it is defined as `fires` in the libraries (`lib/`) and as `fires3`
  in `proof/ZZN/Statement.lean`.
  - **Proved entries:** P (parity), T1, T2, L1–L6, E1, and R (rewrites R1–R3 with effective
    alternation).
  - **Verified-only entries:** B (21 + 5 boundary-only corner patterns), C (36 corner
    configurations, R·C even), D (3, R·C odd).
- **Thin.** The short side is ≤ 10.
- **The domain 𝔇.** Instances with both sides ≥ 11.
- **Line.** A full row or a full column. A *gap* on an axis is a maximal run of consecutive lines
  holding no endpoint:
  - an *edge gap* touches the border;
  - an *internal gap* lies between two endpoint lines.
- **IPS.** The Itai–Papadimitriou–Szwarcfiter theorem (1982). It decides exactly when an m × n
  rectangle has a Hamiltonian path between two given cells: color compatibility, plus three
  forbidden families at widths 1, 2 and 3. It is formalized in `proof/GridHam`.
- **Plug DP.** An exact dynamic programming algorithm over the grid (`docs/PLUGDP.md`). It decides solvability,
  in time linear in the long side for a fixed short side.

### Cuts and moves

A **cut** is a straight line between two adjacent rows (or columns), splitting the rectangle into
pieces *a* and *b*. Where a path crosses the cut, the two cells on either side of the crossing are
a **crossing pair**. Each becomes a **virtual endpoint** of its piece. A **move** is a cut with a
choice of crossings. It is **valid** when every piece is **OK**:
- a *one-path piece* (two endpoints) is OK when IPS accepts it;
- a *two-path piece* (four distinct endpoints) is OK when it is either:
  - thin and solvable, decided exactly by the plug DP; or
  - not thin and passes.

The move types, by how the four real endpoints fall:

| Type | Endpoints on side a | Pieces |
|---|---|---|
| strip | 4 or 0 | the side with the endpoints (two-path), and the empty side *f* (no path; must have even area and both sides ≥ 2) |
| 1/3 split | 1 or 3 | the lone endpoint's piece (one-path, to its crossing), and the rest (two-path: the lone path's mate to its crossing, plus the other pair) |
| 2/2 same | each side holds one whole pair | two one-path pieces, no crossing |
| 2/2 cross | each side holds one endpoint of each color | two two-path pieces, two crossings |
| excursion | each side holds one whole pair | one color crosses twice. Near piece: its two segments as a two-path instance. Far piece: the other pair plus the excursion, as a two-path instance. |

In Lean, an accepted move is `MoveOK` (`proof/ZZN/Moves.lean`).

---

## 2. The theorems

**Theorem A.** Every instance in 𝔇 that passes is solvable.

**Theorem B.** Every catalogue entry is sound on 𝔇 (§4.7 and §7). Hence solvability of
two-color Zig-Zag Numberlink on rectangles is decidable in polynomial time:
- outside 𝔇 (some side ≤ 10), by the plug DP;
- inside 𝔇, by the catalogue.

A solution is constructed in polynomial time (§8).

---

## 3. Proof of Theorem A: the induction

Induction on the area N0·N1 over 𝔇. Let R ∈ 𝔇 pass. Check the cases in this order; one of them
always applies.

1. **Base box: both sides ≤ 16.** Every configuration of every such box has been checked: it is
   either solvable or has a valid move (§5.1).
2. **A reduction applies.** It produces a passing R′ ∈ 𝔇 of smaller area. R′ is solvable by
   induction, and R is solvable by the reduction's lifting lemma. The reductions, on either axis
   of length n:
   - **(S) strip:** an edge gap of ≥ 4 lines, and n − 2 ≥ 11 (§4.3);
   - **(K) compression:** an internal gap of ≥ 10 lines, and n − 2 ≥ 11 (§4.4);
   - **(I) interior compression:** an internal gap of ≥ 3 lines containing two lines d, d+1 with
     8 ≤ d ≤ n − 10 (§4.5);
   - **(Q) same-color split:** a cut inside a middle gap whose two one-path pieces both pass IPS
     (§4.6). This one doesn't recurse: both pieces are solved directly.
3. **Leftover family 𝔉:** R is not a base box and no reduction applies. 𝔉 is finite (long sides
   ≤ 22), and every passing member has a valid move (§5.2).

**Valid move ⇒ solvable** (§4.1):
- one-path pieces are solvable by IPS;
- thin two-path pieces are solvable by the plug DP's verdict;
- non-thin two-path pieces pass, lie in 𝔇 (both sides ≥ 11, since they aren't thin), and have
  smaller area, so they are solvable by induction.

The pieces' solutions glue together.

**Symmetry.** The catalogue, the moves and the reductions all commute with the 8 symmetries of
the rectangle, with swapping the colors, and with swapping s and t within a color. So the
computations need only one representative of each orbit. ∎ (modulo §4–§6)

---

## 4. Lemmas

### 4.1 Gluing: a valid move gives a solution

Fix solutions of the pieces.
- **1/3 split.** Join the lone piece's path (lone → its crossing cell) and the rest's path (the
  mate's crossing cell → the mate) by the crossing edge.
- **2/2 cross.** The same, at both crossings.
- **2/2 same.** The two paths are already disjoint and cover everything.
- **Excursion.** The path runs s → (near segment) → crossing → (far excursion) → crossing →
  (near segment) → t. The far piece's excursion pair is exactly the two far crossing cells.
- **Strip.** Let s be the piece with the endpoints and f the empty piece, w × L, where L ≥ 11 is
  the cut length.
  - Let K be the line of s next to the cut. Its cells cannot use an edge across the cut. If no
    edge along K were used, every cell of K would have degree ≤ 1, i.e. be an endpoint, which
    needs L ≤ 4. So some edge e along K is used.
  - **If w is even,** add f two lines at a time. Each 2 × L block has a Hamiltonian cycle (its
    boundary), which contains the edge next to e. The square flip merges it into the path through
    e. After the first block, the new line next to the cut has no endpoints, so it has a used
    edge along it too.
  - **If w is odd,** then L is even (f has even area). f has a Hamiltonian cycle containing every
    edge of its side next to the cut: down that side, then back up in a serpentine through the
    remaining columns, two rows at a time. Flip it with e.

  In every case the result is two disjoint paths with the original endpoints, covering
  everything. ∎

### 4.2 Band extension

**Lemma.** If R′ is solvable and some full line of R′ holds no endpoint, then inserting two
empty lines next to that line gives a solvable instance. There is no length condition.

**Proof** (Lean: `proof/ZZN/BandExtension.lean`):
1. Extend every path crossing the insertion line straight through the two new lines.
2. Absorb each block of new cells between consecutive crossings by a U-shaped detour of a
   neighbouring crossing.
3. Absorb the one block left over by a square flip with an edge along the endpoint-free line. A
   counting argument shows that edge exists: m crossing cells supply at most m horizontal edges,
   and the m + 1 runs between them need at least m + 1.

**Corroboration:** F^k ⊆ F^(k+2) for every boundary state at widths 2–9, computed during development.

### 4.3 Strip (S)

- **Lifting:** §4.1 with w = 2 (Lean: `proof/ZZN/StripExtend.lean`).
- **Passing is preserved** (Lean: `proof/ZZN/PassStrip.lean`). It needs an edge gap of ≥ 4 lines and
  n − 2 ≥ 11. Every size condition in the catalogue is monotone, so it holds on R whenever it holds
  on R′.

### 4.4 Compression (K)

- **Lifting:** band extension (§4.2).
- **Passing is preserved** (Lean: `proof/ZZN/PassX.lean`, `proof/ZZN/PassXAssemble.lean`). Delete the two middle lines of an
  internal gap of G ≥ 10 lines. Every catalogue entry fires on R iff it fires on R′:
  - the 8 × 8 corner windows see the same cells, because G − 2 ≥ 8 empty lines remain;
  - the boundary cyclic order is unchanged;
  - the size and parity conditions are unchanged or monotone.

### 4.5 Interior compression (I)

- **Lifting:** band extension.
- **Passing is preserved** (Lean: `proof/ZZN/PassX.lean`, `proof/ZZN/PassXR.lean`), entry by entry.
  - Let φ insert the two lines at position d, with 8 ≤ d ≤ n − 10. Then φ fixes the first 8 and
    the last 8 lines, so every corner window is identical, and it never moves an endpoint toward
    a corner.
  - A gap of ≥ 3 lines leaves ≥ 1 empty line between the two endpoint lines. That stops T2, L1
    and the transposed E1 from firing newly.

### 4.6 Same-color split (Q)

Both pieces are one-path problems and IPS is exact, so if both pass IPS each has a Hamiltonian
path. They are disjoint and cover R.

This replaces an earlier, wrong claim: "a middle gap of ≥ 6 always admits such a cut". It fails
on checkerboard color compatibility, e.g. an even cut-line length with a pair on the same color.
The computation of §5.2 was redone for the instances the wrong claim had skipped.

### 4.7 Soundness of the proved catalogue entries (used only by Theorem B)

P, T1 and T2: parity and planarity. L1–L6 and E1: local forcing. R1–R3 and effective alternation:
forced corner routes, then T1 on the remaining region. Lean: `proof/ZZN/Parity.lean`,
`SoundT1.lean`, `SoundT2.lean`, `SoundLocal.lean` and `SoundR.lean`. The entries B, C and D are
sound by window certificates (`proof/ZZN/WinBCD.lean`, `proof/WinKU/Facts.lean`).

---

## 5. The computations

These are the computations of the original computer-assisted proof; the Lean development replaces
them with its own box checks (see Status). "Canonical" means one representative per symmetry orbit
(§3).

### 5.1 Base boxes (both sides 11–16)

| Boxes | Method | Result |
|---|---|---|
| 11 × 11, 11 × 12, 12 × 12 | *coverage*: each passing configuration is shown solvable directly, by an IPS decomposition (CERT), by peeling empty strips and solving exactly (PEEL), or by an exact solve (FULL_FEAS) | 807,180 / 3,443,870 / 2,446,945 configurations, 0 misses |
| every other box with sides 11–16 | *one-step*: each passing configuration has a valid move (§1) | about 2.5 × 10⁸ configurations, all have a move; 2 needed the excursion |

For the one-step boxes, non-thin pieces fall into smaller boxes of 𝔇. That is exactly what the
induction of §3 needs.

### 5.2 The leftover family 𝔉

**Definition.** Per axis of length n, sorted endpoint
coordinates c1 ≤ c2 ≤ c3 ≤ c4, with (when n − 2 ≥ 11):
- edge gaps ≤ 3;
- internal gaps ≤ 9;
- no internal gap of ≥ 3 lines containing two lines d, d+1 with 8 ≤ d ≤ n − 10.

On top of that, no same-color split passes IPS (§4.6). Boxes with both sides ≤ 16 are excluded,
as base boxes.

**Per-side tuple counts** (C and Python agree): 11:1001, 12:1365, 13:885, 14:1031, 15:1163,
16:1272, 17:1352, 18:480, 19:304, 20:96, 21:48, 22:16, and 0 from 23 (enumerated up to 40).

**𝔉 is finite (proved; Lean `redX_of_wide`).** A side n ≥ 23 always has a reduction:
- if neither strip applies, some endpoint has coordinate ≤ 3 and another ≥ n − 4 ≥ 19;
- so at most two endpoint lines fall in lines 7–15;
- so one of the windows 7–9, 10–12, 13–15 is endpoint-free;
- its middle line, or line 8 for the first window, gives an interior compression with
  8 ≤ d ≤ 13 ≤ n − 10.

**Result:**
- **Main run** (sides 11–22, every box with a side ≥ 17): 97,767,047 canonical parity-OK instances
  checked; 238,215 fail the catalogue; **all 97,528,832 others have a valid move**.
- **Supplementary run:** the 2,082,096 instances that the original, too-generous same-color rule had skipped:
  **all have a valid move**.

Together these cover every member of 𝔉 under the exact same-color rule.

Moves used in the main run: strip 43.0 M, 1/3 split 49.3 M, 2/2 cross 4.6 M, 2/2 same 0.37 M, excursion
0.35 M. Time: about 1 h on 4 processes.

---

## 6. What is trusted

In the Lean development:
- Lean's kernel and the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
- the definitions of the statements, `proof/ZZN/Statement.lean` (grids, instances, solutions, the
  catalogue, the plug DP, the decision procedure and the construction).

The programs used for the original computations of §5 (a C catalogue, plug DP, IPS test and move
checker, and a Python window-certificate program) are no longer part of the trusted base. They were
cross-checked against each other during development and later against the Lean definitions.

---

## 7. Status and open questions

1. **Soundness of B, C and D on all of 𝔇:** a window certificate per entry shows that no covering
   of a 6 × 6 or 8 × 8 corner window extends outside, by parity, planarity and global path
   structure, for any grid size. All 65 entries are certified, so every catalogue entry is sound
   on 𝔇 and **Theorem B holds**. In Lean the certificates are checked by the kernel.
2. **Lean formalization:** complete (see Status). No `sorry`; the axioms are the standard three.
3. **Open questions:** three or more pairs; two pairs on other regions, such as solid grid graphs;
   a conceptual description of the B, C and D configurations, which would shorten the proof
   and its certificates.

---

## 8. The algorithm (proof version)

Input: an instance R. Output: a solution, or "unsolvable".
1. If a side is ≤ 10: run the plug DP and return its answer.
2. If R fails the catalogue: return "unsolvable" (sound by §4.7 and §7).
3. If a reduction (S), (K) or (I) applies: build R′, solve it recursively, and lift the solution
   (strip splice, or band extension).
4. If (Q) applies: solve both one-path pieces by the IPS construction and return their union.
5. Otherwise R is a base box or in 𝔉, with sides ≤ 22. Find a valid move, solve the pieces
   recursively, and glue. §5 found a valid move for every such instance outside 11 × 11, 11 × 12 and
   12 × 12; in those three `lib/tests/boxes.sh` finds a same-colour split or a valid move for every
   passing instance. If no move is found, solve R with the exact plug DP.

**Cost.**
- Step 3 shrinks one side per step, so there are O(N0 + N1) of them, each costing a catalogue
  check (O(N0 + N1)) plus a lift (O(N0·N1), the paths are rebuilt). Step 4 happens once and costs
  O(N0·N1).
- Step 5 runs on a bounded-size instance, in constant time.
- Step 1 is linear in the long side, with a large constant (the number of width-10 plug states).

So the total is O((N0 + N1)·N0·N1), plus the plug DP on thin inputs.

The libraries in `lib/` (Python, JavaScript, C) implement this algorithm, together with an optimized
solver for thin instances.
