# The proof: a map of the Lean theorems

Every result the paper and the other documents state is listed here with its Lean name, its place under `proof/`
(branch `lib`, `proof/` unchanged since `31c6bb0`), and what lies outside the Lean check.
Statements are paraphrased from the Lean source; the Lean text is authoritative.
All theorems below depend only on `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean Axioms.lean`, run 2026-11-17 on this tree; `lake build --no-build` reports every
target up to date).

## 1. Definitions (trusted: a reader must check these say what is meant)

All in `ZZN/Statement.lean` unless noted.

| Name | Line | Meaning |
|---|---|---|
| `Coord`, `InBounds`, `Adjacent` | 25–35 | cells `(x, y)`, `x < w`, `y < h`; grid adjacency |
| `IsPath w h s t p` | 52 | `p` is a list of distinct in-bounds cells from `s` to `t`, consecutive cells adjacent |
| `Inst` | 59 | `w`, `h`, endpoints `s0 t0` (colour 0), `s1 t1` (colour 1) |
| `Inst.WellFormed` | 67 | the four endpoints are distinct cells of the grid |
| `IsSolution I p q` | 74 | `p` a path `s0 → t0`, `q` a path `s1 → t1`, disjoint, together covering every cell |
| `Solvable I` | 80 | `∃ p q, IsSolution I p q` |
| `fires3` | 377 | the catalogue: P (`parityOk`), T1, T2, L1, L6, frame entries L2–L5, E1 (`edgeClosure`), B (`boundaryOnly`), C/D (`corner4`, only when both sides ≥ 10), R (`effAlt3`) |
| `Passes I` | 385 | `fires3 I.w I.h I.s0 I.t0 I.s1 I.t1 = false` |
| `stretch`, `bandExtE` | 103, 432 | band extension as a function: insert lines `r+1, r+2` |
| `Inst.deleteAt I d` | 459 | delete lines `x = d, d+1` |
| `redB` (decides `RedX`) | 500 | see §3 |
| `liftE` | 510 | band extension after line `d` or `d − 1` |
| `stage`, `thinBF` | 624, 663 | plug DP, rows along the longer side |
| `thinSolveW` | 748 | plug DP carrying witness paths |
| `solveZZN` | 757 | the first construction (two-line reductions `RedX` only, plug DP leaf, every lift checked) |
| `solvableB` | 763 | both sides ≥ 11: `!fires3`; otherwise `thinBF` |

Defined outside `Statement.lean` (mentioned by the construction theorems):

| Name | Place | Meaning |
|---|---|---|
| `RedX I d` | `ZZN/Skeleton.lean:50` | `13 ≤ w` and one of: strip (`d = 0`, lines 0–3 free; or `d + 2 = w`, last 4 lines free); compression (`d, d+1` inside a window of 10 free lines with endpoints on both sides); interior compression (`8 ≤ d`, `d + 10 ≤ w`, `d, d+1` and a neighbour free, endpoints on both sides) |
| `RedB I d` | `ZZN/PassB.lean:29` | band compression: `13 ≤ w`, `5 ≤ d`, `d + 7 ≤ w`, `CompCore I d` |
| `CompCore I d` | `ZZN/PassX.lean:689` | `d, d+1` free, a free neighbour, endpoints on both sides, and every endpoint below `d` has `x + 8 ≤ w`, every endpoint above `d+1` has `x ≥ 7` (`FarK 5`) |
| `InDom I` | `ZZN/Skeleton.lean:37` | `11 ≤ w`, `11 ≤ h`, well formed |
| `Blk`, `Blk.del`, `Blk.lift` | `ZZN/Constr/Round.lean:254–269` | block of `2k` free lines at the left edge, right edge, or after line `r` |
| `leftK`, `rightK`, `innerK`, `blkX` | `Round.lean:275–297` | block sizes: left `min((xmin − 2)/2, (w − 11)/2)`, right `min((w − 3 − xmax)/2, (w − 11)/2)`, inner `min((b − a − 9)/2, (w − 11)/2)`; `blkX` tries left, right, then the first inner gap |
| `solveR`, `solveZ3` | `Round.lean:420, 440` | delete blocks on x, then on the transpose, else `solveZ2` |
| `findRed2`, `solveRec2`, `solveZ2` | `ZZN/Constr/Solve2.lean:186, 214, 234` | first `d` with `RedX` or `RedB`, on x then on the transpose; lift with `liftE`; leaf `checkE (thin I)` |
| `thinSolveW2` | `ZZN/Constr/ThinWit2.lean:38` | plug DP with witnesses, duplicates removed by merge sort |
| `leafL thin tab` | `ZZN/Look/Complete.lean:141` | a side ≤ 10: `thin`; otherwise the lookup `lookJ tab` |
| `lookJ`, `lookLe`, `lookK`, `entryP` | `ZZN/Look/Leaf.lean:46–141` | canonical symmetry (`argminS` of `key2` over `Gbox`), table row by endpoint rows, then a template (`tcheck`/`tsol`) or a stored path pair (`solF`), pulled back (`unSym`) |
| `tabAll` | `ZZN/Look/Table.lean:64` | the table, generated into `ZZN/LookGen/` by `notes/gen_lookgen.py` from the Theorem A certificates |

## 2. Main results

| Claim | Lean | Place |
|---|---|---|
| Characterization: both sides ≥ 11, well formed: `Passes I ↔ Solvable I` | `passes_iff_solvable_K` (= `passes_iff_solvable`) | `FinalN.lean:43`, `ZZN/Main.lean:23` |
| Decision for every rectangle: `solvableB J = true ↔ Solvable J` (well formed) | `solvableB_iff` | `ZZN/Thin/Decide.lean:26` |
| Plug DP decides every rectangle: `thinBF J = true ↔ Solvable J` | `thinBF_iff` | `ZZN/Thin/Fast.lean:163` |
| **The construction the libraries run**: `solveZ3 (leafL thinSolveW2 tabAll)`: every answer is a solution; well formed and solvable ⇒ an answer | `solveZ3L_main` | `ZZN/Look/Main.lean:24` |
| Same, counted: time ≤ `37(80(M+1)² + 400) + ((10M+1)·KwR 10 + 3(10M+1)² + 10) + (74·700·38² + ((371·KwR 10 + 28 000 000) + 3·593² + 10))`, `M = max w h` | `solveZ3LT_main` | `ZZN/Look/RoundTimeL.lean:97` |
| Registered construction (plug DP at every leaf): `solveZ3T thinSolveWRT`, sound, complete, time ≤ `37(80(M+1)² + 400) + ((10M+1)·KwR 10 + 3(10M+1)² + 10) + (74·700·38² + (593·KwR 16 + 3·593² + 10))` | `solveZ3RT_main` | `ZZN/Timed/RoundTimeR.lean:61` |
| Registered decision: `(solvableBRT J).ret = true ↔ Solvable J` and time ≤ `CdecR·(wh + w + h + 1)`, `CdecR = KwR 10 + 300000` | `solvableBRT_main` | `ZZN/Timed/DecideR.lean:79` (`CdecR` line 35) |
| Counted catalogue: both sides ≥ 11: `(fires3T …).ret = false ↔ Solvable J` | `fires3T_iff_solvable` | `ZZN/Timed/Main.lean:95` |
| Older construction: `solveZZN` sound and complete | `solveZZN_sound`, `solveZZN_complete` | `ZZN/Constr/Main.lean:33, 36` |

Numbers for `KwR 10` (≈ 9.45·10⁸) and `KwR 16` (≈ 2.55·10¹²) are from the development notes, not
evaluated for this map; `KwR b = KsR b + 2·Nw b + 30` (`ZZN/Timed/ThinRopeCost.lean:41`).

## 3. Proof structure: Theorem A (passes ⇒ solvable)

| Step | Lean | Place |
|---|---|---|
| Band extension: line `r < w` free, `I` solvable ⇒ `I.insertAt r` solvable (no length condition) | `band_extension` | `ZZN/BandExtension.lean:319` |
| `RedX` lifts solvability back | `lift_redX` | `ZZN/Skeleton.lean:207` |
| `RedB` lifts solvability back | `lift_redB` | `ZZN/PassB.lean:50` |
| `RedX` preserves passing (on `InDom`) | `passX_all` | `ZZN/PassB.lean:181` |
| `RedB` preserves passing | `passB` | `ZZN/PassB.lean:118` |
| Induction on area: passing irreducible instances with sides ≤ 22 are solvable ⇒ every passing `InDom` instance is | `theoremA_B` | `ZZN/PassB.lean:195` |
| Sides ≥ 23 always have a `RedX` | `redX_of_wide` | `ZZN/Skeleton.lean:154` |
| Sides 17–22: every endpoint tuple has a reduction (kernel evaluation of `noneOK`) | `none_all` | `ZZN/BoxK/None.lean:27` |
| Boxes 11–16: slice certificates for all 21 boxes `w ≤ h` | `boxes_allK` | `FinalN.lean:35` |
| Certificates ⇒ the finite fact | `finite_of_boxes`, `theoremA_boxes` | `ZZN/BoxK/Box.lean:317, 333` |

A slice certificate (`ZZN/BoxK/Slice.lean`, `SliceC.lean`) fixes the four endpoint rows (one
representative per symmetry class, `rowsOK`) and covers every column tuple ("lane") by a
template (a cut tree with symbolic positions, leaves single cells or one-pair rectangles accepted
by the IPS test), an explicit path pair, a lane of a smaller slice lifted through row insertions,
or a lane where the catalogue fires.

IPS: `ips_characterization` (`GridHam/Main.lean:20`): a `w × h` grid has a Hamiltonian path
`s → t` iff `IsAcceptable` (colour compatibility and not one of the forbidden cases),
Itai–Papadimitriou–Szwarcfiter 1982. Constructive form `ipsP`, `ipsP_valid`
(`ZZN/Look/IPS.lean:474`).

## 4. Proof structure: Theorem B (solvable ⇒ passes)

| Entry | Lean | Place |
|---|---|---|
| P (colour sum) | `parity_of_solvable` | `ZZN/Parity.lean:112` |
| T1 (four endpoints on the perimeter, colours alternate) | `t1_core` (planarity core) | `ZZN/SoundT1.lean:411` |
| R (alternation after the corner rewrites) | `theoremB_R` | `ZZN/SoundRMain.lean:494` |
| B, C, D (window certificates, kernel-checked) | `certFactsK`, `theoremB_K` | `WinKU/Facts.lean:167, 170` |
| Window-8 C entries follow from R | `c8_sound` | `ZZN/C8R.lean:134` |
| Assembly | `theoremB` | `ZZN/TheoremB.lean:63` |

## 5. The construction (`solveZ3`)

| Claim | Lean | Place |
|---|---|---|
| A block deletion is a chain of `RedX` steps; the lift returns a solution; width drops by ≥ 2; height unchanged | `BlkOK`, `blkX_ok` | `ZZN/Constr/Round.lean:299, 344` |
| A chain preserves `InDom` and passing | `chain_pass` | `Round.lean:32` |
| Right-edge lift (one splice of a snake block) | `edgeLift_sol` | `ZZN/Constr/EdgeBlock.lean:413` |
| Left-edge lift (by reflection) | `edgeLiftL_sol` | `EdgeBlock.lean:577` |
| Inner lift (wide band, one pass) | `wideExt_sol`, `innerLift_sol` | `ZZN/Constr/WideBand.lean:856`, `Round.lean:246` |
| No block on an axis ⇒ that side ≤ 37 | `w_le_of_none` | `ZZN/Constr/RoundCount.lean:90` |
| Block levels: potential `phi ≤ 36`, strictly drops per block | `phi_le`, `phi_del` | `RoundCount.lean:143, 350` |
| No `RedX`/`RedB` on an axis of length ≥ 11 ⇒ length ≤ 16 | `leaf16` | `ZZN/Constr/Solve2.lean:272` |
| `solveRec2` answers are solutions | `solveRec2_sound` | `Solve2.lean:239` |
| `solveZ3` answers are solutions (any `thin`) | `solveZ3_sound` | `Round.lean:528` |
| Completeness given the leaf property | `solveZ3_completeL` | `ZZN/Look/Complete.lean:133` |
| The leaf is correct (plug DP side ≤ 10; lookup on irreducible 11–16) | `leafL_ok` | `Complete.lean:145` |
| Lookup sound / complete | `lookJ_sound`, `lookJ_complete` | `ZZN/Look/Leaf.lean:157, 306` |
| Table certified | `tabAll_ok` | `ZZN/Look/Table.lean:67` |
| Plug DP with witnesses sound / complete | `thinSolveW2_sound`, `thinSolveW2_complete` | `ZZN/Constr/ThinWit2.lean:128, 141` |

## 6. Step counts

Model: `ZZN/Timed/TimeM.lean` (cost table in its header; trusted). Each list operation costs one
step per element touched; arithmetic on numbers, Booleans, cells, endpoint records, frames and
options is constant time. Bit-mask arithmetic on up to 256-bit numbers in the lookup is also
charged as constant time.

| Claim | Lean | Place |
|---|---|---|
| Reached plug DP states are non-crossing | `fold_NC` | `ZZN/Timed/ThinNC.lean:441` |
| A stage holds at most `wcnt (b+1) 0 0 0` states | `card_fold` | `ZZN/Timed/ThinWordCount.lean:248` |
| Tree-segment plug DP: time ≤ `(wh + 1)·KwR (min w h)`, result = `thinSolveW2` | `thinSolveWRT_time`, `thinSolveWRT_ret` | `ZZN/Timed/ThinRopeCost.lean:393`, `ThinRope.lean:295` |

## 7. Outside Lean

- The libraries in `lib/` (Python, JavaScript, C): transcriptions, checked against Lean by
  evaluation on random instances (`lib/tests/lean/*.lean`), not proved.
- The certificate search (`certgen/`) and `notes/gen_lookgen.py`: untrusted; a wrong certificate
  or table fails the build.
- The step-count model (§6) and the claim that it reflects running time.
- Palomar has not registered the current results; the registered entry is
  PALOMAR-2026-11-04-000002 v1 (older statements).
