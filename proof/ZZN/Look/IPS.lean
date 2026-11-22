/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import GridHam.Main

@[expose] public section

/-!
# A constructive IPS path

`ipsP n w h s t` follows the induction of `ips_sufficiency` (`GridHam/Main.lean`): transpose to
`h ≤ w`, reverse to `s.x ≤ t.x`, then a prime shape (`primeLookup`), a two-column strip on the left
or right, or a split after column 1. `ipsP_valid`: on an acceptable problem with `w + h ≤ n` it is a
Hamiltonian path. The strip step finds an edge of the smaller path along its last column with
`colEdge` (the computable form of `exists_col_edge`).
-/

namespace GridHam

/-! ### Path-level forms of the symmetry and split lemmas -/

theorem validPath_transpose {w h : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath w h s t p) : ValidPath h w (swapXY s) (swapXY t) (p.map swapXY) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen, Nat.mul_comm]
    · show (swapXY a :: l.map swapXY).head? = some (swapXY s)
      rw [has]
      rfl
    · exact getLast?_map_coord swapXY (a :: l) t hlast
    · apply nodup_map_coord swapXY _ (a :: l) hnd
      intro v u hvu
      unfold swapXY at hvu
      have h1 := congrArg Prod.fst hvu
      have h2 := congrArg Prod.snd hvu
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold swapXY
      dsimp only
      exact ⟨hu'.2, hu'.1⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords h w v).mp hv
      have hu := hcov (swapXY v) ((mem_allCoords w h _).mpr
        ⟨by unfold swapXY; dsimp only; exact hy, by unfold swapXY; dsimp only; exact hx⟩)
      exact List.mem_map.mpr ⟨swapXY v, hu, rfl⟩
    · exact chainAdjacent_map swapXY (fun v u hvu => adjacent_swapXY hvu) (a :: l) hch

theorem validPath_reflect {w h : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath w h s t p) :
    ValidPath w h (reflectX w s) (reflectX w t) (p.map (reflectX w)) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen]
    · show (reflectX w a :: l.map (reflectX w)).head? = some (reflectX w s)
      rw [has]
      rfl
    · exact getLast?_map_coord (reflectX w) (a :: l) t hlast
    · apply nodup_map_coord_on (reflectX w) (a :: l) _ hnd
      intro v hv u hu hvu
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold reflectX at hvu
      have h1 := congrArg Prod.fst hvu
      have h2 := congrArg Prod.snd hvu
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold reflectX
      dsimp only
      exact ⟨by omega, hu'.2⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords w h v).mp hv
      have hu := hcov (reflectX w v) ((mem_allCoords w h _).mpr
        ⟨by unfold reflectX; dsimp only; omega, by unfold reflectX; dsimp only; exact hy⟩)
      refine List.mem_map.mpr ⟨reflectX w v, hu, ?_⟩
      unfold reflectX
      ext
      · show w - 1 - (w - 1 - v.1) = v.1
        omega
      · rfl
    · apply chainAdjacent_map_on (reflectX w) (a :: l) _ hch
      intro v hv u hu hadj
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold Adjacent at hadj ⊢
      unfold reflectX
      dsimp only
      omega

/-- The split of `splitVertically_preserves_startLeft`, on explicit paths. -/
theorem validPath_split (width height cut cutRow : ℕ) (s t : Coord) (pL pR : List Coord)
    (hcutRange' : cut < t.1)
    (hleft : ValidPath (cut + 1) height s (cut, cutRow) pL)
    (hright : ValidPath (width - (cut + 1)) height (0, cutRow) (t.1 - (cut + 1), t.2) pR) :
    ValidPath width height s t (pL ++ pR.map (shiftX (cut + 1))) := by
  obtain ⟨lenL, headL, lastL, ndL, inL, covL, chL⟩ := hleft
  obtain ⟨lenR, headR, lastR, ndR, inR, covR, chR⟩ := hright
  cases pR with
  | nil => simp at headR
  | cons b restR =>
    have hb : b = (0, cutRow) := by simpa using headR
    have hbin := inR b (List.mem_cons.mpr (Or.inl rfl))
    unfold InBounds at hbin
    have hle : cut + 1 ≤ width := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_map, lenL, lenR, ← Nat.add_mul,
        Nat.add_sub_of_le hle]
    · cases pL with
      | nil => simp at headL
      | cons a restL => simpa using headL
    · rw [show (b :: restR).map (shiftX (cut + 1)) =
          shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) from rfl,
        getLast?_append_cons,
        show shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) =
          (b :: restR).map (shiftX (cut + 1)) from rfl,
        getLast?_map_coord (shiftX (cut + 1)) (b :: restR) _ lastR]
      congr 1
      unfold shiftX
      ext
      · show t.1 - (cut + 1) + (cut + 1) = t.1
        omega
      · rfl
    · apply nodup_append_of pL _ ndL
      · apply nodup_map_coord (shiftX (cut + 1)) _ (b :: restR) ndR
        intro v u hvu
        unfold shiftX at hvu
        have h1 := congrArg Prod.fst hvu
        have h2 := congrArg Prod.snd hvu
        dsimp only at h1 h2
        ext
        · omega
        · omega
      · intro v hv u hu
        obtain ⟨u', _, rfl⟩ := List.mem_map.mp hu
        have hv' := inL v hv
        unfold InBounds at hv'
        intro heq
        have h1 := congrArg Prod.fst heq
        unfold shiftX at h1
        dsimp only at h1
        omega
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · have hv' := inL v h
        unfold InBounds at hv' ⊢
        exact ⟨by omega, hv'.2⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
        have hu' := inR u hu
        unfold InBounds at hu' ⊢
        unfold shiftX
        dsimp only
        exact ⟨by omega, hu'.2⟩
    · intro v hv
      obtain ⟨hvx, hvy⟩ := (mem_allCoords width height v).mp hv
      by_cases hc : v.1 ≤ cut
      · exact List.mem_append.mpr (Or.inl
          (covL v ((mem_allCoords (cut + 1) height v).mpr ⟨by omega, hvy⟩)))
      · have hu := covR (v.1 - (cut + 1), v.2)
          ((mem_allCoords (width - (cut + 1)) height _).mpr ⟨by dsimp only; omega, hvy⟩)
        refine List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hu, ?_⟩))
        unfold shiftX
        ext
        · show v.1 - (cut + 1) + (cut + 1) = v.1
          omega
        · rfl
    · have hadj : Adjacent (cut, cutRow) (shiftX (cut + 1) b) := by
        rw [hb]
        unfold Adjacent shiftX
        simp
      have hchR' : chainAdjacent ((b :: restR).map (shiftX (cut + 1))) = true :=
        chainAdjacent_map_shiftX (cut + 1) (b :: restR) chR
      exact chainAdjacent_append pL (shiftX (cut + 1) b) (restR.map (shiftX (cut + 1)))
        (cut, cutRow) lastL chL hadj hchR'

/-! ### The strip step -/

/-- The first consecutive pair of `l` with both cells in column `X`. -/
def colEdge (X : ℕ) : List Coord → Option (List Coord × Coord × Coord × List Coord)
  | a :: b :: r =>
    if a.1 = X ∧ b.1 = X then some ([], a, b, r)
    else (colEdge X (b :: r)).map fun q => (a :: q.1, q.2.1, q.2.2.1, q.2.2.2)
  | _ => none

theorem colEdge_some (X : ℕ) : ∀ (l : List Coord) {l1 : List Coord} {a b : Coord} {l2 : List Coord},
    colEdge X l = some (l1, a, b, l2) → l = l1 ++ a :: b :: l2 ∧ a.1 = X ∧ b.1 = X
  | [], _, _, _, _, h => by simp [colEdge] at h
  | [_], _, _, _, _, h => by simp [colEdge] at h
  | c :: d :: r, l1, a, b, l2, h => by
    unfold colEdge at h
    split_ifs at h with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hc⟩
    · obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨q1, qa, qb, q2⟩ := q
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      obtain ⟨e1, e2, e3⟩ := colEdge_some X (d :: r) hq
      exact ⟨by rw [e1]; rfl, e2, e3⟩

theorem colEdge_isSome (X : ℕ) : ∀ (l l1 : List Coord) (a b : Coord) (l2 : List Coord),
    l = l1 ++ a :: b :: l2 → a.1 = X → b.1 = X → (colEdge X l).isSome
  | l, [], a, b, l2, e, ha, hb => by subst e; simp [colEdge, ha, hb]
  | l, c :: l1, a, b, l2, e, ha, hb => by
    subst e
    have ih := colEdge_isSome X (l1 ++ a :: b :: l2) l1 a b l2 rfl ha hb
    cases l1 with
    | nil =>
      simp only [List.nil_append, List.cons_append] at ih ⊢
      unfold colEdge
      split_ifs
      · rfl
      · simpa using ih
    | cons d l1' =>
      simp only [List.cons_append] at ih ⊢
      unfold colEdge
      split_ifs
      · rfl
      · simpa using ih

/-- Strip two columns on the right: insert `rightDetour` at an edge along the last column. -/
def stripRightP (width height : ℕ) (p : List Coord) : List Coord :=
  match colEdge (width - 3) p with
  | some (l1, a, b, l2) =>
    if b.2 = a.2 + 1 then l1 ++ a :: (rightDetour (width - 2) height a.2 ++ b :: l2)
    else (l2.reverse ++ b :: (rightDetour (width - 2) height b.2 ++ a :: l1.reverse)).reverse
  | none => p

theorem stripRightP_valid (width height : ℕ) (s t : Coord) (p : List Coord)
    (hs : s.1 + 2 < width) (_ht : t.1 + 2 < width)
    (hfree : ∃ y, y < height ∧ (width - 3, y) ≠ s ∧ (width - 3, y) ≠ t)
    (hv : ValidPath (width - 2) height s t p) :
    ValidPath width height s t (stripRightP width height p) := by
  obtain ⟨y0, hy0, hys, hyt⟩ := hfree
  have hv0 := hv
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv0
  have hw1 : 1 ≤ width - 2 := by omega
  have hvmem : (width - 3, y0) ∈ p :=
    hcov _ ((mem_allCoords _ _ _).mpr ⟨by dsimp only; omega, hy0⟩)
  have hhd : p.head? ≠ some (width - 3, y0) := by
    intro h
    rw [hhead] at h
    exact hys (Option.some.inj h).symm
  have hlst : p.getLast? ≠ some (width - 3, y0) := by
    intro h
    rw [hlast] at h
    exact hyt (Option.some.inj h).symm
  have hbound : ∀ u ∈ p, u.1 ≤ width - 3 := by
    intro u hu
    have hu' := hin u hu
    unfold InBounds at hu'
    omega
  obtain ⟨m1, ma, mb, m2, hpm, hma, hmb⟩ :=
    exists_col_edge (width - 3) p hch hnd hbound _ hvmem rfl hhd hlst
  obtain ⟨⟨l1, a, b, l2⟩, hq⟩ := Option.isSome_iff_exists.mp
    (colEdge_isSome (width - 3) p m1 ma mb m2 hpm hma hmb)
  obtain ⟨hp, ha, hb⟩ := colEdge_some (width - 3) p hq
  unfold stripRightP
  rw [hq]
  dsimp only
  have hc2 : chainAdjacent (a :: b :: l2) = true :=
    chainAdjacent_suffix l1 _ (by rw [← hp]; exact hch)
  have hc' : (adjacentB a b && chainAdjacent (b :: l2)) = true := by
    simpa [chainAdjacent] using hc2
  simp at hc'
  obtain ⟨hab, _⟩ := hc'
  have hadj : Adjacent a b := by
    unfold adjacentB at hab
    by_contra hcon
    simp [hcon] at hab
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, byy⟩ := b
  dsimp only at ha hb ⊢
  unfold Adjacent at hadj
  dsimp only at hadj
  have hax : ax = width - 2 - 1 := by omega
  have hbx : bx = width - 2 - 1 := by omega
  subst hax hbx
  have e : width - 2 + 2 = width := by omega
  by_cases hup : byy = ay + 1
  · simp only [hup, ↓reduceIte]
    subst hup
    have hv2 : ValidPath (width - 2) height s t
        (l1 ++ (width - 2 - 1, ay) :: (width - 2 - 1, ay + 1) :: l2) := by
      rw [← hp]
      exact hv
    have hN := extend_right_up (width - 2) height s t l1 l2 ay hw1 hv2
    rw [e] at hN
    exact hN
  · simp only [hup, ↓reduceIte]
    have hdown : ay = byy + 1 := by omega
    subst hdown
    have hrev : p.reverse =
        l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse := by
      rw [hp]
      simp
    have hv2 : ValidPath (width - 2) height t s
        (l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse) := by
      rw [← hrev]
      exact validPath_reverse hv
    have hN := extend_right_up (width - 2) height t s l2.reverse l1.reverse byy hw1 hv2
    rw [e] at hN
    exact validPath_reverse hN

/-- Strip two columns on the left: reflect, strip on the right, reflect back. -/
def stripLeftP (width height : ℕ) (p : List Coord) : List Coord :=
  (stripRightP width height (p.map (reflectX (width - 2)))).map (reflectX width)

theorem stripLeftP_valid (width height : ℕ) (s t : Coord) (p : List Coord)
    (hs : 2 ≤ s.1) (ht : 2 ≤ t.1)
    (hfree : ∃ y, y < height ∧ (2, y) ≠ s ∧ (2, y) ≠ t)
    (hv : ValidPath (width - 2) height (s.1 - 2, s.2) (t.1 - 2, t.2) p) :
    ValidPath width height s t (stripLeftP width height p) := by
  obtain ⟨y, hy, hys, hyt⟩ := hfree
  have hb := hasHamPath_bounds ⟨p, hv⟩
  unfold InBounds at hb
  dsimp only at hb
  obtain ⟨⟨hsx, -⟩, ⟨htx, -⟩⟩ := hb
  have hR := validPath_reflect hv
  have es : reflectX (width - 2) (s.1 - 2, s.2) = reflectX width s := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  have et : reflectX (width - 2) (t.1 - 2, t.2) = reflectX width t := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [es, et] at hR
  have neq : ∀ u : Coord, 2 ≤ u.1 → u.1 < width → (2, y) ≠ u →
      (width - 3, y) ≠ reflectX width u := by
    intro u h2 hw hne heq
    apply hne
    unfold reflectX at heq
    have h1 := congrArg Prod.fst heq
    have h2' := congrArg Prod.snd heq
    dsimp only at h1 h2'
    ext
    · show 2 = u.1
      omega
    · exact h2'
  have hS := stripRightP_valid width height (reflectX width s) (reflectX width t) _
    (by unfold reflectX; dsimp only; omega) (by unfold reflectX; dsimp only; omega)
    ⟨y, hy, neq s hs (by omega) hys, neq t ht (by omega) hyt⟩ hR
  have hB := validPath_reflect hS
  have rr : ∀ u : Coord, u.1 < width → reflectX width (reflectX width u) = u := by
    intro u hu
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [rr s (by omega), rr t (by omega)] at hB
  exact hB

/-! ### The recursion -/

/-- One step for `h ≤ w`, `s.x ≤ t.x`, with `f` for the smaller problems. -/
def normP (f : ℕ → ℕ → Coord → Coord → List Coord) (w h : ℕ) (s t : Coord) : List Coord :=
  if NotPrime w h then
    if 2 ≤ s.1 then stripLeftP w h (f (w - 2) h (s.1 - 2, s.2) (t.1 - 2, t.2))
    else if t.1 + 2 < w then stripRightP w h (f (w - 2) h s t)
    else
      f 2 h s (1, rChoice s.1 s.2 h) ++
        (f (w - 2) h (0, rChoice s.1 s.2 h) (t.1 - 2, t.2)).map (shiftX 2)
  else primeLookup w h s t

def stepP (f : ℕ → ℕ → Coord → Coord → List Coord) (w h : ℕ) (s t : Coord) : List Coord :=
  if h ≤ w then (if s.1 ≤ t.1 then normP f w h s t else (normP f w h t s).reverse)
  else
    (if s.2 ≤ t.2 then normP f h w (swapXY s) (swapXY t)
     else (normP f h w (swapXY t) (swapXY s)).reverse).map swapXY

/-- The IPS path, with fuel `n ≥ w + h`. -/
def ipsP : ℕ → ℕ → ℕ → Coord → Coord → List Coord
  | 0, _, _, _, _ => []
  | n + 1, w, h, s, t => stepP (ipsP n) w h s t

theorem normP_valid (n : ℕ)
    (IH : ∀ w h s t, w + h ≤ n → InBounds w h s → InBounds w h t → s ≠ t →
      IsAcceptable w h s t → ValidPath w h s t (ipsP n w h s t))
    (w h : ℕ) (s t : Coord) (hsz : w + h ≤ n + 1) (hwh : h ≤ w) (hle : s.1 ≤ t.1)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : ValidPath w h s t (normP (ipsP n) w h s t) := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < w ∧ sy < h := hs
  have ht' : tx < w ∧ ty < h := ht
  have hle' : sx ≤ tx := hle
  have hst' : ¬ (sx = tx ∧ sy = ty) := by
    rintro ⟨e1, e2⟩
    apply hst
    rw [e1, e2]
  have hA : AccA w h sx sy tx ty := (acc_iff w h (sx, sy) (tx, ty)).mp hacc
  unfold normP
  dsimp only
  by_cases hnp : NotPrime w h
  · simp only [hnp, ↓reduceIte]
    have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
    by_cases hA2 : 2 ≤ sx
    · simp only [hA2, ↓reduceIte]
      obtain ⟨hsub, hfree⟩ := branchA w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA hA2
      apply stripLeftP_valid w h (sx, sy) (tx, ty) _ hA2 (by show 2 ≤ tx; omega)
        (freeCol_exists 2 h sx sy tx ty hfree)
      apply IH (w - 2) h (sx - 2, sy) (tx - 2, ty) (by omega)
        (show sx - 2 < w - 2 ∧ sy < h by omega) (show tx - 2 < w - 2 ∧ ty < h by omega)
      · intro e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact hst' ⟨by omega, e2⟩
      · exact (acc_iff (w - 2) h (sx - 2, sy) (tx - 2, ty)).mpr hsub
    · simp only [hA2, ↓reduceIte]
      by_cases hC : tx + 2 < w
      · simp only [hC, ↓reduceIte]
        obtain ⟨hsub, hfree⟩ :=
          branchC w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) hC
        apply stripRightP_valid w h (sx, sy) (tx, ty) _ (by show sx + 2 < w; omega) hC
          (freeCol_exists (w - 3) h sx sy tx ty hfree)
        apply IH (w - 2) h (sx, sy) (tx, ty) (by omega)
          (show sx < w - 2 ∧ sy < h by omega) (show tx < w - 2 ∧ ty < h by omega) hst
        exact (acc_iff (w - 2) h (sx, sy) (tx, ty)).mpr hsub
      · simp only [hC, ↓reduceIte]
        have hB := branchB w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) (by omega)
        unfold BConcl at hB
        obtain ⟨hr, hs1, hq, haccL, haccR⟩ := hB
        have hleft := IH 2 h (sx, sy) (1, rChoice sx sy h) (by omega)
          (show sx < 2 ∧ sy < h by omega) (show 1 < 2 ∧ rChoice sx sy h < h by omega)
          (by
            intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hs1 ⟨e1, e2⟩)
          ((acc_iff 2 h (sx, sy) (1, rChoice sx sy h)).mpr haccL)
        have hright := IH (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) (by omega)
          (show 0 < w - 2 ∧ rChoice sx sy h < h by omega)
          (show tx - 2 < w - 2 ∧ ty < h by omega)
          (by
            intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hq ⟨e1, e2⟩)
          ((acc_iff (w - 2) h (0, rChoice sx sy h) (tx - 2, ty)).mpr haccR)
        exact validPath_split w h 1 (rChoice sx sy h) (sx, sy) (tx, ty) _ _
          (by show 1 < tx; omega) hleft hright
  · simp only [hnp, ↓reduceIte]
    exact prime_check (w, h) (mem_primeShapes_of w h (by omega) (by omega) hnp) (sx, sy)
      ((mem_allCoords w h _).mpr hs) (tx, ty) ((mem_allCoords w h _).mpr ht) hst hacc

/-- **The constructive IPS path is valid.** -/
theorem ipsP_valid : ∀ n w h (s t : Coord), w + h ≤ n → InBounds w h s → InBounds w h t →
    s ≠ t → IsAcceptable w h s t → ValidPath w h s t (ipsP n w h s t)
  | 0, w, h, s, _, hsz, hs, _, _, _ => by
    have hs0 : s.1 < w ∧ s.2 < h := hs
    omega
  | n + 1, w, h, s, t, hsz, hs, ht, hst, hacc => by
    have IH := ipsP_valid n
    unfold ipsP stepP
    have hs0 : s.1 < w ∧ s.2 < h := hs
    have ht0 : t.1 < w ∧ t.2 < h := ht
    by_cases hwh : h ≤ w
    · simp only [hwh, ↓reduceIte]
      by_cases hle : s.1 ≤ t.1
      · simp only [hle, ↓reduceIte]
        exact normP_valid n IH w h s t hsz hwh hle hs ht hst hacc
      · simp only [hle, ↓reduceIte]
        have hacc' : IsAcceptable w h t s := (acc_iff w h t s).mpr
          ((accA_swap w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
        exact validPath_reverse
          (normP_valid n IH w h t s hsz hwh (by omega) ht hs (Ne.symm hst) hacc')
    · simp only [hwh, ↓reduceIte]
      have hsT : InBounds h w (swapXY s) := show s.2 < h ∧ s.1 < w from ⟨hs0.2, hs0.1⟩
      have htT : InBounds h w (swapXY t) := show t.2 < h ∧ t.1 < w from ⟨ht0.2, ht0.1⟩
      have hstT : swapXY s ≠ swapXY t := fun e => hst (by
        have := congrArg swapXY e
        simpa [swapXY] using this)
      have haccT : IsAcceptable h w (swapXY s) (swapXY t) :=
        (acc_iff h w (swapXY s) (swapXY t)).mpr
          ((accA_transpose w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
      have ss : ∀ u : Coord, swapXY (swapXY u) = u := fun u => rfl
      by_cases hle : s.2 ≤ t.2
      · simp only [hle, ↓reduceIte]
        have := validPath_transpose
          (normP_valid n IH h w (swapXY s) (swapXY t) (by omega) (by omega) hle hsT htT hstT haccT)
        rwa [ss, ss] at this
      · simp only [hle, ↓reduceIte]
        have haccT' : IsAcceptable h w (swapXY t) (swapXY s) := (acc_iff h w _ _).mpr
          ((accA_swap h w s.2 s.1 t.2 t.1 hsT htT).mp ((acc_iff h w _ _).mp haccT))
        have := validPath_transpose (validPath_reverse
          (normP_valid n IH h w (swapXY t) (swapXY s) (by omega) (by omega) (by
            show t.2 ≤ s.2; omega) htT hsT (Ne.symm hstT) haccT'))
        rwa [ss, ss] at this

end GridHam
