/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.BuildT
public import ZZN.Look.Size
public import ZZN.Look.Complete

@[expose] public section

/-!
# The certificate lookup, counted

`lookJT tab` is `lookJ tab` (`lookJT_ret`). On a table whose entries pass `szOK` and that is empty
outside sides 16 (`TabSz`), it takes at most `28 000 000` steps on any instance (`lookJT_time`):
choosing the symmetry, scanning at most 1569 slices, trying at most 163 templates and 418 stored
pairs, building one tree of at most 16 IPS leaves of at most `16 × 16` cells, pulling back.
-/

namespace ZZN.T

open GridHam ZZN.Cut ZZN.BoxK ZZN.Look

/-! ### Maps and the symmetry pull-back -/

def mapPT (f : Coord → Coord) (s : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let a ← lmapT (fun v => pure (f v)) s.1
  let b ← lmapT (fun v => pure (f v)) s.2
  pure (a, b)

theorem mapPT_ret (f : Coord → Coord) (s : List Coord × List Coord) :
    (mapPT f s).ret = (s.1.map f, s.2.map f) := by
  simp [mapPT, lmapT]

theorem mapPT_time (f : Coord → Coord) (s : List Coord × List Coord) :
    (mapPT f s).time = s.1.length + s.2.length := by
  simp [mapPT, lmapT]

def unLabT (σ : Sym) (s : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let s1 := if σ.sw then (s.2, s.1) else s
  let q ← if σ.r1 then lreverseT s1.2 else pure s1.2
  let p ← if σ.r0 then lreverseT s1.1 else pure s1.1
  pure (p, q)

theorem unLabT_ret (σ : Sym) (s : List Coord × List Coord) : (unLabT σ s).ret = unLab σ s := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> simp [unLabT, unLab, lreverseT]

theorem unLabT_time (σ : Sym) (s : List Coord × List Coord) :
    (unLabT σ s).time ≤ s.1.length + s.2.length + 2 := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> simp [unLabT, lreverseT] <;> omega

theorem unLab_len (σ : Sym) (s : List Coord × List Coord) :
    (unLab σ s).1.length + (unLab σ s).2.length = s.1.length + s.2.length := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> simp [unLab] <;> omega

def unGeoT (σ : Sym) (J : Inst) (s : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let I1 := if σ.tr then J.transpose else J
  let I2 := if σ.rx then I1.reflectX else I1
  let s4 ← if σ.ry then do
      let a ← mapPT Prod.swap s
      let b ← mapPT (reflX I2.h) a
      mapPT Prod.swap b
    else pure s
  let s5 ← if σ.rx then mapPT (reflX I1.w) s4 else pure s4
  if σ.tr then mapPT Prod.swap s5 else pure s5

theorem unGeoT_ret (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unGeoT σ J s).ret = unGeo σ J s := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases tr <;> cases rx <;> cases ry <;> simp [unGeoT, unGeo, mapPT_ret, unRy]

theorem unGeoT_time (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unGeoT σ J s).time ≤ 5 * (s.1.length + s.2.length) := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases tr <;> cases rx <;> cases ry <;>
    simp only [unGeoT, time_bind, time_pure, ret_pure, mapPT_ret, mapPT_time,
      List.length_map, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem unGeo_len (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unGeo σ J s).1.length + (unGeo σ J s).2.length = s.1.length + s.2.length := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases tr <;> cases rx <;> cases ry <;> simp [unGeo, unRy]

def unSymT (σ : Sym) (J : Inst) (s : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let t ← unLabT σ s
  unGeoT σ J t

theorem unSymT_ret (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unSymT σ J s).ret = unSym σ J s := by
  simp [unSymT, unSym, unLabT_ret, unGeoT_ret]

theorem unSymT_time (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unSymT σ J s).time ≤ 6 * (s.1.length + s.2.length) + 2 := by
  simp only [unSymT, time_bind]
  have := unLabT_time σ s
  have := unGeoT_time σ J (unLabT σ s).ret
  rw [unLabT_ret] at this ⊢
  rw [unLab_len] at this
  omega

theorem unSym_len (σ : Sym) (J : Inst) (s : List Coord × List Coord) :
    (unSym σ J s).1.length + (unSym σ J s).2.length = s.1.length + s.2.length := by
  unfold unSym
  rw [unGeo_len, unLab_len]

/-! ### Stored pairs of paths -/

def chainAdjT : List Coord → TimeM Bool
  | [] => do tick 1; pure true
  | [_] => do tick 1; pure true
  | a :: b :: r => do
    tick 1
    let c ← chainAdjT (b :: r)
    pure (adjacentB a b && c)

theorem chainAdjT_ret : ∀ l, (chainAdjT l).ret = chainAdjacent l
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by simp [chainAdjT, chainAdjacent, chainAdjT_ret (b :: r)]

theorem chainAdjT_time : ∀ l, (chainAdjT l).time ≤ l.length + 1
  | [] => by simp [chainAdjT]
  | [_] => by simp [chainAdjT]
  | a :: b :: r => by
    have := chainAdjT_time (b :: r)
    simp only [chainAdjT, time_bind, time_tick, time_pure, List.length_cons] at this ⊢
    omega

def maskOKT (w h : ℕ) : ℕ → List Coord → TimeM Bool
  | _, [] => do tick 1; pure true
  | m, v :: vs => do
    tick 1
    let r ← maskOKT w h (m ||| 2 ^ (v.1 * h + v.2)) vs
    pure (decide (v.1 < w) && decide (v.2 < h) && !m.testBit (v.1 * h + v.2) && r)

theorem maskOKT_ret (w h : ℕ) : ∀ m l, (maskOKT w h m l).ret = maskOK w h m l
  | _, [] => rfl
  | m, v :: vs => by simp [maskOKT, maskOK, maskOKT_ret w h _ vs]

theorem maskOKT_time (w h : ℕ) : ∀ m l, (maskOKT w h m l).time ≤ l.length + 1
  | _, [] => by simp [maskOKT]
  | m, v :: vs => by
    have := maskOKT_time w h (m ||| 2 ^ (v.1 * h + v.2)) vs
    simp only [maskOKT, time_bind, time_tick, time_pure, List.length_cons] at this ⊢
    omega

def solFT (I : Inst) (p q : List Coord) : TimeM Bool := do
  let lp ← lgetLastT p
  let lq ← lgetLastT q
  let cp ← chainAdjT p
  let cq ← chainAdjT q
  let pq ← lappendT p q
  let mk ← maskOKT I.w I.h 0 pq
  let np ← lengthT p
  let nq ← lengthT q
  pure ((p.head? == some I.s0) && (lp == some I.t0) && cp && (q.head? == some I.s1) &&
    (lq == some I.t1) && cq && mk && (np + nq == I.w * I.h))

theorem solFT_ret (I : Inst) (p q : List Coord) : (solFT I p q).ret = solF I p q := by
  simp [solFT, solF, lgetLastT, chainAdjT_ret, lappendT, maskOKT_ret, lengthT]

theorem solFT_time (I : Inst) (p q : List Coord) :
    (solFT I p q).time ≤ 5 * (p.length + q.length) + 8 := by
  simp only [solFT, time_bind, time_pure, lgetLastT, lappendT, lengthT]
  have := chainAdjT_time p
  have := chainAdjT_time q
  have := maskOKT_time I.w I.h 0 (p ++ q)
  simp only [List.length_append] at this
  omega

def decPathT (n code : ℕ) : TimeM (List Coord) := do
  let r ← rangeT n
  lmapT (fun k => pure (let b := code / 256 ^ k % 256; (b / 16, b % 16))) r

theorem decPathT_ret (n code : ℕ) : (decPathT n code).ret = decPath n code := by
  simp [decPathT, decPath, rangeT, lmapT]

theorem decPathT_time (n code : ℕ) : (decPathT n code).time ≤ 2 * n + 1 := by
  simp only [decPathT, time_bind, rangeT]
  have := lmapT_time_le (fun k : ℕ => (pure (let b := code / 256 ^ k % 256; (b / 16, b % 16)) :
    TimeM Coord)) (List.range n) 0 (fun _ _ => le_rfl)
  simp only [List.length_range] at this
  omega

theorem decPath_length (n code : ℕ) : (decPath n code).length = n := by simp [decPath]

def solTest (K : Inst) (e : ℕ × ℕ × ℕ × ℕ × ℕ) : TimeM Bool :=
  if e.1 == idx K.h (colsOf K) then do
    let p ← decPathT e.2.1 e.2.2.1
    let q ← decPathT e.2.2.2.1 e.2.2.2.2
    solFT K p q
  else pure false

theorem solTest_ret (K : Inst) (e : ℕ × ℕ × ℕ × ℕ × ℕ) : (solTest K e).ret =
    (e.1 == idx K.h (colsOf K) && solF K (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2)) := by
  unfold solTest
  split_ifs with h
  · simp [h, decPathT_ret, solFT_ret]
  · simp [h]

theorem solTest_time (K : Inst) (e : ℕ × ℕ × ℕ × ℕ × ℕ) (h1 : e.2.1 ≤ 256) (h2 : e.2.2.2.1 ≤ 256) :
    (solTest K e).time ≤ 3594 := by
  unfold solTest
  split_ifs
  · simp only [time_bind, decPathT_ret]
    have := decPathT_time e.2.1 e.2.2.1
    have := decPathT_time e.2.2.2.1 e.2.2.2.2
    have := solFT_time K (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2)
    rw [decPath_length, decPath_length] at this
    omega
  · simp

/-! ### One slice -/

def entryPT (K : Inst) (d : CData) : TimeM (Option (List Coord × List Coord)) := do
  let e ← lfindT (fun e => tcheckT e.1 (e.2.apply K)) d.2.2.1
  match e with
  | some e => do
    let s ← tsolT e.1 (e.2.apply K)
    let s' ← unSymT e.2 K s
    pure (some s')
  | none => do
    let e ← lfindT (solTest K) d.2.2.2.2
    match e with
    | some e => do
      let p ← decPathT e.2.1 e.2.2.1
      let q ← decPathT e.2.2.2.1 e.2.2.2.2
      pure (some (p, q))
    | none => pure none

theorem entryPT_ret (K : Inst) (d : CData) : (entryPT K d).ret = entryP K d := by
  unfold entryPT entryP
  simp only [ret_bind, lfindT, tcheckT_ret, solTest_ret]
  cases d.2.2.1.find? (fun e => tcheck e.1 (e.2.apply K)) with
  | some e => simp [tsolT_ret, unSymT_ret]
  | none =>
    simp only [ret_bind]
    cases d.2.2.2.2.find? (fun e => e.1 == idx K.h (colsOf K) &&
      solF K (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2)) <;> simp [decPathT_ret]

theorem mem_cells_le {ps : List ZZN.Cut.Seg} {x : ZZN.Cut.Seg} (hx : x ∈ ps) : x.p.length ≤ cellsL ps :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem solOf_len {I : Inst} {ps : List ZZN.Cut.Seg} :
    (solOf I ps).1.length ≤ cellsL ps ∧ (solOf I ps).2.length ≤ cellsL ps := by
  unfold solOf
  constructor
  · cases h : ps.find? (fun x => x.ends == (I.s0, I.t0)) with
    | none => simp
    | some x => exact mem_cells_le (List.mem_of_find?_eq_some h)
  · cases h : ps.find? (fun x => x.ends == (I.s1, I.t1)) with
    | none => simp
    | some x => exact mem_cells_le (List.mem_of_find?_eq_some h)

theorem tsol_len {T : CTree TPos} {I : Inst} (h : tcheck T I = true) (hw : I.w ≤ 16)
    (hh : I.h ≤ 16) (hN : tleaves T ≤ 16) :
    (tsol T I).1.length ≤ 4096 ∧ (tsol T I).2.length ≤ 4096 := by
  unfold tsol
  set T' := inst (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  obtain ⟨c, -⟩ := buildT_cells T' (rootPiece I) h hw hh
  rw [tleaves_inst] at c
  obtain ⟨l1, l2⟩ := solOf_len (I := I) (ps := buildT T' (rootPiece I))
  constructor <;> omega

theorem entryPT_time (K : Inst) (d : CData) (hw : K.w ≤ 16) (hh : K.h ≤ 16) (hd : szOK d = true) :
    (entryPT K d).time ≤ 27000000 := by
  simp only [szOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
  obtain ⟨⟨⟨hp, hs⟩, hpe⟩, hse⟩ := hd
  have wK : ∀ σ : Sym, (σ.apply K).w ≤ 16 ∧ (σ.apply K).h ≤ 16 := by
    intro σ
    obtain ⟨e1, e2⟩ := wh_apply' σ K
    split_ifs at e1 e2 <;> omega
  unfold entryPT
  simp only [time_bind]
  have f1 := lfindT_time_le (fun e : CTree TPos × Sym => tcheckT e.1 (e.2.apply K)) d.2.2.1 2666
    (fun e he => by
      have := tcheckT_time e.1 (e.2.apply K)
      have := (hpe e he).1
      omega)
  have f1' : (lfindT (fun e : CTree TPos × Sym => tcheckT e.1 (e.2.apply K)) d.2.2.1).time ≤
      163 * 2667 := le_trans f1 (Nat.mul_le_mul_right _ hp)
  cases he : (lfindT (fun e : CTree TPos × Sym => tcheckT e.1 (e.2.apply K)) d.2.2.1).ret with
  | some e =>
    have hm : e ∈ d.2.2.1 := List.mem_of_find?_eq_some (by simpa [lfindT] using he)
    have hc : tcheck e.1 (e.2.apply K) = true := by
      have := List.find?_some (by simpa [lfindT] using he)
      simpa [tcheckT_ret] using this
    obtain ⟨c1, c2⟩ := (hpe e hm)
    simp only [time_bind, time_pure]
    have t1 := tsolT_time e.1 (e.2.apply K) hc (wK e.2).1 (wK e.2).2 16 c2
    have t2 := unSymT_time e.2 K (tsolT e.1 (e.2.apply K)).ret
    rw [tsolT_ret] at t2 ⊢
    obtain ⟨l1, l2⟩ := tsol_len hc (wK e.2).1 (wK e.2).2 c2
    have : tcost e.1 * (520 * 16 + 11) ≤ 1333 * (520 * 16 + 11) := Nat.mul_le_mul_right _ c1
    omega
  | none =>
    simp only [time_bind]
    have f2 := lfindT_time_le (solTest K) d.2.2.2.2 3594
      (fun e he => solTest_time K e (hse e he).1 (hse e he).2)
    have f2' : (lfindT (solTest K) d.2.2.2.2).time ≤ 418 * 3595 :=
      le_trans f2 (Nat.mul_le_mul_right _ hs)
    cases he2 : (lfindT (solTest K) d.2.2.2.2).ret with
    | some e =>
      have hm : e ∈ d.2.2.2.2 := List.mem_of_find?_eq_some (by simpa [lfindT] using he2)
      simp only [time_bind, time_pure]
      have := decPathT_time e.2.1 e.2.2.1
      have := decPathT_time e.2.2.2.1 e.2.2.2.2
      have := (hse e hm).1
      have := (hse e hm).2
      omega
    | none => simp only [time_pure]; omega

theorem entryP_len {K : Inst} {d : CData} (hw : K.w ≤ 16) (hh : K.h ≤ 16) (hd : szOK d = true)
    {s : List Coord × List Coord} (h : entryP K d = some s) : s.1.length + s.2.length ≤ 8192 := by
  simp only [szOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
  obtain ⟨⟨⟨-, -⟩, hpe⟩, hse⟩ := hd
  unfold entryP at h
  split at h
  · rename_i e he
    have hm := List.mem_of_find?_eq_some he
    have hc : tcheck e.1 (e.2.apply K) = true := by simpa using List.find?_some he
    cases h
    rw [unSym_len]
    obtain ⟨e1, e2⟩ := wh_apply' e.2 K
    obtain ⟨l1, l2⟩ := tsol_len hc (by split_ifs at e1 <;> omega) (by split_ifs at e2 <;> omega)
      (hpe e hm).2
    omega
  · split at h
    · rename_i e he
      have hm := List.mem_of_find?_eq_some he
      cases h
      simp only [decPath_length]
      have := (hse e hm).1
      have := (hse e hm).2
      omega
    · cases h

/-! ### The table and the symmetry -/

/-- The table is small and empty outside sides 16. -/
def TabSz (tab : ℕ → ℕ → List CData) : Prop :=
  ∀ w h, (tab w h).all szOK = true ∧ (tab w h).length ≤ 1569 ∧ (tab w h ≠ [] → w ≤ 16 ∧ h ≤ 16)

def lookKT (tab : ℕ → ℕ → List CData) (K : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let o ← lfindT (fun d => pure (sameX d.1 (rowsOf K))) (tab K.w K.h)
  match o with
  | some d => entryPT K d
  | none => pure none

theorem lookKT_ret (tab : ℕ → ℕ → List CData) (K : Inst) : (lookKT tab K).ret = lookK tab K := by
  unfold lookKT lookK
  simp only [ret_bind, lfindT, ret_pure]
  cases (tab K.w K.h).find? (fun d => sameX d.1 (rowsOf K)) with
  | none => rfl
  | some d => exact entryPT_ret K d

theorem lookKT_time {tab : ℕ → ℕ → List CData} (ht : TabSz tab) (K : Inst) :
    (lookKT tab K).time ≤ 1569 + 27000000 := by
  obtain ⟨hs, hl, hn⟩ := ht K.w K.h
  unfold lookKT
  simp only [time_bind]
  have f := lfindT_time_le (fun d : CData => (pure (sameX d.1 (rowsOf K)) : TimeM Bool))
    (tab K.w K.h) 0 (fun _ _ => le_rfl)
  cases he : (lfindT (fun d : CData => (pure (sameX d.1 (rowsOf K)) : TimeM Bool)) (tab K.w K.h)).ret
    with
  | none => simp only [time_pure]; omega
  | some d =>
    have hm : d ∈ tab K.w K.h := List.mem_of_find?_eq_some (by simpa [lfindT] using he)
    obtain ⟨hw, hh⟩ := hn (List.ne_nil_of_mem hm)
    have := entryPT_time K d hw hh (List.all_eq_true.mp hs d hm)
    dsimp only
    omega

theorem lookK_len {tab : ℕ → ℕ → List CData} (ht : TabSz tab) {K : Inst}
    {s : List Coord × List Coord} (h : lookK tab K = some s) : s.1.length + s.2.length ≤ 8192 := by
  obtain ⟨hs, -, hn⟩ := ht K.w K.h
  unfold lookK at h
  split at h
  · rename_i d hd
    have hm := List.mem_of_find?_eq_some hd
    obtain ⟨hw, hh⟩ := hn (List.ne_nil_of_mem hm)
    exact entryP_len hw hh (List.all_eq_true.mp hs d hm) h
  · cases h

def argminST (f : Sym → ℕ) : List Sym → TimeM Sym
  | [] => pure Sym.id
  | a :: l => lfoldlT (fun b c => do tick 1; pure (if f c < f b then c else b)) a l

theorem argminST_ret (f : Sym → ℕ) (L : List Sym) : (argminST f L).ret = argminS f L := by
  cases L with
  | nil => rfl
  | cons a l => simp [argminST, argminS]

theorem lfoldlT_tick_time (g : Sym → Sym → Sym) : ∀ (l : List Sym) (b : Sym),
    (lfoldlT (fun b c => do tick 1; pure (g b c)) b l).time = 2 * l.length
  | [], _ => rfl
  | c :: l, b => by
    simp only [lfoldlT, time_bind, time_tick, time_pure, ret_bind, ret_pure, List.length_cons]
    rw [lfoldlT_tick_time g l]
    omega

theorem argminST_time (f : Sym → ℕ) (L : List Sym) : (argminST f L).time ≤ 2 * L.length := by
  cases L with
  | nil => simp [argminST]
  | cons a l =>
    simp only [argminST, List.length_cons]
    rw [lfoldlT_tick_time (fun b c => if f c < f b then c else b) l a]
    omega

theorem Gbox_length (w h : ℕ) : (Gbox w h).length ≤ 64 := by
  unfold Gbox; split_ifs <;> decide

def lookLeT (tab : ℕ → ℕ → List CData) (J : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let σ ← argminST (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)
  let r ← lookKT tab (σ.apply J)
  match r with
  | some s => do
    let s' ← unSymT σ J s
    pure (some s')
  | none => pure none

theorem lookLeT_ret (tab : ℕ → ℕ → List CData) (J : Inst) : (lookLeT tab J).ret = lookLe tab J := by
  unfold lookLeT lookLe
  simp only [ret_bind, argminST_ret, lookKT_ret]
  cases lookK tab ((argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)).apply J) with
  | none => rfl
  | some s => simp [unSymT_ret]

theorem lookLeT_time {tab : ℕ → ℕ → List CData} (ht : TabSz tab) (J : Inst) :
    (lookLeT tab J).time ≤ 128 + (1569 + 27000000) + (6 * 8192 + 2) := by
  unfold lookLeT
  simp only [time_bind, argminST_ret, lookKT_ret]
  have t1 := argminST_time (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)
  have := Gbox_length J.w J.h
  set σ := argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)
  have t2 := lookKT_time ht (σ.apply J)
  cases hk : lookK tab (σ.apply J) with
  | none => simp only [time_pure]; omega
  | some s =>
    have hl := lookK_len ht hk
    have := unSymT_time σ J s
    simp only [time_bind, time_pure]
    omega

def lookJT (tab : ℕ → ℕ → List CData) (J : Inst) : TimeM (Option (List Coord × List Coord)) :=
  if J.w ≤ J.h then lookLeT tab J
  else do
    let r ← lookLeT tab J.transpose
    match r with
    | some s => do
      let s' ← mapPT Prod.swap s
      pure (some s')
    | none => pure none

theorem lookJT_ret (tab : ℕ → ℕ → List CData) (J : Inst) : (lookJT tab J).ret = lookJ tab J := by
  unfold lookJT lookJ
  split_ifs
  · exact lookLeT_ret tab J
  · simp only [ret_bind, lookLeT_ret]
    cases lookLe tab J.transpose with
    | none => rfl
    | some s => simp [mapPT_ret]

theorem lookLe_len {tab : ℕ → ℕ → List CData} (ht : TabSz tab) {J : Inst}
    {s : List Coord × List Coord} (h : lookLe tab J = some s) : s.1.length + s.2.length ≤ 8192 := by
  unfold lookLe at h
  obtain ⟨t, ht', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [unSym_len]
  exact lookK_len ht ht'

theorem lookJT_time {tab : ℕ → ℕ → List CData} (ht : TabSz tab) (J : Inst) :
    (lookJT tab J).time ≤ 28000000 := by
  unfold lookJT
  split_ifs
  · have := lookLeT_time ht J; omega
  · simp only [time_bind, lookLeT_ret]
    have := lookLeT_time ht J.transpose
    cases hk : lookLe tab J.transpose with
    | none => simp only [time_pure]; omega
    | some s =>
      have := lookLe_len ht hk
      have := mapPT_time Prod.swap s
      simp only [time_bind, time_pure]
      omega

end ZZN.T
