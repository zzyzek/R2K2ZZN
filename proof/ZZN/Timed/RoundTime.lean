/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.RoundT

@[expose] public section

/-!
# The counted block construction: step counts

Each block level costs `O((M + 1)²)` steps (`wideBandT_time`, `edgeLiftT_time`, `edgeLiftLT_time`):
the paths are walked a constant number of times, each crossing or flip step reads its rows from
the table once (at most `2h` such steps), and the table holds at most `h` attached rows in all
(`sum_att_le`). There are at most 36 block levels (`phi_le`, `phi_del`), and the instance left at
the end has both sides at most 37 (`w_le_of_none`) or a side at most 10 from the start.
-/

namespace ZZN.T

open ZZN GridHam

theorem lmapT_pure_time {α β : Type} (f : α → β) (l : List α) :
    (lmapT (fun x => (pure (f x) : TimeM β)) l).time = l.length := by
  simp only [lmapT, time_pure, Nat.zero_add]
  induction l with
  | nil => rfl
  | cons x l ih => simp; omega

theorem colRun_length (x : ℕ) (A : List ℕ) : (colRun x A).length = A.length := by
  simp [colRun]

theorem colSnake_length (x : ℕ) (A : List ℕ) : ∀ k, (colSnake x A k).length = 2 * k * A.length
  | 0 => by simp [colSnake]
  | k + 1 => by
    rw [colSnake, List.length_append, List.length_append, colSnake_length x A k, colRun_length,
      colRun_length, List.length_reverse]
    ring

theorem colSnakeT_time (x : ℕ) (A : List ℕ) (k : ℕ) :
    (colSnakeT x A k).time ≤ 3 * (2 * k * A.length) + 3 * k + A.length + 2 := by
  have hf : ∀ i ∈ List.range k, ((do
      let a ← lmapT (fun y => (pure (x + 2 * i, y) : TimeM Coord)) A
      let b ← lmapT (fun y => (pure (x + 2 * i + 1, y) : TimeM Coord)) A.reverse
      lappendT a b) : TimeM (List Coord)).time ≤ 3 * A.length + 1 := by
    intro i _
    simp only [time_bind, lappendT, lmapT_pure_time, List.length_reverse]
    simp [lmapT]
    omega
  have hd : ∀ i ∈ List.range k, ((do
      let a ← lmapT (fun y => (pure (x + 2 * i, y) : TimeM Coord)) A
      let b ← lmapT (fun y => (pure (x + 2 * i + 1, y) : TimeM Coord)) A.reverse
      lappendT a b) : TimeM (List Coord)).ret.length ≤ 2 * A.length := by
    intro i _
    simp [lmapT, lappendT]
    omega
  have := lflatMapT_time_le _ (List.range k) _ _ hf hd
  rw [List.length_range] at this
  simp only [colSnakeT, time_bind, rangeT, lreverseT] at this ⊢
  have e : k * (3 * A.length + 1 + 2 * A.length + 1) = 5 * (k * A.length) + 2 * k := by ring
  rw [e] at this
  have : k * A.length ≤ 2 * k * A.length := by nlinarith
  nlinarith

theorem grpT_time (tbl : List (ℕ × List ℕ)) (y : ℕ) : (grpT tbl y).time ≤ tbl.length := by
  have := lfindT_time_le (fun e : ℕ × List ℕ => (pure (e.1 == y) : TimeM Bool)) tbl 0
    (fun _ _ => by simp)
  simp only [grpT, time_bind]
  split <;> simp only [time_pure] <;> omega

theorem snWT_len (r k : ℕ) (tbl : List (ℕ × List ℕ)) (a : ℕ) :
    (snWT r k tbl a).ret.length = 2 * k * (grpT tbl a).ret.length := by
  simp only [snWT, ret_bind, colSnakeT_ret, colSnake_length]

theorem snWT_time (r k : ℕ) (tbl : List (ℕ × List ℕ)) (a : ℕ) (hk : 1 ≤ k) :
    (snWT r k tbl a).time ≤ tbl.length + 4 * (snWT r k tbl a).ret.length + 3 * k + 2 := by
  have t1 := grpT_time tbl a
  have t2 := colSnakeT_time (r + 1) (grpT tbl a).ret k
  have e := snWT_len r k tbl a
  have : (grpT tbl a).ret.length ≤ 2 * k * (grpT tbl a).ret.length := by nlinarith
  simp only [snWT, time_bind] at e ⊢
  omega

/-- The steps where `GWT` inserts something: crossings and flip steps. -/
def SpStep (r k R : ℕ) (fl : Bool) (u v : Coord) : Prop :=
  (u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2) ∨ (u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2) ∨
  (fl = true ∧ u = (r, R - 1) ∧ v = (r, R)) ∨ (fl = true ∧ u = (r, R) ∧ v = (r, R - 1))

instance (r k R : ℕ) (fl : Bool) (u v : Coord) : Decidable (SpStep r k R fl u v) := by
  unfold SpStep; infer_instance

theorem GWT_time (r k R : ℕ) (fl : Bool) (tbl : List (ℕ × List ℕ)) (u v : Coord) (hk : 1 ≤ k) :
    (GWT r k R fl tbl u v).time ≤
      (if SpStep r k R fl u v then 2 * tbl.length + 6 * k + 10 else 0) +
        6 * (GWT r k R fl tbl u v).ret.length := by
  unfold GWT
  by_cases h1 : u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2
  · rw [ite_t h1, ite_t (show SpStep r k R fl u v from Or.inl h1)]
    have := snWT_time r k tbl u.2 hk
    omega
  rw [ite_f h1]
  by_cases h2 : u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2
  · rw [ite_t h2, ite_t (show SpStep r k R fl u v from Or.inr (Or.inl h2))]
    have := snWT_time r k tbl u.2 hk
    simp only [time_bind, ret_bind, lreverseT, List.length_reverse]
    omega
  rw [ite_f h2]
  by_cases h3 : fl = true ∧ u = (r, R - 1) ∧ v = (r, R)
  · rw [ite_t h3, ite_t (show SpStep r k R fl u v from Or.inr (Or.inr (Or.inl h3)))]
    have t1 := snWT_time r k tbl (R - 1) hk
    have t2 := snWT_time r k tbl R hk
    simp only [time_bind, ret_bind, lreverseT, lappendT, List.length_reverse, List.length_append]
    omega
  rw [ite_f h3]
  by_cases h4 : fl = true ∧ u = (r, R) ∧ v = (r, R - 1)
  · rw [ite_t h4, ite_t (show SpStep r k R fl u v from Or.inr (Or.inr (Or.inr h4)))]
    have t1 := snWT_time r k tbl (R - 1) hk
    have t2 := snWT_time r k tbl R hk
    simp only [time_bind, ret_bind, lreverseT, lappendT, List.length_reverse, List.length_append]
    omega
  rw [ite_f h4, ite_f (show ¬ SpStep r k R fl u v by unfold SpStep; tauto)]
  simp

/-- The number of special steps of a list. -/
def spCount (P : Coord → Coord → Prop) [∀ u v, Decidable (P u v)] : List Coord → ℕ
  | u :: v :: l => (if P u v then 1 else 0) + spCount P (v :: l)
  | _ => 0

theorem insManyT_time (G : Coord → Coord → TimeM (List Coord)) (P : Coord → Coord → Prop)
    [∀ u v, Decidable (P u v)] (B : ℕ)
    (hG : ∀ u v, (G u v).time ≤ (if P u v then B else 0) + 6 * (G u v).ret.length) :
    ∀ S : List Coord, (insManyT G S).time ≤ 7 * (insManyT G S).ret.length + B * spCount P S
  | [] => by simp [insManyT]
  | [_] => by simp [insManyT]
  | a :: b :: l => by
    have ih := insManyT_time G P B hG (b :: l)
    have g := hG a b
    simp only [insManyT, time_bind, ret_bind, lappendT, time_pure, ret_pure, List.length_cons,
      List.length_append, spCount] at ih g ⊢
    split_ifs at g ⊢ <;> nlinarith

theorem insManyT_len (G : Coord → Coord → TimeM (List Coord)) :
    ∀ S : List Coord, S.length ≤ (insManyT G S).ret.length
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => by
    have := insManyT_len G (b :: l)
    simp only [insManyT, ret_bind, lappendT, ret_pure, List.length_cons, List.length_append] at this ⊢
    omega

/-! ### Special steps are crossings or steps along line `r` -/

theorem sp_shift {r k R : ℕ} {fl : Bool} (hR : fl = true → 1 ≤ R) {a b : Coord}
    (h : SpStep r k R fl (shW r (2 * k) a) (shW r (2 * k) b)) :
    (((a.1 = r ∧ b.1 = r + 1) ∨ (a.1 = r + 1 ∧ b.1 = r)) ∧ a.2 = b.2) ∨
      (a.1 = r ∧ b.1 = r ∧ b.2 = a.2 + 1) ∨ (a.1 = r ∧ b.1 = r ∧ a.2 = b.2 + 1) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  cases fl
  · unfold SpStep shW at h
    simp only [Bool.false_eq_true, false_and, or_false] at h
    split_ifs at h <;> simp only at h ⊢ <;> omega
  · have := hR rfl
    unfold SpStep shW at h
    simp only [true_and] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h ⊢ <;> omega

theorem spCount_shift {r k R : ℕ} {fl : Bool} (hR : fl = true → 1 ≤ R) : ∀ L : List Coord,
    spCount (SpStep r k R fl) (L.map (shW r (2 * k))) ≤
      (crossRowsT r L).ret.length + (flipRowsT r L).ret.length
  | [] => by simp [spCount]
  | [_] => by simp [spCount]
  | a :: b :: l => by
    have ih := spCount_shift (r := r) (k := k) hR (b :: l)
    simp only [List.map_cons] at ih ⊢
    simp only [spCount, crossRowsT, flipRowsT, ret_bind]
    have key := fun h => sp_shift (r := r) (k := k) (R := R) (fl := fl) hR (a := a) (b := b) h
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> (try simp only [List.length_cons]) <;>
      first | omega | (exfalso; rcases key h1 with h | h | h <;> tauto)

/-! ### The table of attached rows -/

theorem runDnT_time (cv : ℕ → TimeM Bool) (C : ℕ) (hC : ∀ y, (cv y).time ≤ C) :
    ∀ a, (runDnT cv a).time ≤ ((runDnT cv a).ret.length + 1) * (C + 1)
  | 0 => by simp [runDnT]
  | n + 1 => by
    have ih := runDnT_time cv C hC n
    have hc := hC n
    simp only [runDnT, time_bind, ret_bind]
    split_ifs
    · simp; omega
    · simp only [time_bind, ret_bind, List.length_cons]
      nlinarith

theorem runUpFT_time (cv : ℕ → TimeM Bool) (C : ℕ) (hC : ∀ y, (cv y).time ≤ C) :
    ∀ k y, (runUpFT cv k y).time ≤ ((runUpFT cv k y).ret.length + 1) * (C + 1)
  | 0, _ => by simp [runUpFT]
  | k + 1, y => by
    have ih := runUpFT_time cv C hC k (y + 1)
    have hc := hC y
    simp only [runUpFT, time_bind, ret_bind]
    split_ifs
    · simp; omega
    · simp only [time_bind, ret_bind, List.length_cons]
      nlinarith

theorem attWT_time (cv : ℕ → TimeM Bool) (C : ℕ) (hC : ∀ y, (cv y).time ≤ C) (h R a : ℕ) :
    (attWT cv h R a).time ≤ ((attWT cv h R a).ret.length + 1) * (C + 1) := by
  unfold attWT
  split_ifs
  · exact runDnT_time cv C hC a
  · exact runUpFT_time cv C hC _ _

theorem sum_ite_filter {α : Type} (c : α → Bool) (f : α → ℕ) : ∀ l : List α,
    (l.map (fun a => if c a then f a else 0)).sum = ((l.filter c).map f).sum
  | [] => rfl
  | a :: l => by
    have := sum_ite_filter c f l
    by_cases hc : c a <;> simp [hc, this]

/-- **The attached rows of all covered rows below `h` number at most `h`.** -/
theorem sum_att_le (c : ℕ → Bool) (h R : ℕ) :
    ((List.range h).map (fun a => if c a then (attW c h R a).length + 1 else 0)).sum ≤ 2 * h := by
  rw [sum_ite_filter]
  set F := (List.range h).filter c with hF
  have hFn : F.Nodup := (List.nodup_range).filter _
  have hFl : F.length ≤ h := by
    have := List.length_filter_le c (List.range h); rw [List.length_range] at this; exact this
  have hnd : (F.flatMap (attW c h R)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => (List.nodup_cons.mp (nodup_grpW (cv := c) (h := h) (R := R) a)).2, ?_⟩
    refine (List.nodup_iff_pairwise_ne.mp hFn).imp_of_mem (fun {a b} ha hb hne => ?_)
    show List.Disjoint (attW c h R a) (attW c h R b)
    rw [List.disjoint_left]
    intro x hxa hxb
    have ca : c a = true := (List.mem_filter.mp ha).2
    have cb : c b = true := (List.mem_filter.mp hb).2
    exact grpW_disj ca cb hne (List.mem_cons_of_mem _ hxa) (List.mem_cons_of_mem _ hxb)
  have hlt : ∀ y ∈ F.flatMap (attW c h R), y < h := by
    intro y hy
    obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
    exact attW_lt (List.mem_range.mp (List.mem_filter.mp ha).1) hya
  have hfl := length_le_of_nodup_lt hnd hlt
  rw [List.length_flatMap] at hfl
  have e : (F.map (fun a => (attW c h R a).length + 1)).sum =
      (F.map (fun a => (attW c h R a).length)).sum + F.length := by
    clear hF hFn hFl hnd hlt hfl
    induction F with
    | nil => rfl
    | cons a F ih => simp [ih]; omega
  rw [e]
  omega

theorem sum_map_le_mul {α : Type} (F g : α → ℕ) (C : ℕ) (hF : ∀ a, F a ≤ C * (1 + g a)) :
    ∀ l : List α, (l.map F).sum ≤ C * (l.length + (l.map g).sum)
  | [] => by simp
  | a :: l => by
    have := sum_map_le_mul F g C hF l
    have := hF a
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem tblT_time (cv : ℕ → TimeM Bool) (c : ℕ → Bool) (hc : ∀ y, (cv y).ret = c y) (C : ℕ)
    (hC : ∀ y, (cv y).time ≤ C) (h R : ℕ) : (tblT cv h R).time ≤ h + 1 + (C + 1) * (3 * h) := by
  have hF : ∀ a, (((do
      let b ← cv a
      if b then do
        let l ← attWT cv h R a
        pure (some (a, l))
      else pure none) : TimeM (Option (ℕ × List ℕ))).time + 1) ≤
      (C + 1) * (1 + (if c a then (attW c h R a).length + 1 else 0)) := by
    intro a
    have t1 := hC a
    simp only [time_bind, hc]
    by_cases ha : c a = true
    · rw [ite_t ha, ite_t ha]
      have t2 := attWT_time cv C hC h R a
      rw [attWT_ret cv c hc] at t2
      simp only [time_bind, time_pure]
      nlinarith
    · rw [ite_f ha, ite_f ha]
      simp only [time_pure]
      nlinarith
  have := sum_map_le_mul _ _ (C + 1) hF (List.range h)
  have hs := sum_att_le c h R
  rw [List.length_range] at this
  simp only [tblT, time_bind, rangeT, lfilterMapT] at this ⊢
  nlinarith

/-! ### The wide band -/

theorem tblT_len (cv : ℕ → TimeM Bool) (h R : ℕ) : (tblT cv h R).ret.length ≤ h := by
  simp only [tblT, ret_bind, rangeT, lfilterMapT]
  have := List.length_filterMap_le (fun a => ((do
      let c ← cv a
      if c then do
        let l ← attWT cv h R a
        pure (some (a, l))
      else pure none) : TimeM (Option (ℕ × List ℕ))).ret) (List.range h)
  rw [List.length_range] at this
  exact this

theorem cvT_time (cr : List ℕ) (R : ℕ) (fl : Bool) (y : ℕ) : (cvT cr R fl y).time ≤ cr.length + 1 := by
  simp [cvT, lcontainsT]

theorem wideTailT_time (h r k : ℕ) (cr : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord)
    (hk : 1 ≤ k) (hcr : cr.length ≤ 2 * h)
    (hsp : spCount (SpStep r k R fl) (p.map (shW r (2 * k))) +
      spCount (SpStep r k R fl) (q.map (shW r (2 * k))) ≤ 4 * h) :
    (wideTailT h r k cr R fl p q).time ≤ h + 1 + (2 * h + 2) * (3 * h) + p.length + q.length +
      7 * ((wideTailT h r k cr R fl p q).ret.1.length + (wideTailT h r k cr R fl p q).ret.2.length) +
      (2 * h + 6 * k + 10) * (4 * h) := by
  set tbl := (tblT (cvT cr R fl) h R).ret with htbl
  have t1 := tblT_time (cvT cr R fl) (fun y => (cvT cr R fl y).ret) (fun y => rfl) (2 * h + 1)
    (fun y => by have := cvT_time cr R fl y; omega) h R
  have hl : tbl.length ≤ h := tblT_len (cvT cr R fl) h R
  have hG : ∀ u v, (GWT r k R fl tbl u v).time ≤
      (if SpStep r k R fl u v then 2 * h + 6 * k + 10 else 0) + 6 * (GWT r k R fl tbl u v).ret.length := by
    intro u v
    have := GWT_time r k R fl tbl u v hk
    split_ifs at this ⊢ <;> omega
  have i1 := insManyT_time _ _ _ hG ((shWT r (2 * k) p).ret)
  have i2 := insManyT_time _ _ _ hG ((shWT r (2 * k) q).ret)
  rw [shWT_ret] at i1 i2
  have s1 : (shWT r (2 * k) p).time = p.length := lmapT_pure_time _ p
  have s2 : (shWT r (2 * k) q).time = q.length := lmapT_pure_time _ q
  simp only [wideTailT, time_bind, ret_bind, ret_pure, time_pure, shWT_ret] at s1 s2 ⊢
  rw [← htbl] at *
  nlinarith

/-- **The wide band costs `O(area + h²)` steps.** -/
theorem wideBandT_time {J : Inst} {p q : List Coord} {r k : ℕ} (hsol : IsSolution J p q)
    (hr : r < J.w) (hfree : LineFree J r) (hh : 0 < J.h) (hk : 1 ≤ k) :
    (wideBandT J.h r k p q).time ≤ 22 * ((J.w + 2 * k) * J.h) + 40 * (J.h + 1) ^ 2 := by
  have hpn := hsol.1.2.2.1
  have hqn := hsol.2.1.2.2.1
  obtain ⟨rp, rq⟩ := rows_lt hsol
  have lcp := crossRowsT_len r J.h hpn rp
  have lcq := crossRowsT_len r J.h hqn rq
  have lfp := flipRowsT_len r J.h hpn rp
  have lfq := flipRowsT_len r J.h hqn rq
  have tcp := crossRowsT_time r p
  have tcq := crossRowsT_time r q
  have tfp := flipRowsT_time r p
  have tfq := flipRowsT_time r q
  have hA := sol_len hsol
  have hout : (wideBandT J.h r k p q).ret.1.length + (wideBandT J.h r k p q).ret.2.length =
      (J.w + 2 * k) * J.h := by
    have e := wideBandT_ret J r k p q rp rq
    have hs := innerLift_sol hsol hr hfree hh (by omega : 0 < k)
    rw [← e] at hs
    exact sol_len hs
  simp only [wideBandT, time_bind, ret_bind] at hout ⊢
  generalize hcr : (lappendT (crossRowsT r p).ret (crossRowsT r q).ret).ret = cr at hout ⊢
  generalize hfr : (lappendT (flipRowsT r p).ret (flipRowsT r q).ret).ret = fr at hout ⊢
  have lcr : cr.length ≤ 2 * J.h := by rw [← hcr]; simp [lappendT]; omega
  have lfr : fr.length ≤ 2 * J.h := by rw [← hfr]; simp [lappendT]; omega
  have tfind := lfindT_time_le (seedT J.h cr fr) (rangeT (J.h + 1)).ret (2 * cr.length + fr.length + 3)
    (fun R _ => seedT_time J.h cr fr R)
  simp only [rangeT, List.length_range] at tfind
  generalize ho : (lfindT (seedT J.h cr fr) (rangeT (J.h + 1)).ret).ret = o at hout ⊢
  have hR : (o.isSome && !((o.getD 0 == 0 || (lcontainsT cr (o.getD 0 - 1)).ret) &&
      (o.getD 0 == J.h || (lcontainsT cr (o.getD 0)).ret))) = true → 1 ≤ o.getD 0 := by
    intro hf
    cases o with
    | none => simp at hf
    | some R =>
      have hs : (seedT J.h cr fr R).ret = true := by
        have h' : List.find? (fun x => (seedT J.h cr fr x).ret) (List.range (J.h + 1)) = some R := by
          rw [← ho]; rfl
        exact List.find?_some (p := fun x => (seedT J.h cr fr x).ret) h'
      simp only [Option.isSome_some, Bool.true_and, Option.getD_some] at hf ⊢
      simp only [seedT, ret_bind, ret_pure] at hs
      revert hf hs
      generalize (lcontainsT cr (R - 1)).ret = c0
      generalize (lcontainsT cr R).ret = c1
      intro hf hs
      cases c0 <;> cases c1 <;> simp at hf hs <;> omega
  have hsp := spCount_shift (r := r) (k := k) hR p
  have hsq := spCount_shift (r := r) (k := k) hR q
  have ht := wideTailT_time J.h r k cr (o.getD 0)
    (o.isSome && !((o.getD 0 == 0 || (lcontainsT cr (o.getD 0 - 1)).ret) &&
      (o.getD 0 == J.h || (lcontainsT cr (o.getD 0)).ret))) p q hk lcr (by omega)
  have e1 : (J.w + 2 * k) * J.h = J.w * J.h + 2 * (k * J.h) := by ring
  have e2 : (J.h + 1) ^ 2 = J.h * J.h + 2 * J.h + 1 := by ring
  have e3 : (2 * J.h + 2) * (3 * J.h) = 6 * (J.h * J.h) + 6 * J.h := by ring
  have e4 : (2 * J.h + 6 * k + 10) * (4 * J.h) = 8 * (J.h * J.h) + 24 * (k * J.h) + 40 * J.h := by
    ring
  have e5 : (J.h + 1) * (2 * cr.length + fr.length + 3 + 1) ≤ (J.h + 1) * (6 * J.h + 4) :=
    Nat.mul_le_mul_left _ (by omega)
  have e6 : (J.h + 1) * (6 * J.h + 4) = 6 * (J.h * J.h) + 10 * J.h + 4 := by ring
  simp only [lappendT, lcontainsT, rangeT] at ht hout ⊢
  generalize (wideTailT J.h r k cr (o.getD 0)
      (o.isSome && !((o.getD 0 == 0 || cr.contains (o.getD 0 - 1)) &&
        (o.getD 0 == J.h || cr.contains (o.getD 0)))) p q) = T at ht hout ⊢
  generalize (lfindT (seedT J.h cr fr) (List.range (J.h + 1))).time = F at tfind ⊢
  generalize T.ret.1.length = P at ht hout
  generalize T.ret.2.length = Q at ht hout
  generalize T.time = TT at ht ⊢
  have tf2 : F ≤ 6 * (J.h * J.h) + 10 * J.h + 4 := le_trans tfind (le_of_le_of_eq e5 e6)
  rw [e3, e4] at ht
  rw [e1] at hout ⊢
  rw [e2]
  omega

/-! ### The edge lifts -/

theorem findVT_time (r : ℕ) : ∀ L : List Coord, (findVT r L).time ≤ L.length
  | [] => by simp [findVT]
  | [_] => by simp [findVT]
  | u :: v :: l => by
    have := findVT_time r (v :: l)
    unfold findVT
    split_ifs
    · simp
    · simp only [time_bind, List.length_cons] at this ⊢; omega

theorem edgeBlockT_time (w h y k : ℕ) (hy : y < h) :
    (edgeBlockT w h y k).time ≤ 10 * (k * h) + 6 * k + 6 * h + 10 := by
  have t1 := colSnakeT_time w (List.range (y + 1)).reverse k
  have t2 := colSnakeT_time w ((List.range (h - (y + 1))).map (· + (y + 1))) k
  simp only [List.length_reverse, List.length_range, List.length_map] at t1 t2
  simp only [edgeBlockT, time_bind, rangeT, lreverseT, lappendT, lmapT_pure_time,
    colSnakeT_ret, colSnake_length, List.length_reverse, List.length_range]
  have e : y + 1 + (h - (y + 1)) = h := by omega
  have m1 : 2 * k * (y + 1) + 2 * k * (h - (y + 1)) = 2 * (k * h) := by
    rw [← Nat.mul_add, e]; ring
  have : lmapT (fun i => (pure (i + (y + 1)) : TimeM ℕ)) (List.range (h - (y + 1))) =
      ⟨(List.range (h - (y + 1))).map (· + (y + 1)), h - (y + 1)⟩ := by
    simp only [lmapT, ret_pure, time_pure, Nat.zero_add]
    congr 1
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_one]
  rw [this]
  simp only [List.length_map, List.length_range]
  nlinarith

theorem edgeBlock_length (w h y k : ℕ) (hy : y < h) : (edgeBlock w h y k).length = 2 * (k * h) := by
  unfold edgeBlock rowsDown rowsUp
  rw [List.length_append, List.length_reverse, colSnake_length, colSnake_length]
  simp only [List.length_reverse, List.length_range, List.length_map]
  have e : y + 1 + (h - (y + 1)) = h := by omega
  rw [← Nat.mul_add, e]; ring

theorem blkET_time (w h k : ℕ) (a b : Coord) (ha : a.2 < h) (hb : b.2 < h) :
    (blkET w h k a b).time ≤ 12 * (k * h) + 6 * k + 6 * h + 11 := by
  unfold blkET
  split_ifs
  · have := edgeBlockT_time w h a.2 k ha; omega
  · have := edgeBlockT_time w h b.2 k hb
    have l := edgeBlock_length w h b.2 k hb
    simp only [time_bind, lreverseT, edgeBlockT_ret, l]
    omega

theorem blkET_len (w h k : ℕ) (a b : Coord) (ha : a.2 < h) (hb : b.2 < h) :
    (blkET w h k a b).ret.length = 2 * (k * h) := by
  rw [blkET_ret]
  unfold blkE
  split_ifs
  · exact edgeBlock_length w h a.2 k ha
  · rw [List.length_reverse]; exact edgeBlock_length w h b.2 k hb

theorem insBT_time (a b : Coord) (X : List Coord) :
    ∀ L : List Coord, (insBT a b X L).time ≤ L.length + X.length + 2
  | [] => by simp [insBT]
  | [_] => by simp [insBT]
  | x :: y :: l => by
    have := insBT_time a b X (y :: l)
    unfold insBT
    split_ifs
    · simp [lappendT]
    · simp only [time_bind, List.length_cons] at this ⊢; omega

theorem insB_length_le (a b : Coord) (X : List Coord) :
    ∀ L : List Coord, (insB a b X L).length ≤ L.length + X.length
  | [] => by simp [insB]
  | [_] => by simp [insB]
  | x :: y :: l => by
    have := insB_length_le a b X (y :: l)
    unfold insB
    split_ifs
    · simp; omega
    · simp only [List.length_cons] at this ⊢; omega

/-- A found step lies on the path, so its rows are below `h`. -/
theorem findV_rows {r h : ℕ} {L : List Coord} (hL : ∀ v ∈ L, v.2 < h) {a b : Coord}
    (hf : findV r L = some (a, b)) : a.2 < h ∧ b.2 < h := by
  obtain ⟨hab, -⟩ := findV_some hf
  exact ⟨hL a (hab.subset (by simp)), hL b (hab.subset (by simp))⟩

theorem edgeLiftT_time (w h k : ℕ) (p q : List Coord) (hp : ∀ v ∈ p, v.2 < h)
    (hq : ∀ v ∈ q, v.2 < h) :
    (edgeLiftT w h k p q).time ≤ 2 * (p.length + q.length) + 14 * (k * h) + 6 * k + 6 * h + 13 ∧
    (edgeLiftT w h k p q).ret.1.length + (edgeLiftT w h k p q).ret.2.length ≤
      p.length + q.length + 2 * (k * h) := by
  have f1 := findVT_time (w - 1) p
  have f2 := findVT_time (w - 1) q
  unfold edgeLiftT
  simp only [time_bind, ret_bind, findVT_ret] at f1 f2 ⊢
  cases hfp : findV (w - 1) p with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨ra, rb⟩ := findV_rows hp hfp
    have t1 := blkET_time w h k a b ra rb
    have l1 := blkET_len w h k a b ra rb
    have t2 := insBT_time a b (blkET w h k a b).ret p
    have l2 := insB_length_le a b (blkET w h k a b).ret p
    simp only [time_bind, ret_bind, time_pure, ret_pure, insBT_ret]
    constructor <;> omega
  | none =>
    simp only [time_bind, ret_bind, findVT_ret]
    cases hfq : findV (w - 1) q with
    | some ab =>
      obtain ⟨a, b⟩ := ab
      obtain ⟨ra, rb⟩ := findV_rows hq hfq
      have t1 := blkET_time w h k a b ra rb
      have l1 := blkET_len w h k a b ra rb
      have t2 := insBT_time a b (blkET w h k a b).ret q
      have l2 := insB_length_le a b (blkET w h k a b).ret q
      simp only [time_bind, ret_bind, time_pure, ret_pure, insBT_ret]
      constructor <;> omega
    | none =>
      simp only [time_pure, ret_pure]
      constructor <;> omega

theorem reflT_time (w : ℕ) (L : List Coord) : (reflT w L).time = L.length := lmapT_pure_time _ L

theorem edgeLiftLT_time (w h k : ℕ) (p q : List Coord) (hp : ∀ v ∈ p, v.2 < h)
    (hq : ∀ v ∈ q, v.2 < h) :
    (edgeLiftLT w h k p q).time ≤ 4 * (p.length + q.length) + 16 * (k * h) + 6 * k + 6 * h + 13 := by
  have hp' : ∀ v ∈ (reflT w p).ret, v.2 < h := by
    rw [reflT_ret]; intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hp u hu
  have hq' : ∀ v ∈ (reflT w q).ret, v.2 < h := by
    rw [reflT_ret]; intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hq u hu
  obtain ⟨t, l⟩ := edgeLiftT_time w h k _ _ hp' hq'
  simp only [reflT_ret, List.length_map] at t l
  simp only [edgeLiftLT, time_bind, reflT_time, time_pure, reflT_ret]
  omega

/-! ### The block finder -/

theorem innerPairT_time (I : Inst) : (innerPairT I).time ≤ 200 := by
  simp only [innerPairT, time_bind, ret_bind, lmapT, lflatMapT, lfindT, lallT, ret_pure, time_pure,
    Inst.ends, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.flatMap_cons,
    List.flatMap_nil, List.length_cons, List.length_nil, List.append_nil, List.cons_append,
    List.nil_append]
  omega

theorem blkXT_time (I : Inst) : (blkXT I).time ≤ 200 := by
  unfold blkXT
  split_ifs
  · simp
  · simp
  · have := innerPairT_time I
    simp only [time_bind]
    split <;> simp only [time_pure] <;> omega

/-! ### One block level -/

/-- What the counted inner lift needs, for an inner block found by `blkX`. -/
theorem blkX_inner {I : Inst} {r k : ℕ} (hI : InDom I) (hb : blkX I = some (.inner r k)) :
    1 ≤ k ∧ r < (I.dropIn r (2 * k)).w ∧ LineFree (I.dropIn r (2 * k)) r := by
  unfold blkX at hb
  split_ifs at hb with hl hr
  · cases hb
  · cases hb
  cases hp : innerPair I with
  | none => rw [hp] at hb; cases hb
  | some ab =>
    rw [hp] at hb
    simp only [Option.some.injEq, Blk.inner.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a, c⟩ := ab
    have hg := List.find?_some hp
    have hmem := List.mem_of_find?_eq_some hp
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨a', ha', c', hc', rfl, rfl⟩ := hmem
    simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
    obtain ⟨⟨hac, hbet⟩, hk1⟩ := hg
    obtain ⟨s1, s2⟩ := innerK_spec hk1
    obtain ⟨ec, hec, ec1⟩ := mem_xsOf.mp hc'
    have hcw : c' < I.w := ec1 ▸ ends_lt_w hI.2.2 ec hec
    have side : ∀ e ∈ I.ends, e.1 ≤ a' ∨ c' ≤ e.1 := by
      intro e hm
      have := hbet e.1 (List.mem_map_of_mem hm)
      omega
    refine ⟨hk1, by simp only [Inst.dropIn, Inst.mapE]; omega, fun y => ?_⟩
    have key : ∀ e ∈ I.ends, ((a' + 1, y) : Coord) ≠
        (if e.1 ≤ a' + 1 then e else (e.1 - 2 * innerK I a' c', e.2)) := by
      intro e hm hre
      have := side e hm
      split_ifs at hre with h1
      · rw [← hre] at this; simp only at this; omega
      · have := congrArg Prod.fst hre; simp only at this; omega
    obtain ⟨k0, k1, k2, k3⟩ := ends_all key
    exact ⟨k0, k1, k2, k3⟩

theorem del_dims (b : Blk) (I : Inst) (hb : blkX I = some b) :
    (b.del I).h = I.h ∧ (b.del I).w + 2 * b.k = I.w ∧ 1 ≤ b.k := by
  have hw := w_del b I
  unfold blkX at hb
  split_ifs at hb with hl hr
  · cases hb
    have := (leftK_spec hl).2
    exact ⟨rfl, by simp only [Blk.k] at hw ⊢; omega, hl⟩
  · cases hb
    have := (rightK_spec hr).2
    exact ⟨rfl, by simp only [Blk.k] at hw ⊢; omega, hr⟩
  · cases hp : innerPair I with
    | none => rw [hp] at hb; cases hb
    | some ab =>
      rw [hp] at hb
      cases hb
      have hg := List.find?_some hp
      simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] at hg
      have := (innerK_spec hg.2).2
      exact ⟨rfl, by simp only [Blk.k] at hw ⊢; omega, hg.2⟩

/-- **One lift costs `O((M + 1)²)` steps.** -/
theorem liftT_time {I : Inst} {b : Blk} {p q : List Coord} {M : ℕ} (hI : InDom I)
    (hb : blkX I = some b) (hsol : IsSolution (b.del I) p q) (hw : I.w ≤ M) (hh : I.h ≤ M) :
    (b.liftT (b.del I) p q).time ≤ 75 * (M + 1) ^ 2 := by
  obtain ⟨eh, ew, hk⟩ := del_dims b I hb
  have hA := sol_len hsol
  obtain ⟨rp, rq⟩ := rows_lt hsol
  have m1 : (b.del I).w * (b.del I).h + 2 * b.k * (b.del I).h = I.w * I.h := by
    rw [← Nat.add_mul, ew, eh]
  have m2 : I.w * I.h ≤ M * M := Nat.mul_le_mul hw hh
  have m3 : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
  cases b with
  | left k =>
    have t := edgeLiftLT_time ((Blk.left k).del I).w ((Blk.left k).del I).h k p q rp rq
    simp only [Blk.liftT, Blk.k] at t m1 hk ew ⊢
    rw [eh] at t m1 hA ⊢
    have : 2 * k * I.h = 2 * (k * I.h) := by ring
    nlinarith
  | right k =>
    have t := (edgeLiftT_time ((Blk.right k).del I).w ((Blk.right k).del I).h k p q rp rq).1
    simp only [Blk.liftT, Blk.k] at t m1 hk ew ⊢
    rw [eh] at t m1 hA ⊢
    have : 2 * k * I.h = 2 * (k * I.h) := by ring
    nlinarith
  | inner r k =>
    obtain ⟨-, hr, hfree⟩ := blkX_inner hI hb
    have hh0 : 0 < ((Blk.inner r k).del I).h := by rw [eh]; have := hI.2.1; omega
    have t := wideBandT_time hsol hr hfree hh0 hk
    simp only [Blk.liftT, Blk.k] at t ew ⊢
    rw [ew] at t
    rw [eh] at t ⊢
    have : (I.h + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

/-! ### The construction -/

theorem liftBT_time {I : Inst} {b : Blk} {M : ℕ} (hI : InDom I) (hb : blkX I = some b)
    (hw : I.w ≤ M) (hh : I.h ≤ M) (o : Sol)
    (ho : ∀ pq, o = some pq → IsSolution (b.del I) pq.1 pq.2) :
    (liftBT b (b.del I) o).time ≤ 75 * (M + 1) ^ 2 := by
  cases o with
  | none => simp [liftBT]
  | some pq =>
    have := liftT_time hI hb (ho pq rfl) hw hh
    simp only [liftBT, time_bind, time_pure]
    omega

theorem liftBTT_time {I : Inst} {b : Blk} {M : ℕ} (hI : InDom I) (hb : blkX I.transpose = some b)
    (hw : I.w ≤ M) (hh : I.h ≤ M) (o : Sol)
    (ho : ∀ pq, o = some pq → IsSolution (b.del I.transpose) pq.1 pq.2) :
    (liftBTT b (b.del I.transpose) o).time ≤ 77 * (M + 1) ^ 2 := by
  cases o with
  | none => simp [liftBTT]
  | some pq =>
    have hIT := inDom_transpose hI
    have ok := blkX_ok hIT hb
    have hsol := ho pq rfl
    obtain ⟨r1, r2⟩ := rows_lt hsol
    have t := liftT_time hIT hb hsol hh hw
    have hs := ok.lift _ _ hsol
    rw [← liftT_ret b _ _ _ r1 r2] at hs
    have hl := sol_len hs
    have s1 := swapT_time (b.liftT (b.del I.transpose) pq.1 pq.2).ret.1
    have s2 := swapT_time (b.liftT (b.del I.transpose) pq.1 pq.2).ret.2
    have m : I.transpose.w * I.transpose.h ≤ M * M := Nat.mul_le_mul hh hw
    have m3 : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
    simp only [liftBTT, time_bind, time_pure]
    nlinarith

/-- **The step bound of the block construction**, by the number of open gaps. -/
theorem solveRT_time {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J) (M L : ℕ)
    (hleaf : ∀ J : Inst, J.WellFormed → J.w ≤ M → J.h ≤ M →
      ((J.w ≤ 10 ∨ J.h ≤ 10) ∨ (J.w ≤ 37 ∧ J.h ≤ 37)) → (solveZT thinT J).time ≤ L) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → I.w ≤ M → I.h ≤ M →
      (solveRT thinT n I).time ≤ (phi I + 1) * (80 * (M + 1) ^ 2 + 400) + L := by
  intro n
  induction n with
  | zero => intro I _ _ _; simp [solveRT]
  | succ n ih =>
    intro I hwf hw hh
    have hC : 400 ≤ 80 * (M + 1) ^ 2 + 400 := by omega
    simp only [solveRT]
    split_ifs with hs
    · have := hleaf I hwf hw hh (Or.inl hs)
      nlinarith
    · have hI := inDom_of hwf hs
      have tb := blkXT_time I
      simp only [time_bind, blkXT_ret]
      cases hb : blkX I with
      | some b =>
        have ok := blkX_ok hI hb
        have hJ := (chain_inDom ok.chain hI).2.2
        have hJw : (b.del I).w ≤ M := by have := ok.smaller; omega
        have hJh : (b.del I).h ≤ M := by rw [ok.sameH]; exact hh
        have hrec := ih (b.del I) hJ hJw hJh
        have hphi := phi_del hb
        have tl := liftBT_time hI hb hw hh (solveRT thinT n (b.del I)).ret (fun pq hpq => by
          rw [solveRT_ret hret n _ hJ] at hpq
          exact solveR_sound thin n _ pq.1 pq.2 hJ hpq)
        simp only [time_bind]
        nlinarith
      | none =>
        have tbT := blkXT_time I.transpose
        simp only [time_bind, blkXT_ret]
        cases hbT : blkX I.transpose with
        | some b =>
          have hIT := inDom_transpose hI
          have ok := blkX_ok hIT hbT
          have hJ := (chain_inDom ok.chain hIT).2.2
          have hJw : (b.del I.transpose).w ≤ M := by
            have := ok.smaller; have : I.transpose.w = I.h := rfl; omega
          have hJh : (b.del I.transpose).h ≤ M := by rw [ok.sameH]; exact hw
          have hrec := ih (b.del I.transpose) hJ hJw hJh
          have hphi := phi_delT hbT
          have tl := liftBTT_time hI hbT hw hh (solveRT thinT n (b.del I.transpose)).ret
            (fun pq hpq => by
              rw [solveRT_ret hret n _ hJ] at hpq
              exact solveR_sound thin n _ pq.1 pq.2 hJ hpq)
          simp only [time_bind]
          nlinarith
        | none =>
          have h37 : I.w ≤ 37 := w_le_of_none hb
          have h37' : I.h ≤ 37 := w_le_of_none hbT
          have := hleaf I hwf hw hh (Or.inr ⟨h37, h37'⟩)
          nlinarith

/-! ### The leaves and the main theorem -/

/-- A leaf with a side at most 10: the thin solver runs once. -/
theorem solveZT_thin_time {J : Inst} (hwf : J.WellFormed) (hs : J.w ≤ 10 ∨ J.h ≤ 10) :
    (solveZT thinSolveWT J).time ≤ (J.w * J.h + 1) ^ 2 * Kw 16 + 3 * (J.w * J.h + 1) ^ 2 + 10 := by
  unfold solveZT
  rw [ite_t ((wfB_iff J).2 hwf)]
  have h1 : 1 ≤ J.w := by have := hwf.1; unfold InBounds at this; omega
  obtain ⟨n, hn⟩ : ∃ n, J.w + J.h = n + 1 := ⟨J.w + J.h - 1, by omega⟩
  rw [hn]
  simp only [solveRecT, ite_t hs, time_bind]
  have t := thinSolveWT_time J
  have k : Kw (min J.w J.h) ≤ Kw 16 := Kw_mono (by omega)
  have c := checkET_time J (thinSolveWT J).ret (J.w * J.h) (fun x hx => by
    rw [thinSolveWT_ret] at hx; exact thinSolveW_len J x hx)
  have := Nat.mul_le_mul_left ((J.w * J.h + 1) ^ 2) k
  omega

/-- A leaf with both sides at most 37: the step bound of `solveZ2` at `M = 37`. -/
theorem solveZT_box_time {J : Inst} (hw : J.w ≤ 37) (hh : J.h ≤ 37) :
    (solveZT thinSolveWT J).time ≤
      74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) ^ 2 * Kw 16 + 3 * (16 * 37 + 1) ^ 2 + 10) := by
  have h := solveZT_time thinSolveWT_ret thinSolveW_len 37 ((16 * 37 + 1) ^ 2 * Kw 16)
    (fun J' a b c => by
      have t := thinSolveWT_time J'
      have k : Kw (min J'.w J'.h) ≤ Kw 16 := Kw_mono (by omega)
      have area : J'.w * J'.h ≤ 16 * 37 := by
        rcases c with c | c
        · exact Nat.mul_le_mul c b
        · rw [Nat.mul_comm]; exact Nat.mul_le_mul c a
      have s : (J'.w * J'.h + 1) ^ 2 ≤ (16 * 37 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      exact le_trans t (Nat.mul_le_mul s k)) J hw hh
  exact le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)

/-- **The block construction, counted.** Every answer of `solveZ3T thinSolveWT` is a solution, it
returns one for every well-formed solvable instance, and on a `w × h` instance with
`M = max w h` it takes `O(M²)` steps. -/
theorem solveZ3T_main (I : Inst) :
    (∀ p q, (solveZ3T thinSolveWT I).ret = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, (solveZ3T thinSolveWT I).ret = some (p, q)) ∧
    (solveZ3T thinSolveWT I).time ≤ 37 * (80 * (max I.w I.h + 1) ^ 2 + 400) +
      ((16 * max I.w I.h + 1) ^ 2 * Kw 16 + 3 * (16 * max I.w I.h + 1) ^ 2 + 10) +
      (74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) ^ 2 * Kw 16 + 3 * (16 * 37 + 1) ^ 2 + 10)) := by
  refine ⟨fun p q h => solveZ3_sound _ (by rw [← solveZ3T_ret thinSolveWT_ret]; exact h),
    fun hwf hS => by rw [solveZ3T_ret thinSolveWT_ret]; exact solveZ3_complete thinOK16 hwf hS, ?_⟩
  set M := max I.w I.h
  set B := 74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) ^ 2 * Kw 16 + 3 * (16 * 37 + 1) ^ 2 + 10)
  set T := (16 * M + 1) ^ 2 * Kw 16 + 3 * (16 * M + 1) ^ 2 + 10
  unfold solveZ3T
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf)]
    have h := solveRT_time thinSolveWT_ret M (T + B)
      (fun J hJ a b c => by
        rcases c with c | ⟨c1, c2⟩
        · have t := solveZT_thin_time hJ c
          have area : J.w * J.h ≤ 16 * M := by
            rcases c with c | c
            · exact Nat.mul_le_mul (by omega) b
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) a
          have s : (J.w * J.h + 1) ^ 2 ≤ (16 * M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have s1 := Nat.mul_le_mul_right (Kw 16) s
          have s3 := Nat.mul_le_mul_left 3 s
          exact le_trans t (Nat.le_add_right_of_le (by omega))
        · exact le_trans (solveZT_box_time c1 c2) (Nat.le_add_left _ _))
      (I.w + I.h) I hwf (le_max_left _ _) (le_max_right _ _)
    have hp := phi_le I
    have : (phi I + 1) * (80 * (M + 1) ^ 2 + 400) ≤ 37 * (80 * (M + 1) ^ 2 + 400) :=
      Nat.mul_le_mul_right _ (by omega)
    clear_value T B
    generalize 80 * (M + 1) ^ 2 + 400 = C at h this ⊢
    generalize (phi I + 1) * C = X at h this
    generalize (solveRT thinSolveWT (I.w + I.h) I).time = Y at h ⊢
    omega
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h))]
    simp

end ZZN.T
