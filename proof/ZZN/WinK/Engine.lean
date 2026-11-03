/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.WinNorm

@[expose] public section

/-!
# Checkpointed window certificates

The window DP (`ZZN.Win.inside`) is replayed against literal checkpoints: the state set after
every cell is given as data, a packed set of codes. One small kernel check per (stage, bucket)
shows that every successor of a state in the bucket is in the next checkpoint
(`stepOK`), and one check per final bucket shows that every final state fails the outside test
(`finalOK`). `cov_init` and `cov_stage` carry the covering through the stages, and
`certify_of_cov` turns it into the certificate `∀ s ∈ inside …, outsideOK … s =
false`.

The encoding of states is not proved injective: every check re-decodes the code it looks up and
compares with the state, so a wrong encoding only makes a check fail.
-/

namespace ZZN.WinK

open ZZN ZZN.Win

/-- Bits per packed code. -/
def W : ℕ := 192

/-- Entry `k` of a packed array. -/
def getW (arr k : ℕ) : ℕ := (arr >>> (W * k)) % 2 ^ W

/-- A packed set: buckets `(array, count)`. -/
abbrev KSet := List (ℕ × ℕ)

def Mem (L : KSet) (x : ℕ) : Prop := ∃ p ∈ L, ∃ k < p.2, getW p.1 k = x

/-- Binary search in a sorted packed array, entries `lo ≤ k < hi`. -/
def bsearch (arr x : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, lo, hi =>
    if lo < hi then
      if getW arr ((lo + hi) / 2) = x then true
      else if getW arr ((lo + hi) / 2) < x then bsearch arr x f ((lo + hi) / 2 + 1) hi
      else bsearch arr x f lo ((lo + hi) / 2)
    else false

theorem bsearch_sound {arr x : ℕ} : ∀ (f lo hi : ℕ), bsearch arr x f lo hi = true →
    ∃ k, lo ≤ k ∧ k < hi ∧ getW arr k = x
  | 0, _, _, h => by simp [bsearch] at h
  | f + 1, lo, hi, h => by
    unfold bsearch at h
    split_ifs at h with h1 h2 h3
    · exact ⟨(lo + hi) / 2, by omega, by omega, h2⟩
    · obtain ⟨k, hk1, hk2, hk3⟩ := bsearch_sound f _ _ h
      exact ⟨k, by omega, hk2, hk3⟩
    · obtain ⟨k, hk1, hk2, hk3⟩ := bsearch_sound f _ _ h
      exact ⟨k, hk1, by omega, hk3⟩

/-- Look `x` up in bucket `j` of `L` (the caller chooses `j`; any choice is sound). -/
def memL (L : KSet) (j x : ℕ) : Bool :=
  match L[j]? with
  | some p => bsearch p.1 x 64 0 p.2
  | none => false

theorem memL_sound {L : KSet} {j x : ℕ} (h : memL L j x = true) : Mem L x := by
  unfold memL at h
  split at h
  · rename_i p hp
    obtain ⟨k, -, hk, hx⟩ := bsearch_sound _ _ _ h
    exact ⟨p, List.mem_of_getElem? hp, k, hk, hx⟩
  · simp at h

/-- Choose the bucket whose first code is the largest one `≤ x` (`firsts` packed, `nb` buckets). -/
def pick (firsts nb x : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ → ℕ
    | 0, lo, _ => lo
    | f + 1, lo, hi =>
      if lo + 1 < hi then
        if getW firsts ((lo + hi) / 2) ≤ x then go f ((lo + hi) / 2) hi else go f lo ((lo + hi) / 2)
      else lo
  go 64 0 nb

/-! ### Codes of states -/

def encP : List ℕ → ℕ
  | [] => 0
  | p :: ps => p + 1024 * encP ps

def enc (s : St) : ℕ := s.2 + 4 * encP s.1

def decP : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 1024) :: decP f (n / 1024)

def dec (n : ℕ) : St := (decP 32 (n / 4), n % 4)

/-- Every state in `S` is the decoding of some code in `L`. -/
def Cov (L : KSet) (S : List St) : Prop := ∀ s ∈ S, ∃ c, Mem L c ∧ dec c = s

/-! ### Step and final checks -/

/-- Every successor at cell `i` of a state in bucket `(arr, n)` is in `L` (whose bucket starts are
`firsts`, `nb` buckets). -/
def stepOK (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (i : ℕ) (arr n : ℕ) (L : KSet) (firsts nb : ℕ) :
    Bool :=
  (List.range n).all fun k =>
    (stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 (dec (getW arr k))).all fun s' =>
      dec (enc s') == s' && memL L (pick firsts nb (enc s')) (enc s')

theorem cov_stage {a b : ℕ} {tm : List ((ℕ × ℕ) × ℕ)} {i : ℕ} {Lin Lout : KSet} {firsts nb : ℕ}
    {S : List St} (hS : Cov Lin S)
    (hstep : ∀ p ∈ Lin, stepOK a b tm i p.1 p.2 Lout firsts nb = true) :
    Cov Lout (stage a b tm S i) := by
  intro s' hs'
  unfold stage at hs'
  rw [mem_normS, List.mem_flatMap] at hs'
  obtain ⟨s, hs, hs'⟩ := hs'
  obtain ⟨c, ⟨p, hp, k, hk, hc⟩, rfl⟩ := hS s hs
  have h := hstep p hp
  unfold stepOK at h
  have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [hc] at h1
  have h2 := List.all_eq_true.mp h1 s' hs'
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨enc s', memL_sound h2.2, h2.1⟩

/-- Every state of bucket `(arr, n)` fails the outside test. -/
def finalOK (a b odd : ℕ) (F : FSpec) (arr n : ℕ) : Bool :=
  (List.range n).all fun k => !outsideOK a b odd F (dec (getW arr k))

theorem final_of_cov {a b odd : ℕ} {F : FSpec} {L : KSet} {S : List St} (hS : Cov L S)
    (hfin : ∀ p ∈ L, finalOK a b odd F p.1 p.2 = true) :
    ∀ s ∈ S, outsideOK a b odd F s = false := by
  intro s hs
  obtain ⟨c, ⟨p, hp, k, hk, hc⟩, rfl⟩ := hS s hs
  have h := List.all_eq_true.mp (hfin p hp) k (List.mem_range.mpr hk)
  rw [hc] at h
  simpa using h

/-- The start: the empty state has a code in `L0`. -/
theorem cov_init {L : KSet} (h : ∃ c, Mem L c ∧ dec c = ([], 0)) : Cov L [([], 0)] := by
  intro s hs
  rw [List.mem_singleton] at hs
  subst hs; exact h

theorem inside_succ (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) :
    (List.range (n + 1)).foldl (stage a b tm) [([], 0)] =
      stage a b tm ((List.range n).foldl (stage a b tm) [([], 0)]) n := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- From a covering of the final states to the certificate. -/
theorem certify_of_cov {a b odd : ℕ} {tm : List ((ℕ × ℕ) × ℕ)} {F : FSpec} {L : KSet}
    (hS : Cov L (inside a b tm)) (hfin : ∀ p ∈ L, finalOK a b odd F p.1 p.2 = true) :
    certify a b tm odd F = true := by
  unfold certify
  rw [List.all_eq_true]
  intro s hs
  simpa using final_of_cov hS hfin s hs

/-! ### Final checks through outside signatures

`outsideOK` depends on a state only through its signature: the number of outside ends, their
inside links, the end at F, the checkerboard sum and the done mask. A final bucket is checked by
looking each state's signature up in a sorted packed array of signatures, each of which is shown
once to fail the test (`sigsOK`). -/

/-- `outsideOK` from a signature. -/
def outsideSig (odd : ℕ) (m : ℕ) (links : List (Option ℕ)) (fx : Option ℕ) (par : Int) (dn : ℕ) :
    Bool :=
  if links.any (·.isNone) then false else
  let link : ℕ → ℕ := fun i => (links.getD i none).getD 0
  m != 0 && m % 2 == 0 && par == 2 * (odd : Int) &&
    (ncm m (List.range m)).any fun mt =>
      (match fx with | some i => mate mt i == m - 1 | none => true) && structOK m link mt dn

theorem outsideOK_sig (a b odd : ℕ) (F : FSpec) (s : St) :
    outsideOK a b odd F s = outsideSig odd (mOf a b F s) ((List.range (mOf a b F s)).map (linkOf a b F s))
      (fxOf a b F s) (parOf a b F s) s.2 := rfl

/-- Signature code: 5 bits each for `m`, `dn`, `fx + 1`, `par + 16`, then 5 bits per link
(`0` = none, `v + 1`). -/
def sigCode (m : ℕ) (links : List (Option ℕ)) (fx : Option ℕ) (par : Int) (dn : ℕ) : ℕ :=
  m + 32 * (dn + 32 * ((match fx with | none => 0 | some i => i + 1) +
    32 * ((par + 16).toNat + 32 * encP (links.map fun o => match o with | none => 0 | some v => v + 1))))

def decLinks : ℕ → ℕ → List (Option ℕ)
  | 0, _ => []
  | f + 1, n => (if n % 1024 = 0 then none else some (n % 1024 - 1)) :: decLinks f (n / 1024)

/-- Decode a signature code (the number of links is `m`). -/
def sigDec (c : ℕ) : ℕ × List (Option ℕ) × Option ℕ × Int × ℕ :=
  let m := c % 32
  let dn := (c / 32) % 32
  let fx := (c / 1024) % 32
  let par := ((c / 32768) % 32 : ℕ) - (16 : Int)
  (m, decLinks m (c / 1048576), (if fx = 0 then none else some (fx - 1)), par, dn)

def sigOf (a b : ℕ) (F : FSpec) (s : St) : ℕ × List (Option ℕ) × Option ℕ × Int × ℕ :=
  (mOf a b F s, (List.range (mOf a b F s)).map (linkOf a b F s), fxOf a b F s, parOf a b F s, s.2)

/-- Every signature in the packed sorted array `(sa, ns)` fails the outside test. -/
def sigsOK (odd : ℕ) (sa ns : ℕ) : Bool :=
  (List.range ns).all fun k =>
    let g := sigDec (getW sa k)
    !outsideSig odd g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2

/-- Every state of bucket `(arr, n)` has its signature in `(sa, ns)`. -/
def finalSigOK (a b : ℕ) (F : FSpec) (arr n sa ns : ℕ) : Bool :=
  (List.range n).all fun k =>
    let g := sigOf a b F (dec (getW arr k))
    let c := sigCode g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2
    sigDec c == g && bsearch sa c 64 0 ns

theorem final_of_sigs {a b odd : ℕ} {F : FSpec} {sa ns arr n : ℕ} (hs : sigsOK odd sa ns = true)
    (hf : finalSigOK a b F arr n sa ns = true) : finalOK a b odd F arr n = true := by
  unfold finalOK
  rw [List.all_eq_true]
  intro k hk
  have h := List.all_eq_true.mp hf k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hdec, hb⟩ := h
  obtain ⟨j, -, hj, hc⟩ := bsearch_sound _ _ _ hb
  have h2 := List.all_eq_true.mp hs j (List.mem_range.mpr hj)
  rw [hc, hdec] at h2
  rw [outsideOK_sig]
  simpa [sigOf] using h2

/-- Signatures `lo ≤ k < hi` of a packed array fail the outside test. -/
def sigsOKR (odd : ℕ) (sa lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun k =>
    let g := sigDec (getW sa (lo + k))
    !outsideSig odd g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2

theorem sigsOKR_spec {odd sa lo hi : ℕ} (h : sigsOKR odd sa lo hi = true) (j : ℕ) (h1 : lo ≤ j)
    (h2 : j < hi) :
    outsideSig odd (sigDec (getW sa j)).1 (sigDec (getW sa j)).2.1 (sigDec (getW sa j)).2.2.1
      (sigDec (getW sa j)).2.2.2.1 (sigDec (getW sa j)).2.2.2.2 = false := by
  have := List.all_eq_true.mp h (j - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (j - lo) = j by omega] at this
  simpa using this

theorem final_of_sigs' {a b odd : ℕ} {F : FSpec} {sa ns arr n : ℕ}
    (hs : ∀ j, j < ns → outsideSig odd (sigDec (getW sa j)).1 (sigDec (getW sa j)).2.1
      (sigDec (getW sa j)).2.2.1 (sigDec (getW sa j)).2.2.2.1 (sigDec (getW sa j)).2.2.2.2 = false)
    (hf : finalSigOK a b F arr n sa ns = true) : finalOK a b odd F arr n = true := by
  unfold finalOK
  rw [List.all_eq_true]
  intro k hk
  have h := List.all_eq_true.mp hf k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hdec, hb⟩ := h
  obtain ⟨j, -, hj, hc⟩ := bsearch_sound _ _ _ hb
  have h2 := hs j hj
  rw [hc, hdec] at h2
  rw [outsideOK_sig]
  simpa [sigOf] using h2

end ZZN.WinK
