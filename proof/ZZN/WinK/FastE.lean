/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.WinK.Engine

@[expose] public section

/-!
# Window-check helpers in the form the kernel evaluates fastest

Copies of `getW`, `decP`, `dec`, `encP`, `enc`, `bsearch`, `pick`, `memL` and `stepOK` that
recurse with `Nat.rec`/`List.rec` instead of compiled structural recursion, compare with
`Nat.beq`/`Nat.blt`/`Nat.ble` instead of `Decidable` instances, and call the `Nat` operations
directly. On a stage bucket the kernel checks `stepOKD` about 1.6 times faster than `stepOK`.
Each copy equals its original (`stepOKD_eq`). They are kernel-only (`noncomputable`).
-/

namespace ZZN.WinK

open ZZN ZZN.Win

def P192 : ℕ := 2 ^ 192

def getWD (arr k : ℕ) : ℕ := Nat.mod (Nat.shiftRight arr (Nat.mul 192 k)) P192

noncomputable def decPD (f : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih n => cond (Nat.beq n 0) [] (Nat.mod n 1024 :: ih (Nat.div n 1024))) f

noncomputable def decD (n : ℕ) : St := (decPD 32 (Nat.div n 4), Nat.mod n 4)

noncomputable def encPD (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun p _ ih => Nat.add p (Nat.mul 1024 ih)) l

noncomputable def encD (s : St) : ℕ := Nat.add s.2 (Nat.mul 4 (encPD s.1))

noncomputable def bsearchD (arr x f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih lo hi =>
      cond (Nat.blt lo hi)
        (let m := Nat.div (Nat.add lo hi) 2
         let v := getWD arr m
         cond (Nat.beq v x) true (cond (Nat.blt v x) (ih (Nat.add m 1) hi) (ih lo m)))
        false) f

noncomputable def pickGoD (firsts x f : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun lo _ => lo)
    (fun _ ih lo hi =>
      cond (Nat.blt (Nat.add lo 1) hi)
        (let m := Nat.div (Nat.add lo hi) 2
         cond (Nat.ble (getWD firsts m) x) (ih m hi) (ih lo m))
        lo) f

noncomputable def pickD (firsts nb x : ℕ) : ℕ := pickGoD firsts x 64 0 nb

noncomputable def memLD (L : KSet) (j x : ℕ) : Bool :=
  match L[j]? with
  | some p => bsearchD p.1 x 64 0 p.2
  | none => false

noncomputable def stepOKD (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (i : ℕ) (arr n : ℕ) (L : KSet)
    (firsts nb : ℕ) : Bool :=
  (List.range n).all fun k =>
    (stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 (decD (getWD arr k))).all fun s' =>
      decD (encD s') == s' && memLD L (pickD firsts nb (encD s')) (encD s')

/-! ### Each copy equals its original -/

private theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl
private theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
private theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl

private theorem beq_false {a b : ℕ} (h : ¬a = b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem getWD_eq (arr k : ℕ) : getWD arr k = getW arr k := by
  simp only [getWD, getW, P192, W]; rfl

theorem decPD_eq : ∀ (f n : ℕ), decPD f n = decP f n
  | 0, _ => rfl
  | f + 1, n => by
    show cond (Nat.beq n 0) [] (Nat.mod n 1024 :: decPD f (Nat.div n 1024)) = decP (f + 1) n
    rw [decPD_eq f]
    by_cases h : n = 0
    · simp [h, decP]
    · have hb : Nat.beq n 0 = false := beq_false h
      simp [decP, h, hb, ndiv, nmod]

theorem decD_eq (n : ℕ) : decD n = dec n := by
  simp only [decD, dec, decPD_eq, ndiv, nmod]

theorem encPD_eq : ∀ l : List ℕ, encPD l = encP l
  | [] => rfl
  | p :: ps => by
    show Nat.add p (Nat.mul 1024 (encPD ps)) = encP (p :: ps)
    rw [encPD_eq ps]; simp [encP]

theorem encD_eq (s : St) : encD s = enc s := by
  simp only [encD, enc, encPD_eq, nadd, nmul]

theorem bsearchD_eq (arr x : ℕ) : ∀ (f lo hi : ℕ), bsearchD arr x f lo hi = bsearch arr x f lo hi
  | 0, _, _ => rfl
  | f + 1, lo, hi => by
    show cond (Nat.blt lo hi)
        (cond (Nat.beq (getWD arr (Nat.div (Nat.add lo hi) 2)) x) true
          (cond (Nat.blt (getWD arr (Nat.div (Nat.add lo hi) 2)) x)
            (bsearchD arr x f (Nat.add (Nat.div (Nat.add lo hi) 2) 1) hi)
            (bsearchD arr x f lo (Nat.div (Nat.add lo hi) 2)))) false = bsearch arr x (f + 1) lo hi
    simp only [bsearchD_eq arr x f, getWD_eq, ndiv, nadd]
    conv_rhs => rw [bsearch]
    by_cases h1 : lo < hi
    · by_cases h2 : getW arr ((lo + hi) / 2) = x
      · simp [h1, h2]
      · by_cases h3 : getW arr ((lo + hi) / 2) < x
        · have hb : Nat.beq (getW arr ((lo + hi) / 2)) x = false := beq_false h2
          simp [h1, h2, h3, hb]
        · have hb : Nat.beq (getW arr ((lo + hi) / 2)) x = false := beq_false h2
          simp [h1, h2, h3, hb]
    · simp [h1]

theorem pickGoD_eq (firsts x : ℕ) : ∀ (f lo hi : ℕ), pickGoD firsts x f lo hi = pick.go firsts x f lo hi
  | 0, _, _ => rfl
  | f + 1, lo, hi => by
    show cond (Nat.blt (Nat.add lo 1) hi)
        (cond (Nat.ble (getWD firsts (Nat.div (Nat.add lo hi) 2)) x)
          (pickGoD firsts x f (Nat.div (Nat.add lo hi) 2) hi)
          (pickGoD firsts x f lo (Nat.div (Nat.add lo hi) 2))) lo = pick.go firsts x (f + 1) lo hi
    simp only [pickGoD_eq firsts x f, getWD_eq, ndiv, nadd]
    conv_rhs => rw [pick.go]
    by_cases h1 : lo + 1 < hi
    · by_cases h2 : getW firsts ((lo + hi) / 2) ≤ x
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]

theorem pickD_eq (firsts nb x : ℕ) : pickD firsts nb x = pick firsts nb x := by
  simp only [pickD, pick, pickGoD_eq]

theorem memLD_eq (L : KSet) (j x : ℕ) : memLD L j x = memL L j x := by
  unfold memLD memL
  cases L[j]? <;> simp [bsearchD_eq]

theorem stepOKD_eq (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (i arr n : ℕ) (L : KSet) (firsts nb : ℕ) :
    stepOKD a b tm i arr n L firsts nb = stepOK a b tm i arr n L firsts nb := by
  simp only [stepOKD, stepOK, decD_eq, getWD_eq, encD_eq, memLD_eq, pickD_eq]

end ZZN.WinK
