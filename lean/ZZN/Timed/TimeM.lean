-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card

/-!
# Step counting: the monad and the counted list operations

`TimeM α` pairs a result with a step count, and `bind` adds the counts. The counted algorithm
(`ZZN/Timed/*.lean`) is written with the operations below and with constant-time functions on
numbers, Booleans, cells, endpoint records, frames and options. Nothing else: the script
`checks/timed_lint.py` rejects any other list operation inside a counted definition.

**The trusted part is this list of costs.** Each is one step per element touched, with a
quadratic charge for removing duplicates.

| operation | cost |
|---|---|
| `tick n` | `n` |
| `lmapT f l`, `lfilterT p l`, `lallT p l`, `lanyT p l`, `lfindT p l`, `lfilterMapT f l` | `Σ_{x ∈ l} (cost of f x + 1)` |
| `lflatMapT f l` | `Σ_{x ∈ l} (cost of f x + |f x| + 1)` |
| `lfoldlT f b l` | `Σ (cost of each step + 1)` |
| `lengthT`, `lcontainsT`, `leraseT`, `lappendT l m`, `lreverseT`, `lsumT`, `lzipIdxT`, `lzipT l m`, `lfindIdxT`, `lmodifyT`, `lgetT` | `|l| + 1` |
| `rangeT n` | `n + 1` |
| `ldedupT l` | `|l|² + 1` |
| `lnodupT l` (test for repeats) | `|l|² + 1` |
| `infix2T a b l` (are `a, b` consecutive in `l`) | `|l| + 1` |
| `lgetLastT l` | `|l| + 1` |
| `fmemT x s`, `feraseT s x`, `ffilterT p s` (sets of numbers, `p` constant time) | `|s| + 1` |
| `frangeFilterT n p` | `Σ_{y < n} (cost of p y + 1)` |
-/

namespace ZZN.T

structure TimeM (α : Type) where
  ret : α
  time : ℕ

instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.ret; ⟨r.ret, m.time + r.time⟩

variable {α β : Type}

@[simp] lemma ret_pure (a : α) : (pure a : TimeM α).ret = a := rfl
@[simp] lemma time_pure (a : α) : (pure a : TimeM α).time = 0 := rfl
@[simp] lemma ret_bind (m : TimeM α) (f : α → TimeM β) : (m >>= f).ret = (f m.ret).ret := rfl
@[simp] lemma time_bind (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl

/-! ## The counted operations -/

def tick (n : ℕ) : TimeM Unit := ⟨(), n⟩

def lmapT (f : α → TimeM β) (l : List α) : TimeM (List β) :=
  ⟨l.map (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩

def lfilterT (p : α → TimeM Bool) (l : List α) : TimeM (List α) :=
  ⟨l.filter (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lallT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.all (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lanyT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.any (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lfindT (p : α → TimeM Bool) (l : List α) : TimeM (Option α) :=
  ⟨l.find? (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lfilterMapT (f : α → TimeM (Option β)) (l : List α) : TimeM (List β) :=
  ⟨l.filterMap (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩

def lflatMapT (f : α → TimeM (List β)) (l : List α) : TimeM (List β) :=
  ⟨l.flatMap (fun x => (f x).ret), (l.map (fun x => let r := f x; r.time + r.ret.length + 1)).sum⟩

def lfoldlT (f : β → α → TimeM β) : β → List α → TimeM β
  | b, [] => ⟨b, 0⟩
  | b, x :: l => let r := f b x; let s := lfoldlT f r.ret l; ⟨s.ret, r.time + 1 + s.time⟩

def lengthT (l : List α) : TimeM ℕ := ⟨l.length, l.length + 1⟩

def lcontainsT [BEq α] (l : List α) (x : α) : TimeM Bool := ⟨l.contains x, l.length + 1⟩

def leraseT [BEq α] (l : List α) (x : α) : TimeM (List α) := ⟨l.erase x, l.length + 1⟩

def lappendT (l m : List α) : TimeM (List α) := ⟨l ++ m, l.length + 1⟩

def lreverseT (l : List α) : TimeM (List α) := ⟨l.reverse, l.length + 1⟩

def lsumT (l : List ℤ) : TimeM ℤ := ⟨l.sum, l.length + 1⟩

def lzipIdxT (l : List α) : TimeM (List (α × ℕ)) := ⟨l.zipIdx, l.length + 1⟩

def lzipT (l : List α) (m : List β) : TimeM (List (α × β)) := ⟨l.zip m, l.length + 1⟩

def lfindIdxT (p : α → Bool) (l : List α) : TimeM (Option ℕ) := ⟨l.findIdx? p, l.length + 1⟩

def lmodifyT (l : List α) (i : ℕ) (f : α → α) : TimeM (List α) := ⟨l.modify i f, l.length + 1⟩

def lgetT [Inhabited α] (l : List α) (i : ℕ) : TimeM α := ⟨l[i]!, l.length + 1⟩

def rangeT (n : ℕ) : TimeM (List ℕ) := ⟨List.range n, n + 1⟩

def ldedupT [DecidableEq α] (l : List α) : TimeM (List α) := ⟨l.dedup, l.length ^ 2 + 1⟩

def lnodupT [DecidableEq α] (l : List α) : TimeM Bool := ⟨decide l.Nodup, l.length ^ 2 + 1⟩

def infix2T [DecidableEq α] (a b : α) (l : List α) : TimeM Bool :=
  ⟨decide ([a, b] <:+: l), l.length + 1⟩

def lgetLastT (l : List α) : TimeM (Option α) := ⟨l.getLast?, l.length + 1⟩

def fmemT (x : ℕ) (s : Finset ℕ) : TimeM Bool := ⟨decide (x ∈ s), s.card + 1⟩

def feraseT (s : Finset ℕ) (x : ℕ) : TimeM (Finset ℕ) := ⟨s.erase x, s.card + 1⟩

def ffilterT (p : ℕ → Bool) (s : Finset ℕ) : TimeM (Finset ℕ) := ⟨s.filter (fun x => p x = true), s.card + 1⟩

def frangeFilterT (n : ℕ) (p : ℕ → TimeM Bool) : TimeM (Finset ℕ) :=
  ⟨(Finset.range n).filter (fun y => (p y).ret = true), ((List.range n).map (fun y => (p y).time + 1)).sum⟩

/-! ## Simp lemmas -/

@[simp] lemma ret_tick (n : ℕ) : (tick n).ret = () := rfl
@[simp] lemma time_tick (n : ℕ) : (tick n).time = n := rfl

@[simp] lemma ret_lfoldlT (f : β → α → TimeM β) (b : β) (l : List α) :
    (lfoldlT f b l).ret = l.foldl (fun b x => (f b x).ret) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => simp [lfoldlT, ih]

lemma lsum_le {γ : Type} (l : List γ) (g : γ → ℕ) (c : ℕ) (h : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.succ_mul]; omega

lemma lmapT_time_le (f : α → TimeM β) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (f x).time ≤ c) :
    (lmapT f l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lfilterT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lfilterT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lallT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lallT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lanyT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lanyT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lfindT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lfindT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lfilterMapT_time_le (f : α → TimeM (Option β)) (l : List α) (c : ℕ)
    (h : ∀ x ∈ l, (f x).time ≤ c) : (lfilterMapT f l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lflatMapT_time_le (f : α → TimeM (List β)) (l : List α) (c d : ℕ)
    (h : ∀ x ∈ l, (f x).time ≤ c) (hd : ∀ x ∈ l, (f x).ret.length ≤ d) :
    (lflatMapT f l).time ≤ l.length * (c + d + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; have := hd x hx; dsimp only; omega)

end ZZN.T
