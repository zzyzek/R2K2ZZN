-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Catalogue

/-!
# Window certificates: the computation

A port of the window-certificate program used during development, written to be evaluated by the
kernel and reasoned about.

Window `W` = rows `0 … a−1`, columns `0 … b−1` at the top-left corner. Cells are processed in
row-major order. A partial covering is abstracted to its **pieces**: maximal runs of processed
cells along a solution path, each with two **ends**, coded as naturals:
- `c` (`c < b`): a plug down from column `c` into the next row;
- `b`: a plug right, into the next cell of the row;
- `b + 1 + s`: exit slot `s` (`s < a`: right of row `s`; `s = a + j`: below column `b − 1 − j`);
- `a + 2b + 1 + col`: an endpoint of colour `col`.
A piece is the code `32 x + y` of its ends `x ≤ y` (all ends are below 32 for `a, b ≤ 8`).
A state is the sorted list of piece codes and a bitmask of the colours whose path is complete.
-/

namespace ZZN.Win

abbrev St := List ℕ × ℕ

def mkP (x y : ℕ) : ℕ := if x ≤ y then 32 * x + y else 32 * y + x
def lo (p : ℕ) : ℕ := p / 32
def hi (p : ℕ) : ℕ := p % 32
def hasEnd (e p : ℕ) : Bool := lo p == e || hi p == e
def other (e p : ℕ) : ℕ := if lo p == e then hi p else lo p

def termE (a b col : ℕ) : ℕ := a + 2 * b + 1 + col
def isTerm (a b e : ℕ) : Bool := decide (a + 2 * b + 1 ≤ e)
def colE (a b e : ℕ) : ℕ := e - (a + 2 * b + 1)
def exitE (b s : ℕ) : ℕ := b + 1 + s
def isExit (a b e : ℕ) : Bool := decide (b + 1 ≤ e) && decide (e < a + 2 * b + 1)

def insSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insSorted x l

/-- Close a piece with ends `x, y`: a complete path (two endpoints) marks its colour done. -/
def closeP (a b : ℕ) (x y : ℕ) (rest : List ℕ) (dn : ℕ) : Option St :=
  if isTerm a b x && isTerm a b y then
    if colE a b x != colE a b y then none
    else if (dn / 2 ^ colE a b x) % 2 == 1 then none
    else some (rest, dn + 2 ^ colE a b x)
  else some (insSorted (mkP x y) rest, dn)

/-- Process cell `(r, c)`, an endpoint of colour `e` or not. -/
def stepCell (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) : List St :=
  let ps := s.1
  let pu := if r = 0 then none else ps.find? (hasEnd c)
  let pl := if c = 0 then none else ps.find? (hasEnd b)
  let down := if r + 1 < a then c else exitE b (a + (b - 1 - c))
  let right := if c + 1 < b then b else exitE b r
  let nin := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
  let deg := if e.isSome then 1 else 2
  if deg < nin then [] else
  if pu.isSome && pu == pl then [] else
  let rest := if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0)
    else ps.erase (pu.getD 0)) else (if pl.isSome then ps.erase (pl.getD 0) else ps)
  let ins := (pu.map (other c)).toList ++ (pl.map (other b)).toList ++ (e.map (termE a b)).toList
  let opts : List (List ℕ) := match deg - nin with
    | 0 => [[]]
    | 1 => [[down], [right]]
    | _ => [[down, right]]
  opts.filterMap fun outs =>
    match ins ++ outs with
    | [x, y] => closeP a b x y rest s.2
    | _ => none

/-- Lexicographic order on states, for sorting. -/
def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: l, y :: m => x < y || (x == y && ltL l m)

def ltS (s t : St) : Bool := s.2 < t.2 || (s.2 == t.2 && ltL s.1 t.1)

def mergeS : ℕ → List St → List St → List St
  | 0, l, m => l ++ m
  | _ + 1, [], m => m
  | _ + 1, l, [] => l
  | f + 1, x :: l, y :: m => if ltS y x then y :: mergeS f (x :: l) m else x :: mergeS f l (y :: m)

def splitS : List St → List St × List St
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: l => let p := splitS l; (x :: p.1, y :: p.2)

/-- Merge sort with fuel (always a permutation; sorted when the fuel suffices). -/
def msortS : ℕ → List St → List St
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | f + 1, l => let p := splitS l; mergeS (l.length) (msortS f p.1) (msortS f p.2)

def dedupAdj : List St → List St
  | x :: y :: l => if x == y then dedupAdj (y :: l) else x :: dedupAdj (y :: l)
  | l => l

def normS (l : List St) : List St := dedupAdj (msortS 64 l)

def termAt (tm : List ((ℕ × ℕ) × ℕ)) (x : ℕ × ℕ) : Option ℕ := (tm.find? (·.1 == x)).map (·.2)

/-- Cell `i` in row-major order. -/
def cell (b i : ℕ) : ℕ × ℕ := (i / b, i % b)

/-- One DP stage: process cell `i`. -/
def stage (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) : List St :=
  normS (S.flatMap (stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2))

/-- All final states: the inside signatures of the window. -/
def inside (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List St :=
  (List.range (a * b)).foldl (stage a b tm) [([], 0)]

/-! ### The outside test -/

def sgn (x : ℕ × ℕ) : Int := if (x.1 + x.2) % 2 = 0 then 1 else -1

/-- The outside cell an exit slot leads to. -/
def exitCell (a b s : ℕ) : ℕ × ℕ := if s < a then (s, b) else (a, b - 1 - (s - a))

/-- Non-crossing perfect matchings of the list `l` (points in cyclic order). -/
def ncm : ℕ → List ℕ → List (List (ℕ × ℕ))
  | _, [] => [[]]
  | 0, _ :: _ => []
  | f + 1, x :: l => (List.range l.length).flatMap fun j =>
      if j % 2 = 0 then
        (ncm f (l.take j)).flatMap fun mA => (ncm f (l.drop (j + 1))).map fun mB =>
          (x, l.getD j 0) :: (mA ++ mB)
      else []

/-- The partner of node `i` in matching `mt`. -/
def mate (mt : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  match mt.find? (fun pr => pr.1 == i || pr.2 == i) with
  | some pr => if pr.1 == i then pr.2 else pr.1
  | none => i

/-- Walk from terminal node `t`: out along the matching, then in along the inside pieces, until a
terminal node. `link i` is `m + col` for a terminal node, else its inside partner. Returns the last
node and the nodes passed. -/
def walk (m : ℕ) (link : ℕ → ℕ) (mt : List (ℕ × ℕ)) : ℕ → ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | f + 1, cur =>
    let n := mate mt cur
    if m ≤ link n then some (n, [n])
    else (walk m link mt f (link n)).map fun r => (r.1, n :: link n :: r.2)

/-- The structure test for one matching: a colour completed inside the window has no terminal
node; otherwise it has exactly two, and the walk from the first ends at the second. Every node is
reached. (Equivalent to the Python test: every terminal's walk ends at another terminal of its
colour, every node is reached, and each colour has exactly one path.) -/
def visC (m : ℕ) (link : ℕ → ℕ) (mt : List (ℕ × ℕ)) (c : ℕ) : Option (List ℕ) :=
  match (List.range m).filter (fun i => link i == m + c) with
  | [t1, t2] => match walk m link mt (m + 1) t1 with
    | some (e, ps) => if e == t2 then some (t1 :: ps) else none
    | none => none
  | [] => some []
  | _ => none

def structOK (m : ℕ) (link : ℕ → ℕ) (mt : List (ℕ × ℕ)) (dn : ℕ) : Bool :=
  match visC m link mt 0, visC m link mt 1 with
  | some v0, some v1 =>
    [0, 1].all (fun c => ((dn / 2 ^ c) % 2 == 1) == ((List.range m).filter (fun i => link i == m + c)).isEmpty) &&
      (List.range m).all fun i => v0.contains i || v1.contains i
  | _, _ => false

/-- The F data: its colour, its checkerboard sign, and the exit slot whose cell it is (if any). -/
abbrev FSpec := Option (ℕ × Int × Option ℕ)

/-- The exit slots in use. -/
def usedOf (a b : ℕ) (s : St) : List ℕ := (List.range (a + b)).filter fun sl => s.1.any (hasEnd (exitE b sl))

/-- The number of outside ends: the used exits, and F. -/
def mOf (a b : ℕ) (F : FSpec) (s : St) : ℕ := (usedOf a b s).length + (if F.isSome then 1 else 0)

/-- The inside link of outside end `i`: its partner end, or `m + colour` for a terminal. -/
def linkOf (a b : ℕ) (F : FSpec) (s : St) (i : ℕ) : Option ℕ :=
  if i < (usedOf a b s).length then
    match s.1.find? (hasEnd (exitE b ((usedOf a b s).getD i 0))) with
    | none => none
    | some pc =>
      if isExit a b (other (exitE b ((usedOf a b s).getD i 0)) pc) then
        some ((usedOf a b s).idxOf (other (exitE b ((usedOf a b s).getD i 0)) pc - (b + 1)))
      else if isTerm a b (other (exitE b ((usedOf a b s).getD i 0)) pc) then
        some (mOf a b F s + colE a b (other (exitE b ((usedOf a b s).getD i 0)) pc))
      else none
  else match F with | some (fc, _, _) => some (mOf a b F s + fc) | none => none

/-- The outside end whose exit cell is F, if it is in use. -/
def fxOf (a b : ℕ) (F : FSpec) (s : St) : Option ℕ :=
  match F with
  | some (_, _, some fsl) => if (usedOf a b s).contains fsl then some ((usedOf a b s).idxOf fsl) else none
  | _ => none

/-- The checkerboard sum of the outside ends. -/
def parOf (a b : ℕ) (F : FSpec) (s : St) : Int :=
  ((usedOf a b s).map fun sl => sgn (exitCell a b sl)).sum + (match F with | some (_, fs, _) => fs | none => 0)

/-- **The outside test** for a final state. -/
def outsideOK (a b odd : ℕ) (F : FSpec) (s : St) : Bool :=
  let m := mOf a b F s
  let links := (List.range m).map (linkOf a b F s)
  if links.any (·.isNone) then false else
  let link : ℕ → ℕ := fun i => (links.getD i none).getD 0
  m != 0 && m % 2 == 0 && parOf a b F s == 2 * (odd : Int) &&
    (ncm m (List.range m)).any fun mt =>
      (match fxOf a b F s with | some i => mate mt i == m - 1 | none => true) && structOK m link mt s.2

/-- The certificate: no final state of the window passes the outside test. -/
def certify (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (odd : ℕ) (F : FSpec) : Bool :=
  (inside a b tm).all fun s => !outsideOK a b odd F s

end ZZN.Win
