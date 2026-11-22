/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Lean
import ZZN.Look.Leaf

/-!
# The library's certificate lookup against the Lean definitions

Two modes, both run from a built `proof/` directory by `lib/tests/look_lean.py`:

    lake env lean --run <path>/LookEval.lean cases cases.txt table.txt
    lake env lean --run <path>/LookEval.lean data out.txt

**cases**: reads the cases written by `look_lean.py` and evaluates the Lean definitions on them;
prints one line per case whose Lean value differs from the library's, and a summary. `table.txt`
is the exported table (`lib/data/look.json.gz`) in text form: `T id tree` per template and
`D w h x0 x1 x2 x3 ; id sym … ; lane n0 code0 n1 code1 …` per slice, in table order. From it a
table `tab` is built (chain and firing lanes empty, which `lookJ` does not read), and `look`
cases evaluate `lookJ tab` itself. Case lines (tab-separated fields, cells `x,y`):

- `tpl T I c p q`: `tcheck T I = c` and `tsol T I = (p, q)`;
- `sym I k J`: `(symOf k).apply I = J` (`Sym.apply`);
- `canon I k key`: `argminS (fun σ => key2 (σ.apply I)) (Gbox I.w I.h) = symOf k`, `key2 I = key`;
- `unsym k J p q p2 q2`: `unSym (symOf k) J (p, q) = (p2, q2)`;
- `dec n code p`: `decPath n code = p`;
- `solf I p q b`: `solF I p q = b`;
- `ips w h sx sy tx ty a p`: `accB w h s t = a` and `ipsP (w + h) w h s t = p`;
- `entry w h i I p q` (or `none`): `entryP I d = some (p, q)` for slice `i` of box `w × h`;
- `look I p q` (or `none`): `lookJ tab I`.

`symOf k` is the symmetry with bits `32 tr + 16 rx + 8 ry + 4 r0 + 2 r1 + sw`. A tree is in prefix
form: `L` a leaf, `C vert a o n k₁ … kₙ left right` a cut with kinds `S s`, `X s a o`,
`E s a o a₂ o₂`.

**data**: imports `ZZN.Look.Table` into a fresh environment and prints, from the elaborated
definitions (the `Expr` values of `BoxKGen.tN`, of `ZZN.LookGen.N{w}x{h}.tab` and of its slices
`BoxKGen.N{w}x{h}.dK`), the templates and the table in the text form above, with the slice index
after `w h`; and the stored prime paths (`GridHam.primeTable`, evaluated) as
`P w h sx sy tx ty x0 y0 x1 y1 …`. `look_lean.py` compares this with the export.
-/

open Lean ZZN ZZN.Cut ZZN.BoxK ZZN.Look GridHam

/-! ### Parsing the library's data -/

def toks (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def natsOf (s : String) : List Nat := (toks s).filterMap String.toNat?

def cellsOf (s : String) : List Coord :=
  (toks s).filterMap fun t =>
    match t.splitOn "," with
    | [a, b] => some (a.toNat!, b.toNat!)
    | _ => none

def instOf (s : String) : Option Inst :=
  match natsOf s with
  | [w, h, a, b, c, d, e, f, g, i] => some ⟨w, h, (a, b), (c, d), (e, f), (g, i)⟩
  | _ => none

def instEq (I J : Inst) : Bool :=
  I.w == J.w && I.h == J.h && I.s0 == J.s0 && I.t0 == J.t0 && I.s1 == J.s1 && I.t1 == J.t1

def symOf (k : Nat) : Sym :=
  ⟨k.testBit 5, k.testBit 4, k.testBit 3, k.testBit 2, k.testBit 1, k.testBit 0⟩

def symNat (σ : Sym) : Nat :=
  [σ.tr, σ.rx, σ.ry, σ.r0, σ.r1, σ.sw].foldl (fun a b => 2 * a + if b then 1 else 0) 0

def posOf (a o : String) : TPos := (a.toNat!, (o.toInt?).getD 0)

partial def parseKinds : Nat → List String → Option (List (Kind TPos) × List String)
  | 0, r => some ([], r)
  | n + 1, "S" :: s :: r => do
    let (ks, r) ← parseKinds n r
    pure (Kind.stay (s == "1") :: ks, r)
  | n + 1, "X" :: s :: a :: o :: r => do
    let (ks, r) ← parseKinds n r
    pure (Kind.cross (s == "1") (posOf a o) :: ks, r)
  | n + 1, "E" :: s :: a :: o :: a2 :: o2 :: r => do
    let (ks, r) ← parseKinds n r
    pure (Kind.exc (s == "1") (posOf a o) (posOf a2 o2) :: ks, r)
  | _, _ => none

partial def parseTree : List String → Option (CTree TPos × List String)
  | "L" :: r => some (CTree.leaf, r)
  | "C" :: v :: a :: o :: n :: r => do
    let (ks, r) ← parseKinds n.toNat! r
    let (l, r) ← parseTree r
    let (rt, r) ← parseTree r
    pure (CTree.cut (v == "1") (posOf a o) ks l rt, r)
  | _ => none

def treeOf (s : String) : Option (CTree TPos) :=
  match parseTree (toks s) with
  | some (t, []) => some t
  | _ => none

/-- Box index of `w × h`, `11 ≤ w ≤ h ≤ 16`. -/
def boxIx (w h : Nat) : Nat := (w - 11) * 6 + (h - 11)

/-- The table file: templates by id, then slices per box in order. -/
def readTable (file : String) : IO (Array (List CData)) := do
  let lines := (← IO.FS.readFile file).splitOn "\n"
  let mut tpl : Std.HashMap Nat (CTree TPos) := {}
  let mut boxes : Array (List CData) := Array.replicate 36 []
  for line in lines do
    match line.splitOn " " with
    | "T" :: i :: rest =>
      match treeOf (" ".intercalate rest) with
      | some t => tpl := tpl.insert i.toNat! t
      | none => throw (IO.userError s!"bad template {i}")
    | "D" :: _ =>
      match line.splitOn ";" with
      | [hd, ps, ss] =>
        match natsOf hd with
        | [w, h, x0, x1, x2, x3] =>
          let pn := natsOf ps
          let pairs := (List.range (pn.length / 2)).map fun j =>
            ((tpl.get? pn[2 * j]!).getD CTree.leaf, symOf pn[2 * j + 1]!)
          let sn := natsOf ss
          let sols := (List.range (sn.length / 5)).map fun j =>
            (sn[5 * j]!, sn[5 * j + 1]!, sn[5 * j + 2]!, sn[5 * j + 3]!, sn[5 * j + 4]!)
          let d : CData := (![x0, x1, x2, x3], [], pairs, [], sols)
          boxes := boxes.modify (boxIx w h) (d :: ·)
        | _ => throw (IO.userError "bad slice header")
      | _ => throw (IO.userError "bad slice line")
    | _ => pure ()
  return boxes.map List.reverse

/-- `tabAll`'s guard over the parsed boxes. -/
def tabOf (boxes : Array (List CData)) (w h : ℕ) : List CData :=
  if 11 ≤ w ∧ w ≤ h ∧ h ≤ 16 then boxes.getD (boxIx w h) [] else []

def solEq (s : Option (List Coord × List Coord)) (fs : List String) : Bool :=
  match s, fs with
  | none, ["none"] => true
  | some (p, q), [ps, qs] => p == cellsOf ps && q == cellsOf qs
  | _, _ => false

def showSol : Option (List Coord × List Coord) → String
  | none => "none"
  | some (p, q) => s!"{p.length} + {q.length} cells"

/-- `none` if the case agrees, else what differs. -/
def checkLine (boxes : Array (List CData)) (fs : List String) : Option String :=
  match fs with
  | ["tpl", t, i, c, p, q] =>
    match treeOf t, instOf i with
    | some T, some I =>
      if tcheck T I != (c == "1") then some s!"tcheck = {tcheck T I}"
      else if (tsol T I).1 != cellsOf p then some "tsol differs on the first path"
      else if (tsol T I).2 != cellsOf q then some "tsol differs on the second path"
      else none
    | _, _ => some "bad tpl line"
  | ["sym", i, k, j] =>
    match instOf i, instOf j with
    | some I, some J => if instEq ((symOf k.toNat!).apply I) J then none else some "Sym.apply differs"
    | _, _ => some "bad sym line"
  | ["canon", i, k, key] =>
    match instOf i with
    | some I =>
      let σ := argminS (fun σ => key2 (σ.apply I)) (Gbox I.w I.h)
      if symNat σ != k.toNat! then some s!"argminS = {symNat σ}"
      else if key2 I != key.toNat! then some s!"key2 = {key2 I}"
      else none
    | none => some "bad canon line"
  | ["unsym", k, j, p, q, p2, q2] =>
    match instOf j with
    | some J =>
      let r := unSym (symOf k.toNat!) J (cellsOf p, cellsOf q)
      if r.1 == cellsOf p2 && r.2 == cellsOf q2 then none else some "unSym differs"
    | none => some "bad unsym line"
  | ["dec", n, code, p] =>
    if decPath n.toNat! code.toNat! == cellsOf p then none else some "decPath differs"
  | ["solf", i, p, q, b] =>
    match instOf i with
    | some I => if solF I (cellsOf p) (cellsOf q) == (b == "1") then none else some "solF differs"
    | none => some "bad solf line"
  | ["ips", wh, a, p] =>
    match natsOf wh with
    | [w, h, sx, sy, tx, ty] =>
      if Lane.accB w h (sx, sy) (tx, ty) != (a == "1") then some "accB differs"
      else if ipsP (w + h) w h (sx, sy) (tx, ty) != cellsOf p then some "ipsP differs"
      else none
    | _ => some "bad ips line"
  | "entry" :: wh :: k :: i :: rest =>
    match natsOf wh, instOf i with
    | [w, h], some I =>
      match (tabOf boxes w h)[k.toNat!]? with
      | some d =>
        let r := entryP I d
        if solEq r rest then none else some s!"entryP = {showSol r}"
      | none => some "no such slice"
    | _, _ => some "bad entry line"
  | "look" :: i :: rest =>
    match instOf i with
    | some I =>
      let r := lookJ (tabOf boxes) I
      if solEq r rest then none else some s!"lookJ = {showSol r}"
    | none => some "bad look line"
  | _ => some "bad line"

def runCases (file table : String) : IO UInt32 := do
  let boxes ← readTable table
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.filter (· ≠ "")
  let mut counts : Std.HashMap String Nat := {}
  let mut bad := 0
  for (line, i) in lines.zip (List.range lines.length) do
    let fs := line.splitOn "\t"
    let kind := fs.headD ""
    counts := counts.insert kind (counts.getD kind 0 + 1)
    match checkLine boxes fs with
    | none => pure ()
    | some why =>
      bad := bad + 1
      IO.println s!"FAIL line {i + 1} ({kind}): {why}"
  let kinds := ["tpl", "sym", "canon", "unsym", "dec", "solf", "ips", "entry", "look"]
  IO.println s!"cases: {", ".intercalate (kinds.map fun k => s!"{k} {counts.getD k 0}")}; failed {bad}"
  return (if bad == 0 then 0 else 1)

/-! ### Reading the elaborated definitions -/

/-- Drop metadata and top-level `let`/`have` bindings (long list literals elaborate to a chain of
`have`s), by substituting their values. -/
partial def norm (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ v b _ => norm (b.instantiate1 v)
  | e => e

partial def natE (e : Expr) : Except String Nat :=
  match norm e with
  | .lit (.natVal n) => pure n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then natE (e.getArg! 1)
    else throw s!"not a Nat literal: {e}"

partial def intE (e : Expr) : Except String Int := do
  let e := norm e
  if e.isAppOfArity ``Neg.neg 3 then return - (← intE (e.getArg! 2))
  else if e.isAppOfArity ``OfNat.ofNat 3 then return Int.ofNat (← natE (e.getArg! 1))
  else if e.isAppOfArity ``Int.ofNat 1 then return Int.ofNat (← natE (e.getArg! 0))
  else if e.isAppOfArity ``Int.negSucc 1 then return Int.negSucc (← natE (e.getArg! 0))
  else throw s!"not an Int literal: {e}"

def boolE (e : Expr) : Except String String :=
  if (norm e).isConstOf ``Bool.true then pure "1"
  else if (norm e).isConstOf ``Bool.false then pure "0"
  else throw s!"not a Bool: {e}"

partial def listE (e : Expr) (acc : Array Expr := #[]) : Except String (Array Expr) :=
  let e := norm e
  if e.isAppOfArity ``List.cons 3 then listE (e.getArg! 2) (acc.push (e.getArg! 1))
  else if e.isAppOfArity ``List.nil 1 then pure acc
  else throw s!"not a list: {e}"

def pairE (e : Expr) : Except String (Expr × Expr) :=
  let e := norm e
  if e.isAppOfArity ``Prod.mk 4 then pure (e.getArg! 2, e.getArg! 3)
  else throw s!"not a pair: {e}"

def posE (e : Expr) : Except String String := do
  let (a, o) ← pairE e
  return s!"{← natE a} {← intE o}"

def kindE (e : Expr) : Except String String := do
  let e := norm e
  if e.isAppOfArity ``ZZN.Cut.Kind.stay 2 then return s!"S {← boolE (e.getArg! 1)}"
  else if e.isAppOfArity ``ZZN.Cut.Kind.cross 3 then return s!"X {← boolE (e.getArg! 1)} {← posE (e.getArg! 2)}"
  else if e.isAppOfArity ``ZZN.Cut.Kind.exc 4 then
    return s!"E {← boolE (e.getArg! 1)} {← posE (e.getArg! 2)} {← posE (e.getArg! 3)}"
  else throw s!"not a Kind: {e}"

partial def treeE (e : Expr) : Except String String := do
  let e := norm e
  if e.isAppOfArity ``ZZN.Cut.CTree.leaf 1 then return "L"
  else if e.isAppOfArity ``ZZN.Cut.CTree.cut 6 then
    let ks ← listE (e.getArg! 3)
    let kt ← ks.toList.mapM kindE
    return s!"C {← boolE (e.getArg! 1)} {← posE (e.getArg! 2)} {ks.size} " ++
      " ".intercalate (kt ++ [← treeE (e.getArg! 4), ← treeE (e.getArg! 5)])
  else throw s!"not a tree: {e}"

def tplId (e : Expr) : Except String Nat :=
  match norm e with
  | .const n _ =>
    match n with
    | .str p s =>
      match p == `BoxKGen, s.startsWith "t", (s.drop 1).toString.toNat? with
      | true, true, some k => pure k
      | _, _, _ => throw s!"not a template name: {n}"
    | _ => throw s!"not a template name: {n}"
  | e => throw s!"not a template constant: {e}"

def symE (e : Expr) : Except String Nat := do
  let e := norm e
  if e.isAppOfArity ``ZZN.Sym.mk 6 then
    let bs ← e.getAppArgs.toList.mapM boolE
    return bs.foldl (fun a b => 2 * a + if b == "1" then 1 else 0) 0
  else throw s!"not a Sym: {e}"

partial def vecE (e : Expr) (acc : Array Nat := #[]) : Except String (Array Nat) := do
  let e := norm e
  if e.isAppOfArity ``Matrix.vecCons 4 then vecE (e.getArg! 3) (acc.push (← natE (e.getArg! 2)))
  else if e.isAppOfArity ``Matrix.vecEmpty 1 then pure acc
  else throw s!"not a vector: {e}"

/-- A slice `(rows, chain, pairs, fires, sols)` as `x0 x1 x2 x3 ; id sym … ; lane n0 c0 n1 c1 …`. -/
def sliceE (e : Expr) : Except String String := do
  let (rows, r1) ← pairE e
  let (_chain, r2) ← pairE r1
  let (pairs, r3) ← pairE r2
  let (_fires, sols) ← pairE r3
  let xs ← vecE rows
  let ps ← (← listE pairs).toList.mapM fun p => do
    let (t, σ) ← pairE p
    return s!"{← tplId t} {← symE σ}"
  let ss ← (← listE sols).toList.mapM fun s => do
    let (a, s) ← pairE s
    let (b, s) ← pairE s
    let (c, s) ← pairE s
    let (d, f) ← pairE s
    return s!"{← natE a} {← natE b} {← natE c} {← natE d} {← natE f}"
  return " ".intercalate (xs.toList.map toString) ++ " ; " ++ " ".intercalate ps ++ " ; " ++
    " ".intercalate ss

def valueOf (env : Environment) (n : Name) : Except String Expr :=
  match env.find? n with
  | some ci =>
    match ci.value? with
    | some v => pure v
    | none => throw s!"{n} has no value"
  | none => throw s!"{n} not found"

def runData (out : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `ZZN.Look.Table}] {} (trustLevel := 1024)
  let h ← IO.FS.Handle.mk out .write
  let mut nt := 0
  let mut ns := 0
  repeat
    match valueOf env (.str `BoxKGen s!"t{nt}") with
    | .ok v =>
      match treeE v with
      | .ok s => h.putStrLn s!"T {nt} {s}"
      | .error e => throw (IO.userError s!"t{nt}: {e}")
      nt := nt + 1
    | .error _ => break
  for w in List.range' 11 6 do
    for hh in List.range' w (17 - w) do
      let tabN := Name.str (Name.str `ZZN.LookGen s!"N{w}x{hh}") "tab"
      let ds ← match valueOf env tabN >>= (listE ·) with
        | .ok ds => pure ds
        | .error e => throw (IO.userError e)
      for (d, k) in ds.toList.zip (List.range ds.size) do
        let r := match norm d with
          | .const n _ => valueOf env n >>= sliceE
          | e => .error s!"not a slice constant: {e}"
        match r with
        | .ok s => h.putStrLn s!"D {w} {hh} {k} {s}"
        | .error e => throw (IO.userError s!"N{w}x{hh} slice {k}: {e}")
        ns := ns + 1
  for (w, hh, es) in primeTable do
    for (s, t, p) in es do
      h.putStrLn (s!"P {w} {hh} {s.1} {s.2} {t.1} {t.2} " ++
        " ".intercalate (p.map fun v => s!"{v.1} {v.2}"))
  IO.println s!"data: templates {nt}, slices {ns}, prime shapes {primeTable.length}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cases", file, table] => runCases file table
  | ["data", out] => runData out
  | _ =>
    IO.println "usage: LookEval.lean cases CASES TABLE | data OUT"
    return 2
