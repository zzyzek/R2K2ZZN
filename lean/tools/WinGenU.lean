import ZZN.WinK.Shared
/-!
Generate window certificates that share their late stages.
`lake env lean --run tools/WinGenU.lean CASES OUTDIR A`

Cases with window size `A` whose names end in `c0` or `A0` (the ones `CertFacts` asks for).
Let `J` be one more than the last terminal cell of any case. Every case keeps its own checkpoints
for cells `0 … J-1`; from stage `J` on the checkpoints are the union over all cases, stepped once
with the empty terminal list (`cov_stage_shared`). The union's final states are checked once per
outside specification `F` (signatures) and the signatures once per (odd, F).

Writes `OUTDIR/Shared/{D,T*,G*,Main}.lean` and `OUTDIR/NAME/Main.lean` (namespace `WinKU.NAME`,
theorems `cert{k}` for the k-th specification of the case).
-/
open ZZN ZZN.Win ZZN.WinK

def bucketSize : ℕ := 1024
def finBucket : ℕ := 256
def sigPer : ℕ := 64
def tPer : ℕ := 64
def gPer : ℕ := 48

def hex (n : ℕ) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def pack (cs : List ℕ) : ℕ := (cs.zip (List.range cs.length)).foldl (fun acc (c, k) => acc ||| (c <<< (W * k))) 0

partial def chunks {α} (n : ℕ) (l : List α) : List (List α) :=
  if l.isEmpty then [] else l.take n :: chunks n (l.drop n)

def mergeSortN (l : List ℕ) : List ℕ := (l.mergeSort (· ≤ ·)).eraseDups

def parseTm (s : String) : List ((ℕ × ℕ) × ℕ) :=
  (s.splitOn ";").filterMap fun t => match (t.splitOn ",").map String.toNat! with
    | [r, c, col] => some ((r, c), col)
    | _ => none

def parseF (s : String) : FSpec :=
  let t := (((((s.replace "(" "").replace ")" "").replace ": ℤ" "").replace "some " "").replace " " "")
  if t == "none" then none else
  match t.splitOn "," with
  | [c, sg, x] =>
    let sv : Int := if sg.startsWith "-" then -((sg.drop 1).toNat! : Int) else (sg.toNat! : Int)
    some (c.toNat!, sv, if x == "none" then none else some x.toNat!)
  | _ => none

def hdr (imports : List String) (ns : String) : String :=
  String.join (imports.map fun i => s!"import {i}\n") ++
    s!"set_option Elab.async false\nnamespace {ns}\nopen ZZN.WinK ZZN.Win\n"

def rc (k : ℕ) : String := String.intercalate " | " ((List.range k).map fun _ => "rfl")

-- Membership goals `∀ p ∈ L, P p` are closed by one `AllP` term: `rcases` over the
-- unfolded list is quadratic in its length (25 s per 120-element list).
--
def memIntro (L : String) (names : List String) : String :=
  if names.length == 0 then s!"  exact AllP.mem (L := {L}) trivial\n"
  else s!"  exact AllP.mem (L := {L}) ⟨{String.intercalate ", " (names ++ ["trivial"])}⟩\n"

def allPDefs : String :=
  "def AllP {α : Type} (P : α → Prop) : List α → Prop\n" ++
  "  | [] => True\n  | a :: l => P a ∧ AllP P l\n" ++
  "theorem AllP.mem {α : Type} {P : α → Prop} : ∀ {L : List α}, AllP P L → ∀ p ∈ L, P p\n" ++
  "  | _ :: _, ⟨h, _⟩, _, .head _ => h\n  | _ :: _, ⟨_, t⟩, p, .tail _ hp => AllP.mem t p hp\n"

def dataDefs (pre : String) (i : ℕ) (codes : List ℕ) (bsz : ℕ) : String := Id.run do
  let bs := chunks bsz codes
  let mut d := ""
  for (b, j) in bs.zip (List.range bs.length) do
    d := d ++ s!"def {pre}B{i}_{j} : ℕ × ℕ := ({hex (pack b)}, {b.length})\n"
  d := d ++ s!"def {pre}L{i} : KSet := [{String.intercalate ", " ((List.range bs.length).map fun j => s!"{pre}B{i}_{j}")}]\n"
  d := d ++ s!"def {pre}F{i} : ℕ := {hex (pack (bs.map fun b => b.headD 0))}\n"
  d := d ++ s!"def {pre}N{i} : ℕ := {bs.length}\n"
  return d

structure Case where
  name : String
  odd : ℕ
  tm : List ((ℕ × ℕ) × ℕ)
  tmS : String
  Fs : List String

def main (args : List String) : IO Unit := do
  let [file, out, aS] := args | throw (IO.userError "args")
  let a := aS.toNat!
  let n := a * a
  let mut cases : Array Case := #[]
  for l in ← IO.FS.lines file do
    match l.splitOn "|" with
    | [name, aa, oddS, tmS, fS] =>
      if aa.toNat! != a || !(name.endsWith "c0" || name.endsWith "A0") then continue
      cases := cases.push ⟨name, oddS.toNat!, parseTm tmS, tmS, fS.splitOn ";;"⟩
    | _ => pure ()
  let J := 1 + (cases.toList.flatMap fun c => c.tm.map fun ((r, cc), _) => r * a + cc).foldl max 0
  -- own stage sets 0 … J, and the union from J
  let mut own : Array (Array (List ℕ)) := #[]
  let mut uJ : List ℕ := []
  for c in cases do
    let mut S : List St := [([], 0)]
    let mut sets : Array (List ℕ) := #[mergeSortN (S.map enc)]
    for i in List.range J do
      S := stage a a c.tm S i
      sets := sets.push (mergeSortN (S.map enc))
    own := own.push sets
    uJ := uJ ++ sets[J]!
  let mut U : Array (List ℕ) := Array.replicate (n + 1) []
  U := U.set! J (mergeSortN uJ)
  for i in List.range n do
    if i ≥ J then
      U := U.set! (i + 1) (mergeSortN ((stage a a [] (U[i]!.map dec) i).map enc))
  -- specifications
  let mut Fl : List String := []
  let mut OF : List (ℕ × String) := []
  for c in cases do
    for F in c.Fs do
      if !(Fl.contains F) then Fl := Fl ++ [F]
      if !(OF.contains (c.odd, F)) then OF := OF ++ [(c.odd, F)]
  let finals := (U[n]!).map dec
  let sigs : List (List ℕ) := Fl.map fun F =>
    let Fv := parseF F
    mergeSortN (finals.map fun s => let g := sigOf a a Fv s; sigCode g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2)
  let fidx (F : String) : ℕ := Fl.idxOf F
  -- shared modules
  let sd := s!"{out}/Shared"
  IO.FS.createDirAll sd
  let sns := "WinKU.Shared"
  let mut d := s!"import ZZN.WinK.Shared\nnamespace {sns}\nopen ZZN.WinK\n"
  for i in List.range (n + 1) do
    if i ≥ J then d := d ++ dataDefs "U" i (U[i]!) (if i == n then finBucket else bucketSize)
  for (cs, f) in sigs.zip (List.range sigs.length) do
    d := d ++ s!"def SA{f} : ℕ := {hex (pack cs)}\ndef NS{f} : ℕ := {cs.length}\n"
  d := d ++ s!"end {sns}\n"
  IO.FS.writeFile s!"{sd}/D.lean" d
  let mut steps : List String := []
  for i in List.range n do
    if i ≥ J then
      for j in List.range (chunks bucketSize (U[i]!)).length do
        steps := steps ++ [s!"theorem stU{i}_{j} : stepOK {a} {a} [] {i} UB{i}_{j}.1 UB{i}_{j}.2 UL{i+1} UF{i+1} UN{i+1} = true := by decide +kernel\n"]
  let tG := chunks tPer steps
  for (g, gi) in tG.zip (List.range tG.length) do
    IO.FS.writeFile s!"{sd}/T{gi}.lean" (hdr [s!"{sns}.D"] sns ++ String.join g ++ s!"end {sns}\n")
  let nbF := (chunks finBucket (U[n]!)).length
  let mut fins : List String := []
  for (F, f) in Fl.zip (List.range Fl.length) do
    for j in List.range nbF do
      fins := fins ++ [s!"theorem fsig{f}_{j} : finalSigOK {a} {a} ({F}) UB{n}_{j}.1 UB{n}_{j}.2 SA{f} NS{f} = true := by decide +kernel\n"]
  for (o, F) in OF do
    let f := fidx F
    let ns' := (sigs[f]!).length
    for (rg, rk) in (chunks sigPer (List.range ns')).zip (List.range ns') do
      let lo := rg.headD 0
      fins := fins ++ [s!"theorem sg{o}_{f}_{rk} : sigsOKR {o} SA{f} {lo} {lo + rg.length} = true := by decide +kernel\n"]
  let gG := chunks gPer fins
  for (g, gi) in gG.zip (List.range gG.length) do
    IO.FS.writeFile s!"{sd}/G{gi}.lean" (hdr [s!"{sns}.D"] sns ++ String.join g ++ s!"end {sns}\n")
  let mut sm := hdr ([s!"{sns}.D"] ++ (List.range tG.length).map (fun gi => s!"{sns}.T{gi}") ++
    (List.range gG.length).map (fun gi => s!"{sns}.G{gi}")) sns ++ allPDefs
  for i in List.range n do
    if i ≥ J then
      let nb := (chunks bucketSize (U[i]!)).length
      sm := sm ++ s!"theorem hU{i} : ∀ p ∈ UL{i}, stepOK {a} {a} [] {i} p.1 p.2 UL{i+1} UF{i+1} UN{i+1} = true := by\n" ++
        memIntro s!"UL{i}" ((List.range nb).map fun j => s!"stU{i}_{j}")
  for (o, F) in OF do
    let f := fidx F
    let ns' := (sigs[f]!).length
    let nR := (ns' + sigPer - 1) / sigPer
    sm := sm ++ s!"theorem sigAll{o}_{f} : ∀ j, j < NS{f} → outsideSig {o} (sigDec (getW SA{f} j)).1 (sigDec (getW SA{f} j)).2.1 (sigDec (getW SA{f} j)).2.2.1 (sigDec (getW SA{f} j)).2.2.2.1 (sigDec (getW SA{f} j)).2.2.2.2 = false := by\n  intro j hj\n"
    if nR == 0 then
      sm := sm ++ s!"  simp [NS{f}] at hj\n"
    else
      sm := sm ++ String.intercalate "\n" ((List.range nR).map fun rk =>
        if rk + 1 < nR then s!"  by_cases h{rk} : j < {(rk + 1) * sigPer}\n  · exact sigsOKR_spec sg{o}_{f}_{rk} j (by omega) h{rk}"
        else s!"  · exact sigsOKR_spec sg{o}_{f}_{rk} j (by omega) (by simpa [NS{f}] using hj)") ++ "\n"
    sm := sm ++ s!"theorem finU{o}_{f} : ∀ p ∈ UL{n}, finalOK {a} {a} {o} ({F}) p.1 p.2 = true := by\n" ++
      memIntro s!"UL{n}" ((List.range nbF).map fun j => s!"(final_of_sigs' sigAll{o}_{f} fsig{f}_{j})")
  sm := sm ++ s!"end {sns}\n"
  IO.FS.writeFile s!"{sd}/Main.lean" sm
  -- one module per case
  for (c, ci) in cases.toList.zip (List.range cases.size) do
    let dir := s!"{out}/{c.name}"
    IO.FS.createDirAll dir
    let ns := s!"WinKU.{c.name}"
    let tmLit := s!"[{String.intercalate ", " (c.tm.map fun ((r, cc), col) => s!"(({r}, {cc}), {col})")}]"
    let sets := own[ci]!
    let mut t := hdr [s!"{sns}.Main"] ns ++ s!"open {sns}\n"
    for i in List.range J do
      t := t ++ dataDefs "" i (sets[i]!) bucketSize
    for i in List.range J do
      let nb := (chunks bucketSize (sets[i]!)).length
      for j in List.range nb do
        let tgt := if i + 1 == J then s!"UL{J} UF{J} UN{J}" else s!"L{i+1} F{i+1} N{i+1}"
        t := t ++ s!"theorem st{i}_{j} : stepOK {a} {a} {tmLit} {i} B{i}_{j}.1 B{i}_{j}.2 {tgt} = true := by decide +kernel\n"
    t := t ++ s!"theorem cov0 : Cov L0 ((List.range 0).foldl (stage {a} {a} {tmLit}) [([], 0)]) :=\n  cov_init ⟨getW B0_0.1 0, ⟨B0_0, by simp [L0], 0, by decide +kernel, rfl⟩, by decide +kernel⟩\n"
    for i in List.range n do
      let lhs := if i + 1 ≥ J then s!"UL{i+1}" else s!"L{i+1}"
      t := t ++ s!"theorem cov{i+1} : Cov {lhs} ((List.range {i+1}).foldl (stage {a} {a} {tmLit}) [([], 0)]) := by\n  rw [inside_succ]\n"
      if i < J then
        let nb := (chunks bucketSize (sets[i]!)).length
        let (fs, nbs) := if i + 1 == J then (s!"UF{J}", s!"UN{J}") else (s!"F{i+1}", s!"N{i+1}")
        t := t ++ s!"  refine cov_stage (firsts := {fs}) (nb := {nbs}) cov{i} ?_\n" ++
          memIntro s!"L{i}" ((List.range nb).map fun j => s!"st{i}_{j}")
      else
        t := t ++ s!"  exact cov_stage_shared cov{i} (by decide) hU{i}\n"
    for (F, fk) in c.Fs.zip (List.range c.Fs.length) do
      t := t ++ s!"theorem cert{fk} : certify {a} {a} {tmLit} {c.odd} ({F}) = true :=\n  certify_of_cov (L := UL{n}) (by unfold inside; exact cov{n}) finU{c.odd}_{fidx F}\n"
    t := t ++ s!"end {ns}\n"
    IO.FS.writeFile s!"{dir}/Main.lean" t
  IO.println s!"cases {cases.size}, J {J}, union states {(List.range (n + 1)).foldl (fun s i => if i ≥ J then s + (U[i]!).length else s) 0}, own states {(own.toList.map fun s => (s.toList.map List.length).foldl (· + ·) 0).foldl (· + ·) 0}, final {(U[n]!).length}, F {Fl.length}, (odd,F) {OF.length}, sigs {sigs.map List.length}, shared T {tG.length} G {gG.length}"
