import ZZN.WinK.Engine
/-!
Generate checkpointed window-certificate modules, few and large.
`lake env lean --run tools/WinGen2.lean OUTDIR NAME a odd TMSPEC FSPECS`
TMSPEC: "r,c,col;r,c,col;..."; FSPECS: Lean `FSpec` terms separated by ";;".

Layout (all kernel checks serial, `Elab.async false`, so a module's memory stays that of one check):
* `D.lean`: every checkpoint (`B{i}_{j}`, `L{i}`, `F{i}`, `N{i}`) and, per outside specification
  `fk`, the sorted packed signatures `SA{fk}`, `NS{fk}` of the final states;
* `T{g}.lean`: step theorems, `TPER` per module;
* `G{g}.lean`: signature theorems (`sigsOKR` over ranges of `SIGPER` signatures) and the final
  bucket theorems (`finalSigOK`), `GPER` per module;
* `Main.lean`: the covering chain and `cert{fk}`.

The outside test (an enumeration of non-crossing matchings) runs once per distinct signature, not
once per final state and specification.
-/
open ZZN ZZN.Win ZZN.WinK

def bucketSize : ℕ := 1024
def finBucket : ℕ := 256
def sigPer : ℕ := 64

def hex (n : ℕ) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def pack (cs : List ℕ) : ℕ := (cs.zip (List.range cs.length)).foldl (fun acc (c, k) => acc ||| (c <<< (W * k))) 0

partial def chunks {α} (n : ℕ) (l : List α) : List (List α) :=
  if l.isEmpty then [] else l.take n :: chunks n (l.drop n)

def mergeSortN (l : List ℕ) : List ℕ := (l.mergeSort (· ≤ ·)).eraseDups

def parseTm (s : String) : List ((ℕ × ℕ) × ℕ) :=
  (s.splitOn ";").filterMap fun t => match (t.splitOn ",").map String.toNat! with
    | [r, c, col] => some ((r, c), col)
    | _ => none

/-- `none`, or `some (c, (s : ℤ), none)`, or `some (c, (s : ℤ), some k)`. -/
def parseF (s : String) : FSpec :=
  let t := (((((s.replace "(" "").replace ")" "").replace ": ℤ" "").replace "some " "").replace " " "")
  if t == "none" then none else
  match t.splitOn "," with
  | [c, sg, x] =>
    let sv : Int := if sg.startsWith "-" then -((sg.drop 1).toNat! : Int) else (sg.toNat! : Int)
    some (c.toNat!, sv, if x == "none" then none else some x.toNat!)
  | _ => none

def envNat (k : String) (d : ℕ) : IO ℕ := do
  match (← IO.getEnv k) with
  | some v => pure v.toNat!
  | none => pure d

def hdr (imports : List String) (ns : String) : String :=
  String.join (imports.map fun i => s!"import {i}\n") ++
    s!"set_option Elab.async false\nnamespace {ns}\nopen ZZN.WinK ZZN.Win\n"

def main (args : List String) : IO Unit := do
  let [out, name, aS, oddS, tmS, fS] := args | throw (IO.userError "args")
  let tPer ← envNat "TPER" 64
  let gPer ← envNat "GPER" 32
  let a := aS.toNat!
  let tm := parseTm tmS
  let dir := s!"{out}/{name}"
  IO.FS.createDirAll dir
  let ns := s!"WinKGen.{name}"
  let mut S : List St := [([], 0)]
  let mut sets : Array (List ℕ) := #[mergeSortN (S.map enc)]
  for i in List.range (a * a) do
    S := stage a a tm S i
    sets := sets.push (mergeSortN (S.map enc))
  let n := a * a
  let Fs := fS.splitOn ";;"
  let finals := (sets[n]!).map dec
  -- signatures per outside specification
  let sigs : List (List ℕ) := Fs.map fun F =>
    let Fv := parseF F
    mergeSortN (finals.map fun s =>
      let g := sigOf a a Fv s; sigCode g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2)
  -- data
  let mut d := s!"import ZZN.WinK.Engine\nnamespace {ns}\nopen ZZN.WinK\n"
  for i in List.range (n + 1) do
    let bs := chunks (if i == n then finBucket else bucketSize) (sets[i]!)
    for (b, j) in bs.zip (List.range bs.length) do
      d := d ++ s!"def B{i}_{j} : ℕ × ℕ := ({hex (pack b)}, {b.length})\n"
    d := d ++ s!"def L{i} : KSet := [{String.intercalate ", " ((List.range bs.length).map fun j => s!"B{i}_{j}")}]\n"
    d := d ++ s!"def F{i} : ℕ := {hex (pack (bs.map fun b => b.headD 0))}\n"
    d := d ++ s!"def N{i} : ℕ := {bs.length}\n"
  for (cs, fk) in sigs.zip (List.range sigs.length) do
    d := d ++ s!"def SA{fk} : ℕ := {hex (pack cs)}\ndef NS{fk} : ℕ := {cs.length}\n"
  d := d ++ s!"end {ns}\n"
  IO.FS.writeFile s!"{dir}/D.lean" d
  -- step theorems
  let tmLit := s!"[{String.intercalate ", " (tm.map fun ((r, c), col) => s!"(({r}, {c}), {col})")}]"
  let mut steps : List String := []
  for i in List.range n do
    let nb := (chunks bucketSize (sets[i]!)).length
    for j in List.range nb do
      steps := steps ++ [s!"theorem st{i}_{j} : stepOK {a} {a} {tmLit} {i} B{i}_{j}.1 B{i}_{j}.2 L{i+1} F{i+1} N{i+1} = true := by decide +kernel\n"]
  let tGroups := chunks tPer steps
  for (g, gi) in tGroups.zip (List.range tGroups.length) do
    IO.FS.writeFile s!"{dir}/T{gi}.lean" (hdr [s!"WinKGen.{name}.D"] ns ++ String.join g ++ s!"end {ns}\n")
  -- signature and final theorems
  let nbF := (chunks finBucket (sets[n]!)).length
  let mut fins : List String := []
  for (F, fk) in Fs.zip (List.range Fs.length) do
    let ns' := (sigs[fk]!).length
    for (rg, rk) in (chunks sigPer (List.range ns')).zip (List.range ns') do
      let lo := rg.headD 0
      fins := fins ++ [s!"theorem sg{fk}_{rk} : sigsOKR {oddS} SA{fk} {lo} {lo + rg.length} = true := by decide +kernel\n"]
  -- one declaration per final bucket checks every specification, so the kernel computes the
  -- specification-independent parts of each state's signature once
  for j in List.range nbF do
    let terms := (Fs.zip (List.range Fs.length)).map fun (F, fk) =>
      s!"finalSigOK {a} {a} ({F}) B{n}_{j}.1 B{n}_{j}.2 SA{fk} NS{fk}"
    let conj := String.intercalate " ∧ " (terms.map fun x => s!"{x} = true")
    let mut t := s!"theorem fsigAll_{j} : {conj} := by decide +kernel\n"
    for (tm', fk) in terms.zip (List.range terms.length) do
      let proj := String.join ((List.range fk).map fun _ => ".2") ++ (if fk + 1 < terms.length then ".1" else "")
      t := t ++ s!"theorem fsig{fk}_{j} : {tm'} = true := fsigAll_{j}{proj}\n"
    fins := fins ++ [t]
  let gGroups := chunks gPer fins
  for (g, gi) in gGroups.zip (List.range gGroups.length) do
    IO.FS.writeFile s!"{dir}/G{gi}.lean" (hdr [s!"WinKGen.{name}.D"] ns ++ String.join g ++ s!"end {ns}\n")
  -- assembly
  let mut txt := hdr ([s!"WinKGen.{name}.D"] ++ (List.range tGroups.length).map (fun gi => s!"WinKGen.{name}.T{gi}") ++
    (List.range gGroups.length).map (fun gi => s!"WinKGen.{name}.G{gi}")) ns
  let rc (k : ℕ) : String := String.intercalate " | " ((List.range k).map fun _ => "rfl")
  let memIntro (L : String) (names : List String) : String :=
    let first := names.headD ""
    if names.length == 0 then s!"  intro p hp\n  simp [{L}] at hp\n"
    else if names.length == 1 then s!"  intro p hp\n  simp only [{L}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n  subst hp; exact {first}\n"
    else s!"  intro p hp\n  simp only [{L}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n  rcases hp with {rc names.length}\n  exacts [{String.intercalate ", " names}]\n"
  txt := txt ++ s!"theorem cov0 : Cov L0 ((List.range 0).foldl (stage {a} {a} {tmLit}) [([], 0)]) :=\n  cov_init ⟨getW B0_0.1 0, ⟨B0_0, by simp [L0], 0, by decide +kernel, rfl⟩, by decide +kernel⟩\n"
  for i in List.range n do
    let nb := (chunks bucketSize (sets[i]!)).length
    txt := txt ++ s!"theorem cov{i+1} : Cov L{i+1} ((List.range {i+1}).foldl (stage {a} {a} {tmLit}) [([], 0)]) := by\n  rw [inside_succ]\n  refine cov_stage (firsts := F{i+1}) (nb := N{i+1}) cov{i} ?_\n" ++
      memIntro s!"L{i}" ((List.range nb).map fun j => s!"st{i}_{j}")
  for (F, fk) in Fs.zip (List.range Fs.length) do
    let ns' := (sigs[fk]!).length
    let nR := (ns' + sigPer - 1) / sigPer
    txt := txt ++ s!"theorem sigAll{fk} : ∀ j, j < NS{fk} → outsideSig {oddS} (sigDec (getW SA{fk} j)).1 (sigDec (getW SA{fk} j)).2.1 (sigDec (getW SA{fk} j)).2.2.1 (sigDec (getW SA{fk} j)).2.2.2.1 (sigDec (getW SA{fk} j)).2.2.2.2 = false := by\n  intro j hj\n"
    if nR == 0 then
      txt := txt ++ s!"  simp [NS{fk}] at hj\n"
    else
      txt := txt ++ String.intercalate "\n" ((List.range nR).map fun rk =>
        if rk + 1 < nR then s!"  by_cases h{rk} : j < {(rk + 1) * sigPer}\n  · exact sigsOKR_spec sg{fk}_{rk} j (by omega) h{rk}"
        else s!"  · exact sigsOKR_spec sg{fk}_{rk} j (by omega) (by simpa [NS{fk}] using hj)") ++ "\n"
    txt := txt ++ s!"theorem cert{fk} : certify {a} {a} {tmLit} {oddS} ({F}) = true := by\n  refine certify_of_cov (L := L{n}) (by unfold inside; exact cov{n}) ?_\n" ++
      memIntro s!"L{n}" ((List.range nbF).map fun j => s!"(final_of_sigs' sigAll{fk} fsig{fk}_{j})")
  txt := txt ++ s!"end {ns}\n"
  IO.FS.writeFile s!"{dir}/Main.lean" txt
  IO.println s!"{name}: stages {n}, Σ states {(sets.toList.map List.length).foldl (· + ·) 0}, final {(sets[n]!).length}, sigs {sigs.map List.length}, T modules {tGroups.length}, G modules {gGroups.length}"
