import ZZN.WinK.Engine
/-!
Generate checkpointed window-certificate modules.
`lake env lean --run tools/WinGen.lean OUTDIR NAME a odd TMSPEC FSPEC`
TMSPEC: list of r,c,col triples "r,c,col;r,c,col;..."; FSPEC: "none" or "col,sign,slot|none".
Writes OUTDIR/NAME/S{i}.lean (checkpoint data), OUTDIR/NAME/T{i}_{part}.lean (step theorems),
OUTDIR/NAME/Fin_{part}.lean (final theorems), OUTDIR/NAME/Main.lean (assembly).
-/
open ZZN ZZN.Win ZZN.WinK

def bucketSize : ℕ := 1024
/-- Final-stage buckets are smaller: the outside test needs more kernel memory per state. -/
def finBucket : ℕ := 256
def thmsPerFile : ℕ := 8
def finPerFile : ℕ := 1

def hex (n : ℕ) : String := "0x" ++ String.mk (Nat.toDigits 16 n)

def pack (cs : List ℕ) : ℕ := (cs.zip (List.range cs.length)).foldl (fun acc (c, k) => acc ||| (c <<< (W * k))) 0

partial def chunks {α} (n : ℕ) (l : List α) : List (List α) :=
  if l.isEmpty then [] else l.take n :: chunks n (l.drop n)

def mergeSortN (l : List ℕ) : List ℕ := (l.mergeSort (· ≤ ·)).eraseDups

def parseTm (s : String) : List ((ℕ × ℕ) × ℕ) :=
  (s.splitOn ";").filterMap fun t => match (t.splitOn ",").map String.toNat! with
    | [r, c, col] => some ((r, c), col)
    | _ => none

def main (args : List String) : IO Unit := do
  let [out, name, aS, oddS, tmS, fS] := args | throw (IO.userError "args")
  let a := aS.toNat!
  let tm := parseTm tmS
  let dir := s!"{out}/{name}"
  IO.FS.createDirAll dir
  let ns := s!"WinKGen.{name}"
  -- stage sets as sorted code lists
  let mut S : List St := [([], 0)]
  let mut sets : Array (List ℕ) := #[mergeSortN (S.map enc)]
  for i in List.range (a * a) do
    S := stage a a tm S i
    sets := sets.push (mergeSortN (S.map enc))
  -- data modules
  for i in List.range (a * a + 1) do
    let bs := chunks (if i == a * a then finBucket else bucketSize) (sets[i]!)
    let mut txt := s!"import ZZN.WinK.Engine\nnamespace {ns}\nopen ZZN.WinK\n"
    for (b, j) in bs.zip (List.range bs.length) do
      txt := txt ++ s!"def B{i}_{j} : ℕ × ℕ := ({hex (pack b)}, {b.length})\n"
    txt := txt ++ s!"def L{i} : KSet := [{String.intercalate ", " ((List.range bs.length).map fun j => s!"B{i}_{j}")}]\n"
    txt := txt ++ s!"def F{i} : ℕ := {hex (pack (bs.map fun b => b.headD 0))}\n"
    txt := txt ++ s!"def N{i} : ℕ := {bs.length}\nend {ns}\n"
    IO.FS.writeFile s!"{dir}/S{i}.lean" txt
  -- step theorem modules
  let tmLit := s!"[{String.intercalate ", " (tm.map fun ((r, c), col) => s!"(({r}, {c}), {col})")}]"
  for i in List.range (a * a) do
    let nb := (chunks bucketSize (sets[i]!)).length
    for (part, pj) in (chunks thmsPerFile (List.range nb)).zip (List.range nb) do
      let mut txt := s!"import WinKGen.{name}.S{i}\nimport WinKGen.{name}.S{i+1}\nnamespace {ns}\nopen ZZN.WinK\n"
      for j in part do
        txt := txt ++ s!"theorem st{i}_{j} : stepOK {a} {a} {tmLit} {i} B{i}_{j}.1 B{i}_{j}.2 L{i+1} F{i+1} N{i+1} = true := by decide +kernel\n"
      txt := txt ++ s!"end {ns}\n"
      IO.FS.writeFile s!"{dir}/T{i}_{pj}.lean" txt
  -- final theorems, one family per F
  let n := a * a
  let Fs := fS.splitOn ";;"
  let useSig := (← IO.getEnv "WINGEN_SIG").isSome
  let nbF := (chunks finBucket (sets[n]!)).length
  let nFiles := (nbF + finPerFile - 1) / finPerFile
  let sigPer : ℕ := 64
  let mut nSigFiles := 0
  if useSig then
    let Fv : FSpec := none
    let finals := (sets[n]!).map dec
    let codes := mergeSortN (finals.map fun s =>
      let g := sigOf a a Fv s; sigCode g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2)
    let mut txt := s!"import ZZN.WinK.Engine\nnamespace {ns}\nopen ZZN.WinK\n"
    txt := txt ++ s!"def SA : ℕ := {hex (pack codes)}\ndef NS : ℕ := {codes.length}\nend {ns}\n"
    IO.FS.writeFile s!"{dir}/Sig.lean" txt
    let ranges := chunks sigPer (List.range codes.length)
    nSigFiles := ranges.length
    for (rg, rk) in ranges.zip (List.range ranges.length) do
      let lo := rg.headD 0
      let hi := lo + rg.length
      let t := s!"import WinKGen.{name}.Sig\nnamespace {ns}\nopen ZZN.WinK\ntheorem sg{rk} : sigsOKR {oddS} SA {lo} {hi} = true := by decide +kernel\nend {ns}\n"
      IO.FS.writeFile s!"{dir}/SigR{rk}.lean" t
    for (part, pj) in (chunks finPerFile (List.range nbF)).zip (List.range nbF) do
      let mut t := s!"import WinKGen.{name}.S{n}\nimport WinKGen.{name}.Sig\nnamespace {ns}\nopen ZZN.WinK ZZN.Win\n"
      for jj in part do
        t := t ++ s!"theorem fsig_{jj} : finalSigOK {a} {a} (none) B{n}_{jj}.1 B{n}_{jj}.2 SA NS = true := by decide +kernel\n"
      t := t ++ s!"end {ns}\n"
      IO.FS.writeFile s!"{dir}/Fin0_{pj}.lean" t
  if !useSig then
    for (F, fk) in Fs.zip (List.range Fs.length) do
      for (part, pj) in (chunks finPerFile (List.range nbF)).zip (List.range nbF) do
        let mut txt := s!"import WinKGen.{name}.S{n}\nnamespace {ns}\nopen ZZN.WinK ZZN.Win\n"
        for j in part do
          txt := txt ++ s!"theorem fin{fk}_{j} : finalOK {a} {a} {oddS} ({F}) B{n}_{j}.1 B{n}_{j}.2 = true := by decide +kernel\n"
        txt := txt ++ s!"end {ns}\n"
        IO.FS.writeFile s!"{dir}/Fin{fk}_{pj}.lean" txt
  -- assembly
  let mut txt := ""
  for i in List.range (n + 1) do
    txt := txt ++ s!"import WinKGen.{name}.S{i}\n"
  for i in List.range n do
    let nb := (chunks bucketSize (sets[i]!)).length
    for pj in List.range ((nb + thmsPerFile - 1) / thmsPerFile) do
      txt := txt ++ s!"import WinKGen.{name}.T{i}_{pj}\n"
  for fk in List.range Fs.length do
    for pj in List.range nFiles do
      txt := txt ++ s!"import WinKGen.{name}.Fin{fk}_{pj}\n"
  for rk in List.range nSigFiles do
    txt := txt ++ s!"import WinKGen.{name}.SigR{rk}\n"
  txt := txt ++ s!"namespace {ns}\nopen ZZN.WinK ZZN.Win\n"
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
  if useSig then
    -- every signature fails, by range theorems
    let cases := String.intercalate "\n" ((List.range nSigFiles).map fun rk =>
      s!"  · exact sigsOKR_spec sg{rk} j (by omega) (by omega)")
    txt := txt ++ s!"theorem sigAll : ∀ j, j < NS → outsideSig {oddS} (sigDec (getW SA j)).1 (sigDec (getW SA j)).2.1 (sigDec (getW SA j)).2.2.1 (sigDec (getW SA j)).2.2.2.1 (sigDec (getW SA j)).2.2.2.2 = false := by\n  intro j hj\n  have hn : NS = {(nSigFiles - 1) * sigPer} + (NS - {(nSigFiles - 1) * sigPer}) := by decide\n" ++
      String.intercalate "\n" ((List.range nSigFiles).map fun rk =>
        if rk + 1 < nSigFiles then s!"  by_cases h{rk} : j < {(rk + 1) * sigPer}\n  · exact sigsOKR_spec sg{rk} j (by omega) h{rk}"
        else s!"  · exact sigsOKR_spec sg{rk} j (by omega) (by simpa [NS] using hj)") ++ "\n"
    let _ := cases
    for fk in List.range Fs.length do
      txt := txt ++ s!"theorem cert{fk} : certify {a} {a} {tmLit} {oddS} (none) = true := by\n  refine certify_of_cov (L := L{n}) (by unfold inside; exact cov{n}) ?_\n" ++
        memIntro s!"L{n}" ((List.range nbF).map fun j => s!"(final_of_sigs' sigAll fsig_{j})")
  if !useSig then
    for (F, fk) in Fs.zip (List.range Fs.length) do
      txt := txt ++ s!"theorem cert{fk} : certify {a} {a} {tmLit} {oddS} ({F}) = true := by\n  refine certify_of_cov (L := L{n}) (by unfold inside; exact cov{n}) ?_\n" ++
        memIntro s!"L{n}" ((List.range nbF).map fun j => s!"fin{fk}_{j}")
  txt := txt ++ s!"end {ns}\n"
  IO.FS.writeFile s!"{dir}/Main.lean" txt
  IO.println s!"{name}: stages {a * a}, Σ states {(sets.toList.map List.length).foldl (· + ·) 0}, final {(sets[a * a]!).length}"
