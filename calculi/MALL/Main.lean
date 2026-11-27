/-
`mallrun`: the producers of the Run stage, compiled.

    mallrun facts                      the facts file, for the corpus
    mallrun status                     one line for each entry of the corpus
    mallrun run <producer> <family> <n>   one member of a family: the
                                       verdict, the size of the tree, the time
    mallrun cert <producer> <family> <n>  the same, and a Lean file that
                                       states the fact with its tree
    mallrun model <family> <n>         a finite phase structure that refutes
                                       the member, and a Lean file with the fact
    mallrun refute <family> <n>        a saturated set of sequents of which
                                       the member is one, the size of the
                                       phase structure it presents, and a
                                       Lean file with the fact
    mallrun countermodel <name>        an entry of the corpus: its saturated
                                       set and the structure, described
    mallrun prove '<sequent>'          a sequent typed at a shell: the verdict
                                       and the sequent as it was read, then a
                                       Lean file that states the fact with its
                                       certificate.  `--short`: the first line
                                       only.  `--ascii`: the sequent in it with
                                       the signs of a keyboard.
                                       `--deadline=N`: seconds, 10 if not
                                       given.  Exit code 0 derivable, 1 not
                                       derivable, 3 flag, 2 a text that is not
                                       a sequent
    mallrun corpus                     the corpus as texts: name, status, the
                                       sequent in the source's notation, as
                                       Lean source, and with the signs of a
                                       keyboard
    mallrun show <family> <n>          a member of a family, with the signs of
                                       a keyboard

`<producer>` is `lazy` (the search by lazy splitting) or `search` (the
proved search).  Not trusted.  What it prints is checked by the kernel
when the file it wrote is elaborated.
-/
import MALL.Corpus.Basic
import MALL.ModelRun
import MALL.Refute
import MALL.Encode
import MALL.Parse

open MALL MALL.Corpus ProofTools ProofTools.Explore

/-- The number of moves of a tree of moves. -/
partial def certSize : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certSize x.2).sum

/-- The nesting of a tree of moves. -/
partial def certDepth : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certDepth x.2).foldl max 0

def showRepr {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100

/-- On one line: a structure instance printed over several lines by `Repr`
is not always read back by Lean. -/
def showFlat {α : Type} [Repr α] (x : α) : String := (repr x).pretty 1000000000

/-- The fact for an entry, as a Lean declaration. -/
def fact (name src : String) (Γ : List Form) : String :=
  match proveLazy Γ with
  | some c => s!"def {name} : Fam {src} :=\n  treeCert.verdict _ ({showRepr c})\n"
  | none =>
    match refuteBy Γ with
    | some z => s!"theorem {name} : ¬ Derivable {src} :=\n  noDerivableBy.verdict _ ({showFlat z})\n"
    | none =>
      match refuteSet Γ with
      | some D =>
        if refutedBy D Γ then
          s!"theorem {name} : ¬ Derivable {src} :=\n  noDerivableBySet.verdict _ ({showFlat D})\n"
        else s!"-- {name}: flag\n"
      | none => s!"-- {name}: flag\n"

def header : String :=
"/-
The facts of the corpus.  Written by `mallrun facts` (`Main.lean`); do not
edit.  The kernel checks each when this file is elaborated: for a
derivation, the tree of moves that the search by lazy splitting found;
against one, a finite phase structure on a cyclic group that refutes the
sequent, where the producer of `MALL/ModelRun.lean` has one, and otherwise
a saturated set of sequents of which it is a member (`MALL/SatRun.lean`),
from the producer of `MALL/Refute.lean`.
-/
import MALL.Corpus.Basic
import MALL.ModelRun
import MALL.SatRun

namespace MALL.Corpus.Facts

open MALL MALL.Corpus

"

/-! ## A sequent typed at a shell -/

/-- What the searches found for a sequent. -/
inductive Found where
  /-- A tree of moves that `treeCert` accepts. -/
  | tree (c : Cert S)
  /-- A phase structure on a cyclic group in which the sequent does not
  hold. -/
  | model (z : ZModel)
  /-- A saturated set of sequents of which the sequent is a member,
  written in numbers (`MALL/Coded.lean`). -/
  | set (C : CodeCert)
  /-- A certificate that the compiled check refused: a defect of the
  program. -/
  | defect (why : String)

/-- The "no" side: a small cyclic structure where the producer has one,
and otherwise the saturated set of the memoised search; `none` where that
search says the sequent is derivable.  Each certificate is checked here
before it is handed on. -/
def refuteSide (Γ : List Form) : Option Found :=
  match refuteBy Γ with
  | some z =>
    if z.refutes Γ then some (.model z)
    else some (.defect "the phase structure found does not refute the sequent")
  | none =>
    match refuteSet Γ with
    | some D =>
      let C := Encode.encode D Γ
      if codeRefutes C Γ then some (.set C)
      else some (.defect "the set of sequents found did not pass the check of saturation")
    | none => none

/-- Lean's two limits, lifted in every file the command prints: nobody
adds an option to a file made at a shell.  Seen without them: a phase
structure for a sequent with a letter numbered 92 (a list of 93 sets) was
refused with "maximum recursion depth has been reached", though the
sequent had nine formulas; so the size of the sequent is no guide to
whether they are needed. -/
def liftLimits : String := "
-- Lean's limits on the depth of recursion and on its own work are lifted
-- for this file: its terms can be large.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
"

/-- The head of the file `mallrun prove` prints, after its first line:
the imports, and a name for each of the letters `p q r s` that the
sequent has. -/
def proveHead (Γ : List Form) : String :=
  let names := ((List.range 4).filter fun n => (lettersL Γ).contains n).map fun n =>
    s!"abbrev {letterName n} : Form := .atom {n}\n"
  "/-
Written by `mallrun prove` (`Main.lean`) for a sequent typed at a shell.
The program is not trusted.  The kernel checks the certificate below when
this file is elaborated, in `calculi/MALL`: `lake env lean <file>`.
-/
import MALL.Run
import MALL.ModelRun
import MALL.SatRun

namespace MALL.Answer

open MALL

" ++ String.join names ++ liftLimits ++ s!"
/-- The sequent, as it was read. -/
def sequent : List Form := {srcForms Γ}
"

def proveFoot : String :=
  "\nend MALL.Answer\n\n#axioms_within_file [propext, Quot.sound]\n"

/-- **The largest saturated set the kernel has been seen to check**, in
numbers and stated in parts, under `lake env lean -M 4000`
(`campaign/measurements.md`, 2026-11-27): 11 110 sequents, in 102 s.
Nothing smaller that was tried failed.  An answer whose set is larger than
this says so in its first line.  (Written as lists and checked by
`refutedBy`, the limit was 102 sequents under 8 GB.) -/
def kernelSeen : Nat := 11110

/-- Above this many sequents the check of a set is stated in several
theorems, each for a part of the tree of at most `partSize` numbers.  As
one theorem the kernel was stopped at 4 GB at 2 057 sequents on one family
and passed at 1 717; in parts of at most 150 it stayed under 1 GB over the
imports at 11 110. -/
def partsFrom : Nat := 600

def partSize : Nat := 150

/-- The answer for what was found: the exit code, the verdict, and the
rest of the file. -/
def answerOf (Γ : List Form) : Found → UInt32 × String × String
  | .tree c =>
    (0, "derivable", proveHead Γ ++ s!"
/-- A tree of moves: each node a rule with its principal formula, and for
⊗ the context of its first premise. -/
def tree : ProofTools.Explore.Cert S :=
  {showRepr c}

/-- The kernel runs each move of the tree. -/
theorem checks : treeCert.check sequent tree = true := by decide +kernel

/-- A derivation of the sequent. -/
def proof : Fam sequent := treeCert.verdict sequent tree checks

theorem derivable : Derivable sequent := ⟨proof⟩

/-- By soundness: the sequent holds in every phase structure. -/
theorem valid : Valid sequent := soundness sequent derivable
" ++ proveFoot)
  | .model z =>
    (1, "not derivable", proveHead Γ ++ s!"
/-- A phase structure on the cyclic group ℤ/(k+1): the number `k`, the
antiphases, and for each letter a set of phases whose closure is its
fact. -/
def countermodel : ZModel :=
  {showFlat z}

/-- The kernel computes the interpretation of the sequent in the
structure: the unit is not in it. -/
theorem refutes : countermodel.refutes sequent = true := by decide +kernel

theorem notValid : ¬ Valid sequent := noValidBy.verdict sequent countermodel refutes

/-- By soundness. -/
theorem notDerivable : ¬ Derivable sequent := noDerivableBy.verdict sequent countermodel refutes
" ++ proveFoot)
  | .set C =>
    let n := C.tree.keys.length
    let beyond := n > kernelSeen
    let verdict := if beyond then
      s!"not derivable, by the compiled check only (a set of {n} sequents; the \
kernel has checked sets of up to {kernelSeen})"
      else "not derivable"
    let warn := if beyond then s!"
-- The set below has {n} sequents.  The kernel has checked sets of up to
-- {kernelSeen} sequents written this way, the largest in 102 s under a cap
-- of 4 GB of memory (`campaign/measurements.md`); its time grows with the
-- set.  Until this file is elaborated the answer rests on the compiled
-- check of this program, which is not trusted.
" else ""
    let doc := s!"/-- A saturated set of sequents of which the sequent is a member: every
rule that could conclude a member has a premise in the set.  It is written
in numbers (`MALL/Coded.lean`): `table` lists the formulas, each by its
connective and how many entries later its two parts stand; a number of
`tree` is a sequent, its digit in base `B` at a formula's place the number
of times the formula occurs; `goal` is the places of the formulas of the
sequent.  The {n} sequents themselves: `#eval refutation.sequents`. -/"
    let check :=
      if n ≤ partsFrom then s!"
{doc}
def refutation : CodeCert :=
  {Encode.showCert C}

/-- The kernel checks the membership and the saturation, in numbers. -/
theorem refuted : codeRefutes refutation sequent = true := by decide +kernel
"
      else
        let depth := (List.range 32).find? (fun d => n / 2 ^ d ≤ partSize) |>.getD 31
        let ((top, pf), (parts, keys)) := (Encode.cut depth C.tree).run (#[], #[])
        let defs := String.join ((List.range parts.size).map fun i =>
          s!"def part{i} : Tree := {Encode.showTree (parts.getD i .leaf)}\n")
        let partsOk := String.join ((List.range parts.size).map fun i =>
          s!"theorem part{i}_ok : Tree.all refutation.memberOK part{i} = true := by decide +kernel\n")
        let keysOk := String.join ((List.range keys.size).map fun i =>
          s!"theorem key{i}_ok : refutation.memberOK {keys.getD i 0} = true := by decide +kernel\n")
        s!"
-- The tree of the set, in {parts.size} parts.
{defs}
{doc}
def refutation : CodeCert :=
  {Encode.showCertWith C top}

-- The check is stated in parts, one theorem for the sequent, one for each
-- part of the tree and one for each number above the parts, and they are
-- elaborated one after another: the kernel keeps what it has reduced until
-- a theorem ends, so one theorem for a set of this size would need the
-- memory of all of them together.
set_option Elab.async false

/-- The sequent is the one at the places `goal`, and its number is in the
tree. -/
theorem goalOk : refutation.goalOK sequent = true := by decide +kernel

{partsOk}
{keysOk}
/-- The kernel has checked the membership and the saturation, in numbers:
by the theorems above, put together. -/
theorem refuted : codeRefutes refutation sequent = true :=
  codeRefutes_of_parts goalOk
    {pf}
"
    (1, verdict, proveHead Γ ++ warn ++ check ++ s!"
/-- So the set of sequents that the numbers stand for passes the check of
saturated sets (S27). -/
theorem refutedAsSequents : refutedBy refutation.sequents sequent = true :=
  refutedBy_of_code refutation sequent refuted

/-- By the soundness of the certifier `noDerivableByCode`
(`MALL/SatRun.lean`), applied to the check above as it is stated. -/
theorem notDerivable : ¬ Derivable sequent := not_derivable_of_code refuted

/-- By that of `noValidByCode`. -/
theorem notValid : ¬ Valid sequent := not_valid_of_code refuted

/-- The set presents a finite phase structure in which the sequent does
not hold. -/
theorem countermodel : ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat sequent :=
  countermodel_of_code refuted
" ++ proveFoot)
  | .defect why => (3, "flag", s!"-- {why}: a defect of `mallrun`\n")

/-- `mallrun prove`: the arguments after the word.  The text is the
arguments that are not options, joined by spaces.

Two searches run side by side: the search by lazy splitting, for a
derivation; and the "no" side.  The first that answers with a
certificate gives the verdict.  A flag: neither answered within the
deadline; or both ended and disagree, or a certificate did not pass the
compiled check, which would be defects. -/
partial def prove (args : List String) : IO UInt32 := do
  let usage := "usage: mallrun prove [--short] [--ascii] [--deadline=N] '<sequent>'    \
e.g.  mallrun prove 'p * q -o q * p'"
  let short := args.contains "--short"
  let ascii := args.contains "--ascii"
  let mut secs := 10
  for a in args do
    if a.startsWith "--deadline=" then
      match (a.drop 11).toString.toNat? with
      | some n => secs := n
      | none => IO.eprintln s!"mallrun prove: bad {a}\n{usage}"; return 2
  let texts := args.filter fun a => !(a == "--short" || a == "--ascii" || a.startsWith "--deadline=")
  if texts.isEmpty then
    IO.eprintln usage
    return 2
  let text := " ".intercalate texts
  match Parse.parseSeq text with
  | .error f => IO.eprintln s!"mallrun prove: {f.report text}"; return 2
  | .ok Γ =>
    let shown := if ascii then asciiSeq Γ else showSeq Γ
    let t₀ ← IO.monoMsNow
    let yes := Task.spawn (prio := .dedicated) fun _ => proveLazy Γ
    let no := Task.spawn (prio := .dedicated) fun _ => refuteSide Γ
    let out ← IO.getStdout
    let finish (found : Found) : IO UInt32 := do
      let (code, verdict, rest) := answerOf Γ found
      IO.println s!"-- {verdict}: {shown}"
      unless short do IO.print rest
      out.flush
      -- the other search may still be running: leave without waiting for it
      IO.Process.exit code.toUInt8
    let rec wait : IO UInt32 := do
      let yesDone ← IO.hasFinished yes
      let noDone ← IO.hasFinished no
      if yesDone then
        if let some c := yes.get then return ← finish (.tree c)
      if noDone then
        if let some f := no.get then return ← finish f
      if yesDone && noDone then
        return ← finish (.defect "the search by lazy splitting found no derivation and the \
memoised search says there is one")
      if (← IO.monoMsNow) - t₀ ≥ secs * 1000 then
        IO.println s!"-- flag: {shown}"
        unless short do
          IO.println s!"-- no answer within {secs} s; a longer deadline: --deadline=N, in seconds"
        out.flush
        IO.Process.exit 3
      IO.sleep 5
      wait
    wait

def produceBy (prod : String) (Γ : List Form) : Option (Cert S) :=
  if prod == "lazy" then proveLazy Γ else proveSearch Γ

def main (args : List String) : IO UInt32 := do
  match args with
  | ["facts"] =>
    IO.print header
    for e in entries do
      IO.println (fact e.name e.src e.seq)
    IO.println "end MALL.Corpus.Facts\n\n#axioms_within_file [propext, Quot.sound]"
    return 0
  | "prove" :: rest => prove rest
  | ["screen"] =>
    -- The statement "a certificate in numbers that passes stands for a set
    -- that passes the check of `MALL/Saturated.lean`", tried on altered
    -- certificates: every one that the check in numbers accepts is decoded
    -- and given to the check of sets.
    let mut total := 0
    let mut accepted := 0
    let mut bad := 0
    let fams := (List.range 6).filterMap (fun n => (family "bots" n).map (·.1)) ++
      (List.range 4).filterMap (fun n => (family "parBots" (n + 1)).map (·.1))
    for Γ in (entries.filter (!·.derivable)).map (·.seq) ++ fams do
      match refuteSet Γ with
      | none => pure ()
      | some D =>
        let C := Encode.encode D Γ
        let keys := C.tree.keys.toArray
        let mk (ks : Array Nat) : Tree := Encode.build (ks.qsort (· < ·)) 0 ks.size
        let n := C.table.length
        let mut alts : Array CodeCert := #[C, { C with tree := Encode.build keys.reverse 0 keys.size }]
        for b in [0, 1, 2, 3, C.B - 2, C.B - 1, C.B + 1, 2 * C.B] do
          alts := alts.push { C with B := b }
        for i in [0:keys.size] do
          alts := alts.push { C with tree := mk (keys.eraseIdx! i) }
          alts := alts.push { C with tree := mk (keys.set! i (keys[i]! + 1)) }
          for j in [0:n + 2] do
            alts := alts.push { C with tree := mk (keys.set! i (keys[i]! + C.B ^ j)) }
            alts := alts.push { C with tree := mk (keys.push (keys[i]! + C.B ^ j)) }
            alts := alts.push { C with tree := mk (keys.push (keys[i]! - C.B ^ j)) }
        for j in [0:n + 2] do
          alts := alts.push { C with tree := mk (keys.push (C.B ^ j)) }
          alts := alts.push { C with tree := mk (keys.push (C.B ^ j + C.B ^ (j + 1))) }
          alts := alts.push { C with tree := mk (keys.push (2 * C.B ^ j)) }
          alts := alts.push { C with tree := mk (keys.push ((C.B - 1) * C.B ^ j)) }
        alts := alts.push { C with tree := mk (keys.push 0) }
        let kinds (a c : Nat) : List Node :=
          [.atom a, .natom a, .atom c, .natom c, .one, .bot, .top, .zero, .tensor a c, .par a c,
           .wth a c, .plus a c, .tensor c a, .par (a + 1) c, .wth a (c + 1), .plus (a + 1) (c + 1),
           .tensor (a + n) c, .par 0 0, .tensor 0 0]
        for i in [0:n] do
          let (a, c) := match C.table.getD i .one with
            | .tensor a c | .par a c | .wth a c | .plus a c => (a, c)
            | .atom a | .natom a => (a, a + 1)
            | _ => (0, 1)
          for N in kinds a c do
            alts := alts.push { C with table := C.table.set i N }
          alts := alts.push { C with table := C.table.eraseIdx i }
          alts := alts.push { C with table := C.table.take i ++ [C.table.getD i .one] ++ C.table.drop i }
        for i in [0:C.goal.length] do
          alts := alts.push { C with goal := C.goal.eraseIdx i }
          for j in [0:n + 1] do
            alts := alts.push { C with goal := C.goal.set i j }
            alts := alts.push { C with goal := j :: C.goal }
        for C' in alts do
          total := total + 1
          if codeRefutes C' Γ then
            accepted := accepted + 1
            unless refutedBy C'.sequents Γ do
              bad := bad + 1
              if bad ≤ 5 then
                IO.println s!"FAILS: {showSeq Γ}\n  {Encode.showCert C'}"
    IO.println s!"certificates tried: {total}; accepted by the check in numbers: {accepted}; \
of those, decoded sets that the check of sets refuses: {bad}"
    return (if bad == 0 then 0 else 1)
  | ["corpus"] =>
    for e in entries do
      IO.println s!"{e.name}\t{if e.derivable then "derivable" else "not derivable"}\t{showSeq e.seq}\t{srcForms e.seq}\t{asciiSeq e.seq}"
    return 0
  | ["show", fam, n] =>
    match family fam n.toNat! with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) => IO.println (asciiSeq Γ); return 0
  | ["status"] =>
    for e in entries do
      let lz := proveLazy e.seq
      let sr := proveSearch e.seq
      let dec := decide (Derivable e.seq)
      let show1 (c : Option (Cert S)) : String := match c with
        | some c => s!"a tree of {certSize c} moves"
        | none => "none"
      let agrees := (lz.isSome == e.derivable) && (sr.isSome == e.derivable) && (dec == e.derivable)
      IO.println s!"{e.name}\t{if e.derivable then "derivable" else "not derivable"}\tlazy: {show1 lz}\tsearch: {show1 sr}\tdecided: {dec}\t{if agrees then "agrees" else "DISAGREES"}"
    return 0
  | ["model", fam, n] =>
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) =>
      let t₀ ← IO.monoMsNow
      let out := refuteBy Γ
      IO.println s!"{fam} {n}: {match out with | some z => s!"refuted in ℤ/{z.k + 1}" | none => "none"}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      match out with
      | some z =>
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_model.lean"
          s!"import MALL.Corpus.Basic\nimport MALL.ModelRun\nopen MALL MALL.Corpus\n\ntheorem fact : ¬ Derivable (Corpus.{fam} {n}) :=\n  noDerivableBy.verdict _ ({showFlat z})\n"
      | none => pure ()
      return 0
  | "refute" :: fam :: n :: opts =>
    -- The producer of saturated sets on a member of a family, with the
    -- times of the compiled checks; `--lists` also runs the check of the
    -- set as lists (`refutedBy`), whose time doubles with each formula
    -- beside a ⊗, and writes the set in that form.
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) =>
      let t₀ ← IO.monoNanosNow
      match ← IO.lazyPure (fun _ => refuteSet Γ) with
      | none => IO.println s!"{fam} {n}: none"; return 0
      | some D =>
        let count := D.length
        let t₁ ← IO.monoNanosNow
        let C ← IO.lazyPure fun _ => Encode.encode D Γ
        let k := C.tree.keys.length
        let t₂ ← IO.monoNanosNow
        let ok ← IO.lazyPure fun _ => codeRefutes C Γ
        let t₃ ← IO.monoNanosNow
        IO.println s!"{fam} {n}: a set of {count} ({k} numbers, a table of {C.table.length}, \
base {C.B}); found in {(t₁ - t₀) / 1000} µs; written in numbers in {(t₂ - t₁) / 1000} µs; \
the check in numbers: {ok}, {(t₃ - t₂) / 1000} µs"
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_set.lean"
          s!"import MALL.Corpus.Basic\nimport MALL.SatRun\nopen MALL MALL.Corpus\n\n\
set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n\
theorem fact : ¬ Derivable (Corpus.{fam} {n}) :=\n  noDerivableByCode.verdict _\n  {Encode.showCert C}\n"
        if opts.contains "--lists" then
          let t₄ ← IO.monoNanosNow
          let ok' ← IO.lazyPure fun _ => refutedBy D Γ
          let t₅ ← IO.monoNanosNow
          IO.println s!"{fam} {n}: the check of the set as lists: {ok'}, {(t₅ - t₄) / 1000} µs"
          IO.FS.writeFile s!"Corpus/out/{fam}_{n}_lists.lean"
            s!"import MALL.Corpus.Basic\nimport MALL.SatRun\nopen MALL MALL.Corpus\n\n\
set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n\
theorem fact : ¬ Derivable (Corpus.{fam} {n}) :=\n  noDerivableBySet.verdict _ ({showFlat D})\n"
        if opts.contains "--phases" then
          IO.println s!"phases: {(Table.ofSet D).card}"
        return 0
  | ["countermodel", name] =>
    match entries.find? (·.name == name) with
    | none => IO.eprintln s!"no entry {name}"; return 2
    | some e => IO.println (describeCountermodel e.seq); return 0
  | [cmd, prod, fam, n] =>
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) =>
      let t₀ ← IO.monoMsNow
      let out := produceBy prod Γ
      let (kind, sz, dp) := match out with
        | some c => ("pass", certSize c, certDepth c)
        | none => ("none", 0, 0)
      -- force the work before the clock is read again
      IO.println s!"{fam} {n}: {kind}, size {sz}, depth {dp}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      if cmd == "cert" then
        match out with
        | some c =>
          IO.FS.writeFile s!"Corpus/out/{fam}_{n}_{prod}.lean"
            s!"import MALL.Corpus.Basic\nopen MALL MALL.Corpus\n\nset_option maxRecDepth 100000 in\ndef fact : Fam (Corpus.{fam} {n}) :=\n  treeCert.verdict _ ({showRepr c})\n"
        | none => pure ()
      return 0
  | _ =>
    IO.eprintln "usage: mallrun facts | status | run <producer> <family> <n> | cert <producer> <family> <n> | model <family> <n> | refute <family> <n> | countermodel <name> | prove [options] '<sequent>' | corpus | show <family> <n>"
    return 2
