/-
`ksearch`: the producer of the Run stage, compiled.

    ksearch facts                 the facts file, for the corpus
    ksearch status                one line for each entry of the corpus
    ksearch run <family> <n>      one member of a family: the verdict, the
                                  size of the certificate, the time
    ksearch cert <family> <n>     the same, and a Lean file that states the
                                  fact with its certificate
    ksearch prove '<sequent>'     a sequent typed at a shell: the verdict and
                                  the sequent as it was read, then a Lean
                                  file that states the fact with its
                                  certificate.  `--short`: the first line
                                  only.  `--ascii`: the sequent in it with
                                  the signs of a keyboard.  `--deadline=N`:
                                  seconds, 10 if not given.  Exit code 0
                                  derivable, 1 not derivable, 3 flag, 2 a
                                  text that is not a sequent
                                  Above the sizes Lean was seen to check,
                                  the first line says that the answer
                                  rests on the program's check
    ksearch corpus                the corpus as texts: name, status, the
                                  sequent in the source's notation, as
                                  Lean source, and with the signs of a
                                  keyboard
    ksearch show <family> <n>     a member of a family, in the source's
                                  notation

Not trusted.  What it prints is checked by the kernel when the file it
wrote is elaborated.
-/
import BrunnlerK.Corpus.Basic
import BrunnlerK.Parse

open BrunnlerK BrunnlerK.Corpus ProofTools ProofTools.Explore

/-- The number of moves of a tree of moves. -/
partial def certSize : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certSize x.2).sum

def showRepr {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100

/-- The fact for an entry, as a Lean declaration. -/
def fact (name src : String) (Γ : NSeq) : String :=
  match produce Γ 0 with
  | .pass _ =>
    match prove? Γ with
    | some c => s!"def {name} : K ({src}) :=\n  treeCert.verdict _ ({showRepr c})\n"
    | none => s!"-- {name}: flag\n"
  | .fail t => s!"theorem {name} : ¬ Valid ({src}) :=\n  noValid.verdict _ ({showRepr t})\n"
  | .flag => s!"-- {name}: flag\n"

def header : String :=
"/-
The facts of the corpus, each with its certificate.  Written by `ksearch
facts` (`Main.lean`); do not edit.  The kernel checks every certificate
when this file is elaborated: a tree of moves for a proof in system K, a
finite tree against validity.
-/
import BrunnlerK.Corpus.Basic

namespace BrunnlerK.Corpus.Facts

open BrunnlerK BrunnlerK.Corpus

"

/-! ## A sequent typed at a shell -/

/-! The certificates as Lean source, written here and not by `Repr`.
`Repr` indents each line by the depth of its place in the term: for a
tree of 2 335 moves 82 of the 86 megabytes it wrote were indentation, and
for one of 8 767 moves it wrote 1.26 gigabytes.  These printers write a
node to a line, with the names as the file's `open BrunnlerK` resolves
them, onto the end of a text (which is then extended in place). -/

/-- A formula by its constructors. -/
def formSrc (acc : String) : Form → String
  | .atom n => acc ++ s!"(Form.atom {n})"
  | .natom n => acc ++ s!"(Form.natom {n})"
  | .or A B => formSrc (formSrc (acc ++ "(Form.or ") A ++ " ") B ++ ")"
  | .and A B => formSrc (formSrc (acc ++ "(Form.and ") A ++ " ") B ++ ")"
  | .dia A => formSrc (acc ++ "(Form.dia ") A ++ ")"
  | .box A => formSrc (acc ++ "(Form.box ") A ++ ")"

/-- A move by its constructor. -/
def moveSrc (acc : String) : Move → String
  | .ax a p => acc ++ s!"(Move.ax {a} {p})"
  | .and a A B => formSrc (formSrc (acc ++ s!"(Move.and {a} ") A ++ " ") B ++ ")"
  | .or a A B => formSrc (formSrc (acc ++ s!"(Move.or {a} ") A ++ " ") B ++ ")"
  | .box a A => formSrc (acc ++ s!"(Move.box {a} ") A ++ ")"
  | .dia a i A => formSrc (acc ++ s!"(Move.dia {a} {i} ") A ++ ")"

/-- A tree of moves, a move to a line. -/
partial def certSrc (acc : String) : Cert S → String
  | .node m cs =>
    let acc := moveSrc (acc ++ "\n (ProofTools.Zip.RTree.node ") m ++ " ["
    let out := cs.foldl (init := (acc, true)) fun (acc, first) x =>
      (certSrc (acc ++ (if first then "(()," else ", ((),")) x.2 ++ ")", false)
    out.1 ++ "])"

/-- A finite tree, a node to a line. -/
partial def treeSrc (acc : String) : Tree → String
  | .node v ks =>
    let acc := acc ++ s!"\n (Tree.node {v} ["
    let out := ks.foldl (init := (acc, true)) fun (acc, first) t =>
      (treeSrc (if first then acc else acc ++ ", ") t, false)
    out.1 ++ "])"

/-- Lean's two limits, lifted in every file the command prints.  Without
them a tree of 2 335 moves, and a sequent nested 256 deep, were not
elaborated; with them both were.  In every file, and not only for a large
answer: a threshold on the size of the answer has to guess which size
Lean's limits are met at, and a guess that is wrong refuses a file that
is right (so MALL found). -/
def liftLimits : String := "
-- Lean's limits on the depth of recursion and on its own work, lifted for
-- this file: the terms below may be large or deep.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
"

/-- The head of the file `ksearch prove` prints, after its first line: the
imports, and a name for each of the propositions `p q r s a b c d` that
the sequent has. -/
def proveHead (Γ : NSeq) : String :=
  let names := ((List.range 8).filter fun n => Γ.props.contains n).map fun n =>
    s!"abbrev {propName n} : Form := .atom {n}\n"
  "/-
Written by `ksearch prove` (`Main.lean`) for a sequent typed at a shell.
The program is not trusted.  The kernel checks the certificate below when
this file is elaborated, in `calculi/BrunnlerK`: `lake env lean <file>`.
-/
import BrunnlerK.Run
import BrunnlerK.Tactic

namespace BrunnlerK.Answer

open BrunnlerK

" ++ String.join names ++ liftLimits ++ s!"
/-- The sequent, as it was read. -/
def sequent : NSeq := {Γ.src}
"

def proveFoot : String :=
  "\nend BrunnlerK.Answer\n\n#axioms_within_file [propext, Quot.sound]\n"

/-- How deep the connectives of a formula are nested. -/
def formDepth : Form → Nat
  | .atom _ => 0
  | .natom _ => 0
  | .or A B => 1 + max (formDepth A) (formDepth B)
  | .and A B => 1 + max (formDepth A) (formDepth B)
  | .dia A => 1 + formDepth A
  | .box A => 1 + formDepth A

/-- How deep a sequent is nested: its boxes, and the formulas in them. -/
def seqDepth : NSeq → Nat
  | .leaf fs => (fs.map formDepth).foldl max 0
  | .cons Δ r => max (1 + seqDepth Δ) (seqDepth r)

/-! The largest answers Lean was seen to check, each file under a cap of
8 GB on memory and within 240 s (`Corpus/prove_families.py`; the table is
in `campaign/measurements-2026-11-23.md`, "`ksearch prove` beyond the
corpus").  The search prints in under a second certificates that Lean did
not check so: `boxAnd 96` (cut off at 240 s) and `nest 512` (stopped at
8 GB).  Beyond these three sizes the first line says that the answer
rests on the program's check; the file is printed all the same, and a
machine with more memory or time may check it. -/

/-- The deepest sequent seen checked with its tree of moves: `nest 384`.
(Depth is no measure on the other side: a move carries its formula, a
countermodel does not, and `chain 4096` was checked in seconds.) -/
def seenDepth : Nat := 385
/-- The longest tree of moves seen checked, in characters: `boxAnd 64`. -/
def seenMoves : Nat := 2600000
/-- The longest countermodel seen checked, in characters: `tree 16`. -/
def seenTree : Nat := 4500000

def unseen : String :=
  ", on the program's check (a certificate larger than any Lean was seen to check)"

/-- The answer for a sequent: the exit code, the verdict, and the rest of
the file.  What the search returns is checked here before it is printed;
a certificate that did not pass would be a defect of the search, and the
answer is then `flag`.

In the file the check is a theorem of its own (`checked`), stated through
the certifier and proved once by the kernel; each fact is `verdict` with
that theorem.  Left to its default argument, `verdict` would run the
check again for each fact. -/
def answer (Γ : NSeq) : UInt32 × String × String :=
  match search Γ with
  | .inl d =>
    let c := d.toCert
    if treeCert.check Γ c then
      let text := certSrc "" c
      let word := if seqDepth Γ > seenDepth || text.length > seenMoves then unseen else ""
      (0, "derivable" ++ word, proveHead Γ ++ s!"
/-- The certificate: a tree of moves, {certSize c} of them. -/
def moves : ProofTools.Explore.Cert S :={text}

/-- The kernel checks the tree of moves, once. -/
theorem checked : treeCert.check sequent moves = true := by decide +kernel

/-- A proof in system K, built from the tree of moves. -/
def proof : K sequent := treeCert.verdict _ moves checked

theorem derivable : Derivable sequent := ⟨proof⟩
" ++ proveFoot)
    else (3, "flag", "-- the search's tree of moves did not pass the check: a defect of `ksearch`\n")
  | .inr r =>
    if noDerivable.check Γ r.tree then
      let text := treeSrc "" r.tree
      let word := if text.length > seenTree then unseen else ""
      (1, "not derivable" ++ word, proveHead Γ ++ s!"
/-- The certificate: a finite tree of {nodes r.tree} nodes.  At each node
the propositions true there, by their numbers, and the node's children.
The sequent's formula is false at its root. -/
def countermodel : Tree :={text}

/-- The kernel computes that the sequent's formula is false at the root
of the tree, once. -/
theorem checked : noValid.check sequent countermodel = true := by decide +kernel

theorem notValid : ¬ Valid sequent := noValid.verdict _ countermodel checked

/-- By soundness; the check is the same one. -/
theorem notDerivable : ¬ Derivable sequent := noDerivable.verdict _ countermodel checked
" ++ proveFoot)
    else (3, "flag", "-- the search's tree did not pass the check against validity: a defect of `ksearch`\n")

/-- Wait for a task until the deadline. -/
partial def await {α : Type} (t : Task α) (t₀ ms : Nat) : IO (Option α) := do
  if ← IO.hasFinished t then return some t.get
  if (← IO.monoMsNow) - t₀ ≥ ms then return none
  IO.sleep 5
  await t t₀ ms

/-- `ksearch prove`: the arguments after the word.  The text is the
arguments that are not options, joined by spaces. -/
def prove (args : List String) : IO UInt32 := do
  let usage := "usage: ksearch prove [--short] [--ascii] [--deadline=N] '<sequent>'    \
e.g.  ksearch prove '[](a -> b) -> ([]a -> []b)'"
  let short := args.contains "--short"
  let ascii := args.contains "--ascii"
  let mut secs := 10
  for a in args do
    if a.startsWith "--deadline=" then
      match (a.drop 11).toString.toNat? with
      | some n => secs := n
      | none => IO.eprintln s!"ksearch prove: bad {a}\n{usage}"; return 2
  let texts := args.filter fun a => !(a == "--short" || a == "--ascii" || a.startsWith "--deadline=")
  if texts.isEmpty then
    IO.eprintln usage
    return 2
  let text := " ".intercalate texts
  match Parse.parseSeq text with
  | .error f => IO.eprintln s!"ksearch prove: {f.report text}"; return 2
  | .ok Γ =>
    let shown := if ascii then Γ.ascii else Γ.show
    let t₀ ← IO.monoMsNow
    let task := Task.spawn (prio := .dedicated) fun _ => answer Γ
    let out ← IO.getStdout
    match ← await task t₀ (secs * 1000) with
    | some (code, verdict, rest) =>
      IO.println s!"-- {verdict}: {shown}"
      unless short do IO.print rest
      out.flush
      return code
    | none =>
      IO.println s!"-- flag: {shown}"
      unless short do
        IO.println s!"-- no answer within {secs} s; a longer deadline: --deadline=N, in seconds"
      out.flush
      -- the search is still running: leave without waiting for it
      IO.Process.exit 3

def main (args : List String) : IO UInt32 := do
  match args with
  | "prove" :: rest => prove rest
  | ["corpus"] =>
    for e in entries do
      IO.println s!"{e.name}\t{if e.valid then "valid" else "not valid"}\t{e.seq.show}\t{e.seq.src}\t{e.seq.ascii}"
    return 0
  | ["show", fam, n] =>
    match family fam n.toNat! with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) => IO.println Γ.show; return 0
  | ["facts"] =>
    IO.print header
    for e in entries do
      IO.println (fact e.name e.src e.seq)
    IO.println "end BrunnlerK.Corpus.Facts\n\n#axioms_within_file [propext, Quot.sound]"
    return 0
  | ["status"] =>
    for e in entries do
      let got := match produce e.seq 0 with
        | .pass ls => s!"pass (a script of {ls.length} lines)"
        | .fail t => s!"fail (a tree of {nodes t} nodes)"
        | .flag => "flag"
      let agrees := match produce e.seq 0 with
        | .pass _ => e.valid
        | .fail _ => !e.valid
        | .flag => false
      IO.println s!"{e.name}\t{if e.valid then "valid" else "not valid"}\t{got}\t{if agrees then "agrees" else "DISAGREES"}"
    return 0
  | [cmd, fam, n] =>
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) =>
      let t₀ ← IO.monoMsNow
      let out := match search Γ with
        | .inl d => let c := d.toCert; (s!"pass", certSize c, some c, none)
        | .inr r => (s!"fail", nodes r.tree, none, some r.tree)
      let (kind, sz, c?, t?) := out
      -- force the work before the clock is read again
      IO.println s!"{fam} {n}: {kind}, size {sz}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      if cmd == "cert" then
        let src := s!"Corpus.{fam} {n}"
        let body := match c?, t? with
          | some c, _ => s!"def fact : K ({src}) :=\n  treeCert.verdict _ ({showRepr c})\n"
          | _, some t => s!"theorem fact : ¬ Valid ({src}) :=\n  noValid.verdict _ ({showRepr t})\n"
          | _, _ => ""
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}.lean"
          s!"import BrunnlerK.Corpus.Basic\nopen BrunnlerK BrunnlerK.Corpus\n\n{body}"
      return 0
  | _ => IO.eprintln "usage: ksearch facts | status | corpus | run <family> <n> | cert <family> <n> | show <family> <n> | prove [--short] [--ascii] [--deadline=N] '<sequent>'"; return 2
