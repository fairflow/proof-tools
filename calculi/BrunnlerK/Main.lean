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

/-- The depth of a tree of moves. -/
partial def certDepth : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certDepth x.2).foldl max 0

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

/-- The depth of a finite tree. -/
partial def treeDepth : Tree → Nat
  | .node _ ks => 1 + (ks.map treeDepth).foldl max 0

/-- Lean's two limits, lifted for a file whose terms are large or deep.
Without them a tree of 2 335 moves, and a sequent nested 256 deep, were
not elaborated; with them both were, in 17 s and 13 s.  Written only
where the sequent is nested more than 40 deep or the tree has more than
400 moves or is more than 40 deep: below that Lean's own limits serve. -/
def liftLimits (large : Bool) : String :=
  if large then "
-- The terms below are large: Lean's limits on the depth of recursion and
-- on its own work are lifted for this file.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
" else ""

/-- The head of the file `ksearch prove` prints, after its first line: the
imports, and a name for each of the propositions `p q r s a b c d` that
the sequent has. -/
def proveHead (Γ : NSeq) (large : Bool) : String :=
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

" ++ String.join names ++ liftLimits large ++ s!"
/-- The sequent, as it was read. -/
def sequent : NSeq := {Γ.src}
"

def proveFoot : String :=
  "\nend BrunnlerK.Answer\n\n#axioms_within_file [propext, Quot.sound]\n"

/-- The answer for a sequent: the exit code, the verdict, and the rest of
the file.  What the search returns is checked here before it is printed;
a certificate that did not pass would be a defect of the search, and the
answer is then `flag`. -/
def answer (Γ : NSeq) : UInt32 × String × String :=
  match search Γ with
  | .inl d =>
    let c := d.toCert
    if treeCert.check Γ c then
      let large := seqDepth Γ > 40 || certSize c > 400 || certDepth c > 40
      (0, "derivable", proveHead Γ large ++ s!"
/-- A proof in system K: the kernel checks the tree of moves. -/
def proof : K sequent :=
  treeCert.verdict _ ({showRepr c})

theorem derivable : Derivable sequent := ⟨proof⟩
" ++ proveFoot)
    else (3, "flag", "-- the search's tree of moves did not pass the check: a defect of `ksearch`\n")
  | .inr r =>
    if noDerivable.check Γ r.tree then
      (1, "not derivable", proveHead Γ (seqDepth Γ > 40 || treeDepth r.tree > 40) ++ s!"
/-- A finite tree: at each node the propositions true there, by their
numbers, and the node's children.  The sequent's formula is false at its
root. -/
def countermodel : Tree :=
  {showRepr r.tree}

/-- The kernel computes that the sequent's formula is false at the root
of the tree. -/
theorem notValid : ¬ Valid sequent := noValid.verdict _ countermodel

/-- By soundness. -/
theorem notDerivable : ¬ Derivable sequent := noDerivable.verdict _ countermodel
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
