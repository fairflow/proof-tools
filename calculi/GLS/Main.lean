/-
`glsrun`: the producer of the Run stage, compiled.

    glsrun facts                 the facts file, for the corpus
    glsrun status                one line for each entry of the corpus
    glsrun run <family> <n>      one member of a family: the verdict, the
                                 size of the certificate, the time
    glsrun cert <family> <n>     the same, and a Lean file that states the
                                 fact with its certificate
    glsrun setcert <family> <n>  the same by the search over sets
    glsrun prove '<sequent>'     a sequent typed at a shell: the verdict and
                                 the sequent as it was read, then a Lean
                                 file that states the fact with its
                                 certificate.  `--short`: the first line
                                 only.  `--ascii`: the sequent in it with
                                 the signs of a keyboard.  `--deadline=N`:
                                 the seconds the search may take (10).
                                 `--proved`: the answer of the proved
                                 search, and not of the search over sets.
                                 Exit code: 0 derivable, 1 not derivable,
                                 3 flag, 2 a text that is not a sequent
    glsrun corpus                the corpus as texts: name, status, the
                                 sequent in the source's notation, as Lean
                                 source, with the signs of a keyboard
    glsrun families              the same for some members of the families

Not trusted.  What it prints is checked by the kernel when the file it
wrote is elaborated.
-/
import GLS.Corpus.Basic
import GLS.SetSearch
import GLS.Parse
import GLS.FastCheck

open GLS GLS.Corpus ProofTools ProofTools.Explore

/-- The number of moves of a tree of moves. -/
partial def certSize : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certSize x.2).sum

def showRepr {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100

/-- On one line: a structure instance printed over several lines by `Repr`
is not always read back by Lean (an argument on a new line at the column
of its field). -/
def showFlat {α : Type} [Repr α] (x : α) : String := (repr x).pretty 1000000000

/-- The fact for an entry, as a Lean declaration. -/
def fact (name src : String) (s : Seq) : String :=
  match produce s 0 with
  | .pass _ =>
    match prove? s with
    | some c => s!"def {name} : Fam ({src}) :=\n  treeCert.verdict _ ({showRepr c})\n"
    | none => s!"-- {name}: flag\n"
  | .fail t => s!"theorem {name} : ¬ Derivable ({src}) :=\n  noDerivable.verdict _ ({showRepr t})\n"
  | .flag => s!"-- {name}: flag\n"

def header : String :=
"/-
The facts of the corpus, each with its certificate.  Written by `glsrun
facts` (`Main.lean`); do not edit.  The kernel checks every certificate
when this file is elaborated: a tree of moves for a derivation in GLS, a
finite tree against derivability.
-/
import GLS.Corpus.Basic

namespace GLS.Corpus.Facts

open GLS GLS.Corpus

"

/-! ## `glsrun prove`: a sequent typed at a shell -/

/-- How deep a tree of moves nests. -/
partial def certDepth : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certDepth x.2).foldl max 0

/-- How deep a tree of worlds nests. -/
partial def treeDepth : Tree → Nat
  | .node _ ks => 1 + (ks.map treeDepth).foldl max 0

/-- The tree of moves can be replayed on multisets with no side of a
sequent longer than `cap`.  GLR on multisets doubles the boxed part of an
antecedent, and compiled code builds every sequent in full: beyond the cap
the derivation as data is not checked here, and so not stated. -/
partial def fits (cap : Nat) : Seq → Cert S → Bool
  | j, .node m cs =>
    match step m j with
    | .ok ps =>
      ps.length == cs.length && (ps.zip cs).all fun (q, c) =>
        q.ant.length ≤ cap && q.suc.length ≤ cap && fits cap q c.2
    | .error _ => false

/-- The cap of `fits`. -/
def multisetCap : Nat := 4096

/-- The options that lift Lean's two limits, for a file whose terms are
large. -/
def liftLimits (large : Bool) : String :=
  if large then "
-- The terms below are large: Lean's limits on the depth of recursion and
-- on its own work are lifted for this file.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
" else ""

/-- The head of the file `glsrun prove` prints, after its first line: the
imports, and a name for each of the variables `p q r s` that the sequent
has. -/
def proveHead (s : Seq) (large : Bool) : String :=
  let names := ((List.range 4).filter fun n => s.vars.contains n).map fun n =>
    s!"abbrev {varName n} : Form := .var {n}\n"
  "/-
Written by `glsrun prove` (`Main.lean`) for a sequent typed at a shell.
The program is not trusted.  The kernel checks the certificate below when
this file is elaborated, in `calculi/GLS`: `lake env lean <file>`.
-/
import GLS.SetSearch

namespace GLS.Answer

open GLS

" ++ String.join names ++ liftLimits large ++ s!"
/-- The sequent, as it was read. -/
def sequent : Seq := {s.src}
"

def proveFoot : String :=
  "\nend GLS.Answer\n\n#axioms_within_file [propext, Quot.sound]\n"

/-- A tree of moves or a sequent of this size has Lean's limits lifted. -/
def isLarge (s : Seq) (sz dp : Nat) : Bool := s.depth > 30 || sz > 200 || dp > 30

/-- The answer "derivable", with the derivation as data. -/
def derivableData (s : Seq) (c : Cert S) : UInt32 × String × String :=
  (0, "derivable", proveHead s (isLarge s (certSize c) (certDepth c)) ++ s!"
/-- A derivation in GLS, as data: the kernel checks the tree of moves. -/
def proof : Fam sequent :=
  treeCert.verdict _ ({showRepr c})

theorem derivable : Derivable sequent := ⟨proof⟩

/-- By soundness. -/
theorem valid : Valid sequent := soundness _ proof
" ++ proveFoot)

/-- The answer "derivable", with the proposition only: the tree of moves
is checked over sets. -/
def derivableProp (s : Seq) (c : Cert SS) : UInt32 × String × String :=
  (0, "derivable", proveHead s (isLarge s (certSize c) (certDepth c)) ++ s!"
-- The derivation is not stated as data: replayed on multisets, the tree
-- of moves below has a sequent with more than {multisetCap} formulas on a side
-- (GLR doubles the boxed part of an antecedent), and `glsrun` did not
-- check it there.  It is checked over sets, where a formula is kept once.

/-- There is a derivation in GLS: the kernel checks the tree of moves over
sets. -/
theorem derivable : Derivable sequent :=
  setCert.verdict _ ({showRepr c})

/-- By soundness. -/
theorem valid : Valid sequent := Nonempty.elim derivable (soundness _)
" ++ proveFoot)

/-- The answer "not derivable". -/
def notDerivable (s : Seq) (t : Tree) : UInt32 × String × String :=
  (1, "not derivable", proveHead s (isLarge s (nodes t) (treeDepth t)) ++ s!"
/-- A finite tree: at each node the variables true there, by their
numbers, and the node's children.  The sequent is false at its root: every
formula of the antecedent is true there and none of the succedent. -/
def countermodel : Tree :=
  {showRepr t}

/-- The kernel computes that the sequent is false at the root of the
tree, which is a world of a finite two-valued model of GL. -/
theorem notValid : ¬ Valid sequent := noValid.verdict _ countermodel

/-- By soundness. -/
theorem notDerivable : ¬ Derivable sequent := noDerivable.verdict _ countermodel
" ++ proveFoot)

/-- The answer of the proved search, checked.  It is used where an answer
of the search over sets did not pass its check. -/
def answerProved (s : Seq) : UInt32 × String × String :=
  match proofOrRef s with
  | .inl d =>
    let c := d.toCert
    if treeCert.check s c then derivableData s c
    else (3, "flag", "-- the search's tree of moves did not pass the check: a defect of `glsrun`\n")
  | .inr r =>
    if FastCheck.refuted s r.1 then notDerivable s r.1
    else (3, "flag", "-- the search's tree did not pass the check against derivability: a defect of `glsrun`\n")

/-- The answer for a sequent: the exit code, the verdict, and the rest of
the file.  The search over sets answers first; what it returns is checked
here before it is printed, and an answer that does not pass is replaced by
that of the proved search.  A tree of worlds is checked by the table of
`GLS/FastCheck.lean`, and not by the certifier's own check, which the
kernel runs fast and compiled code does not. -/
def answer (s : Seq) : UInt32 × String × String :=
  match produceSet s with
  | some (.inl c) =>
    if fits multisetCap s c && treeCert.check s c then derivableData s c
    else if setCert.check s c then derivableProp s c
    else answerProved s
  | some (.inr t) => if FastCheck.refuted s t then notDerivable s t else answerProved s
  | none => answerProved s

/-- Wait for a task until the deadline. -/
partial def await {α : Type} (t : Task α) (t₀ ms : Nat) : IO (Option α) := do
  if ← IO.hasFinished t then return some t.get
  if (← IO.monoMsNow) - t₀ ≥ ms then return none
  IO.sleep 5
  await t t₀ ms

/-- `glsrun prove`: the arguments after the word.  The text is the
arguments that are not options, joined by spaces. -/
def prove (args : List String) : IO UInt32 := do
  let usage := "usage: glsrun prove [--short] [--ascii] [--proved] [--deadline=N] '<sequent>'    \
e.g.  glsrun prove '[]([]p -> p) -> []p'"
  let short := args.contains "--short"
  let ascii := args.contains "--ascii"
  let proved := args.contains "--proved"
  let mut secs := 10
  for a in args do
    if a.startsWith "--deadline=" then
      match (a.drop 11).toString.toNat? with
      | some n => secs := n
      | none => IO.eprintln s!"glsrun prove: bad {a}\n{usage}"; return 2
  let texts := args.filter fun a => !(a == "--short" || a == "--ascii" || a == "--proved" || a.startsWith "--deadline=")
  if texts.isEmpty then
    IO.eprintln usage
    return 2
  let text := " ".intercalate texts
  match Parse.parseSeq text with
  | .error f => IO.eprintln s!"glsrun prove: {f.report text}"; return 2
  | .ok s =>
    let shown := if ascii then s.ascii else s.show
    let t₀ ← IO.monoMsNow
    let task := Task.spawn (prio := .dedicated) fun _ =>
      let (code, verdict, rest) := if proved then answerProved s else answer s
      -- the length is asked for so that the text is built inside the task
      (code, verdict, rest, rest.length)
    let out ← IO.getStdout
    match ← await task t₀ (secs * 1000) with
    | some (code, verdict, rest, _) =>
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

/-- Members of the families, for `glsrun families`: with the corpus they
give each kind of answer. -/
def familyMembers : List (String × Nat) :=
  [("boxChain", 3), ("boxChain", 8), ("boxChain", 32), ("kChain", 4), ("kChain", 12),
   ("consis", 3), ("consis", 32), ("binTree", 2), ("binTree", 4)]

def main (args : List String) : IO UInt32 := do
  match args with
  | "prove" :: rest => prove rest
  | ["corpus"] =>
    for e in entries do
      IO.println s!"{e.name}\t{if e.valid then "derivable" else "not derivable"}\t{e.seq.show}\t{e.seq.src}\t{e.seq.ascii}"
    return 0
  | ["families"] =>
    for (fam, n) in familyMembers do
      match family fam n with
      | some (s, v) =>
        IO.println s!"{fam}_{n}\t{if v then "derivable" else "not derivable"}\t{s.show}\t{s.src}\t{s.ascii}"
      | none => pure ()
    return 0
  | ["facts"] =>
    IO.print header
    for e in entries do
      IO.println (fact e.name e.src e.seq)
    IO.println "end GLS.Corpus.Facts\n\n#axioms_within_file [propext, Quot.sound]"
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
      IO.println s!"{e.name}\t{if e.valid then "derivable" else "not derivable"}\t{got}\t{if agrees then "agrees" else "DISAGREES"}"
    return 0
  | ["setcert", fam, n] =>
    -- the search over sets: the verdict, the size, the time; and the facts
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (s, _) =>
      let t₀ ← IO.monoMsNow
      let out := produceSet s
      let (kind, sz) := match out with
        | some (.inl c) => ("pass", certSize c)
        | some (.inr t) => ("fail", nodes t)
        | none => ("flag", 0)
      IO.println s!"{fam} {n}: {kind}, size {sz}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      let src := s!"Corpus.{fam} {n}"
      let pre := "import GLS.Corpus.Basic\nimport GLS.SetSearch\nopen GLS GLS.Corpus\n\nset_option maxRecDepth 100000 in\n"
      match out with
      | some (.inl c) =>
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_set.lean"
          s!"{pre}theorem fact : Derivable ({src}) :=\n  setCert.verdict _ ({showRepr c})\n"
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_settree.lean"
          s!"{pre}def fact : Fam ({src}) :=\n  treeCert.verdict _ ({showRepr c})\n"
      | some (.inr t) =>
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_set.lean"
          s!"{pre}theorem fact : ¬ Derivable ({src}) :=\n  noDerivable.verdict _ ({showRepr t})\n"
      | none => pure ()
      return 0
  | [cmd, fam, n] =>
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (s, _) =>
      let t₀ ← IO.monoMsNow
      let out := match proofOrRef s with
        | .inl d => let c := d.toCert; (s!"pass", certSize c, some c, none)
        | .inr r => (s!"fail", nodes r.1, none, some r.1)
      let (kind, sz, c?, t?) := out
      -- force the work before the clock is read again
      IO.println s!"{fam} {n}: {kind}, size {sz}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      if cmd == "cert" then
        let src := s!"Corpus.{fam} {n}"
        let body := match c?, t? with
          | some c, _ => s!"set_option maxRecDepth 100000 in\ndef fact : Fam ({src}) :=\n  treeCert.verdict _ ({showRepr c})\n"
          | _, some t => s!"set_option maxRecDepth 100000 in\ntheorem fact : ¬ Derivable ({src}) :=\n  noDerivable.verdict _ ({showRepr t})\n"
          | _, _ => ""
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}.lean"
          s!"import GLS.Corpus.Basic\nopen GLS GLS.Corpus\n\n{body}"
        -- for a derivation, the same fact with its script
        match produce s 0 with
        | .pass ls =>
          IO.FS.writeFile s!"Corpus/out/{fam}_{n}_script.lean"
            s!"import GLS.Corpus.Basic\nopen GLS GLS.Corpus\n\nset_option maxRecDepth 100000 in\ndef fact : Fam ({src}) :=\n  scriptCert.verdict _ ({showFlat ls})\n"
        | _ => pure ()
      return 0
  | _ => IO.eprintln "usage: glsrun facts | status | corpus | families | run <family> <n> | cert <family> <n> | setcert <family> <n> | prove [--short] [--ascii] [--proved] [--deadline=N] '<sequent>'"; return 2
