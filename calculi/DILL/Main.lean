/-
`dillrun`: the producer of the Run stage ("yes" side), compiled.

    dillrun status [<budget> [<cap>]]   one row for each entry of the corpus:
                                        the least budget at which the search
                                        finds a tree that checks, or `flag`
    dillrun facts [<budget> [<cap>]]    the facts file, for the corpus
    dillrun tree <name> [<budget>]      an entry: its tree, as Lean source
    dillrun run <mode> <family> <n> <budget>
                                        one member of a family: the verdict,
                                        the size of the tree, the times
    dillrun cert <mode> <family> <n> <budget>
                                        the same, and Lean files that state
                                        the fact with its tree, and with its
                                        script (in `Corpus/out/run/`); and,
                                        where the unrestricted zone is empty
                                        and there is no `!`, a file in which
                                        the kernel runs the proved search of
                                        `DILL/Decide.lean`

    dillrun prove [--ascii] [--short] [--budget=<n>] [--deadline=<s>] '<sequent>'
                                        a sequent typed in (the syntax is in
                                        `DILL/Parse.lean`: `. ; p, p -o q => q`):
                                        `derivable` with its tree, `not
                                        derivable` with a saturated set, or
                                        `flag`.  What is printed is a Lean
                                        file, for the kernel to check: the
                                        facts as named declarations, and the
                                        bound on axioms; with `--short` the
                                        first line only.  The exit code is 0,
                                        1 or 3 for the three answers, 2 for a
                                        text not read (reported on the error
                                        stream, with a mark under the place).
                                        The search for a derivation has the
                                        budget (4) and a cap on its calls; the
                                        search for a set has neither, so the
                                        whole has a deadline (10 s): past it
                                        the answer is `flag`

    dillrun corpus                      the corpus as texts, a line for each
                                        entry: its name, its recorded status,
                                        and the sequent three times (in the
                                        source's notation, as Lean source,
                                        with the signs of a keyboard), with
                                        tabs between.  `Corpus/prove_corpus.py`
                                        gives each text to `dillrun prove`

    dillrun fuzz <count> <size> <seed> [<budget>]
                                        a test of the search itself: <count>
                                        sequents made at random, of at most
                                        <size> signs, each searched in both
                                        modes and, where it applies, decided;
                                        the disagreements are printed

`<mode>` is `focus` (the left rules chained: the default of the search)
or `plain` (the left rules as the figure has them).  `<budget>` is the
number of copies allowed along a branch; `status` and `facts` try each
budget from 0 to the one given (default 4).  `<cap>` is a cap on the
calls of the search at each budget (default 200000; 0 is none).

Not trusted.  What it prints is checked by the kernel when the file it
wrote is elaborated.  A sequent for which nothing is found is a `flag`:
the search is for the "yes" side only.
-/
import DILL.Corpus.Basic
import DILL.Decide
import DILL.Refute
import DILL.Parse

open DILL DILL.Run DILL.Corpus ProofTools ProofTools.Explore

def cfgOf (mode : String) (cap : Nat) : Lazy.Cfg := { focus := mode != "plain", maxCalls := cap }

/-- What the search did for a sequent, over the budgets `0 … maxB`. -/
structure Found where
  /-- The least budget with a tree that checks, and the tree. -/
  tree : Option (Nat × Cert S)
  /-- The run at that budget, or at `maxB`. -/
  stats : Lazy.Stats
  /-- The calls of the search over all the budgets tried. -/
  total : Nat
  /-- The search returned a tree that the checker refused. -/
  defect : Bool

instance : Inhabited Found := ⟨⟨none, {}, 0, false⟩⟩

/-- The budgets `b, b + 1, …, maxB` in turn. -/
partial def findFrom (cfg : Lazy.Cfg) (j : Seq) (maxB b total : Nat) (defect : Bool) : Found :=
  let (out, st, bad) := proveLazyWith cfg j b
  match out with
  | some c => ⟨some (b, c), st, total + st.calls, defect || bad⟩
  | none =>
    -- no copy refused and no cap reached: a larger budget finds no more
    if b ≥ maxB || (st.cuts == 0 && !st.capped) then ⟨none, st, total + st.calls, defect || bad⟩
    else findFrom cfg j maxB (b + 1) (total + st.calls) (defect || bad)

def find (cfg : Lazy.Cfg) (j : Seq) (maxB : Nat) : Found := findFrom cfg j maxB 0 0 false

/-- A cell of the status table. -/
def cell (f : Found) (maxB : Nat) : String :=
  (match f.tree with
  | some (b, c) =>
    s!"budget {b}: {certSize c} moves, nesting {certDepth c}, {f.total} calls"
  | none =>
    if f.stats.cuts == 0 && !f.stats.capped then
      s!"flag: nothing, and no copy refused ({f.total} calls)"
    else if f.stats.capped then
      s!"flag: the cap on calls reached at budget ≤ {maxB} ({f.total} calls)"
    else s!"flag: nothing to budget {maxB} ({f.total} calls, {f.stats.cuts} copies refused at {maxB})")
  ++ (if f.defect then " DEFECT: a tree did not check" else "")

/-- The decision of `DILL/Decide.lean`, where it applies and is small: an
empty unrestricted zone and no `!`. -/
def decided (j : Seq) : Option Bool :=
  if j.unr.isEmpty && (j.goal :: j.lin).all Form.bangFree && ssize j.lin + j.goal.size ≤ 14 then
    some (Dec.searchCF j.lin j.goal).isSome
  else none

def header : String :=
"/-
The facts of the corpus: for each entry that the search derives, the
derivation, by the tree of moves that the search found.  Written by
`dillrun facts` (`Main.lean`); do not edit.  The kernel checks each tree
when this file is elaborated.  An entry with no fact is a comment: the
search is for derivations only, and what it does not find is a flag.
-/
import DILL.Corpus.Basic

namespace DILL.Corpus.Facts

open DILL DILL.Corpus ProofTools.Explore

"

def factFile (stmt : String) (body : String) : String :=
  "import DILL.Corpus.Basic\nopen DILL DILL.Corpus ProofTools.Explore\n\n" ++
  "set_option maxRecDepth 100000 in\n" ++
  s!"def fact : Fam true ({stmt}) :=\n  {body}\n"

/-- A script as Lean source. -/
def scriptSrc (ls : Script S) : String :=
  "[" ++ ", ".intercalate (ls.map fun l =>
    let ms := l.move.src
    s!"⟨{l.goal}, ." ++ ms ++ "⟩") ++ "]"

/-- The script of the derivation that a tree is, where the tree checks. -/
def scriptOf (j : Seq) (c : Cert S) : Option (Script S) :=
  if h : Cert.check j c = true then some (Der.ofCert j c h).script else none

def natArg (as : List String) (i dflt : Nat) : Nat :=
  match as[i]? with
  | some a => a.toNat!
  | none => dflt

/-! ## Sequents made at random, to test the search against itself -/

instance : Inhabited Form := ⟨.one⟩

def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- A formula of at most `bd` signs over the letters `p q`, and the next
seed.  `bang` allows `!`. -/
partial def genForm (bang : Bool) : (bd : Nat) → (seed : Nat) → Form × Nat
  | 0, seed | 1, seed =>
    let seed := lcg seed
    let k := (seed / 65536) % 10
    (if k < 4 then .atom 0 else if k < 8 then .atom 1 else if k == 8 then .one
      else if (seed / 1048576) % 2 == 0 then .top else .zero, seed)
  | bd + 2, seed =>
    let seed := lcg seed
    let k := (seed / 65536) % (if bang then 12 else 10)
    if k < 1 then genForm bang 1 seed
    else if k ≥ 10 then
      let (A, seed) := genForm bang (bd + 1) seed
      (.bang A, seed)
    else
      let seed := lcg seed
      let l := (seed / 65536) % (bd + 1)
      let (A, seed) := genForm bang (l + 1) seed
      let (B, seed) := genForm bang (bd + 1 - l) seed
      ((if k < 4 then .lolli A B else if k < 6 then .tensor A B else if k < 8 then .wth A B
        else .plus A B), seed)

/-- A sequent of at most about `bd` signs, and the next seed. -/
def genSeq (bd seed : Nat) : Seq × Nat :=
  let seed := lcg seed
  let bang := (seed / 65536) % 3 != 0
  let seed := lcg seed
  let nlin := (seed / 65536) % 3 + (if bd > 6 then 1 else 0)
  let seed := lcg seed
  let nunr := if bang && (seed / 65536) % 4 == 0 then 1 else 0
  let parts := nlin + nunr + 1
  let each := max 1 (bd / parts)
  let (goal, seed) := genForm bang each seed
  let (lin, seed) := (List.range nlin).foldl (fun (acc : List Form × Nat) _ =>
    let (A, seed) := genForm bang each acc.2
    (A :: acc.1, seed)) ([], seed)
  let (unr, seed) := (List.range nunr).foldl (fun (acc : List Form × Nat) _ =>
    let (A, seed) := genForm bang each acc.2
    (A :: acc.1, seed)) ([], seed)
  (unr ⨾ lin ⟹ goal, seed)

/-! ## A sequent typed in -/

/-- The atoms of a formula. -/
def formAtoms : Form → List Nat
  | .atom n => [n]
  | .one | .top | .zero => []
  | .tensor A B | .lolli A B | .wth A B | .plus A B => formAtoms A ++ formAtoms B
  | .bang A => formAtoms A

/-- The number of signs of a sequent. -/
def seqSize (j : Seq) : Nat := ssize j.unr + ssize j.lin + j.goal.size

/-- The two options that lift Lean's limits, for a large answer. -/
def liftLimits (large : Bool) : String :=
  if large then "
-- The terms below are large: Lean's limits on the depth of recursion and
-- on its own work are lifted for this file.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
" else ""

/-- The head of the file `dillrun prove` prints, after its first line: a
comment (with `how`, what was found and at what budget), the import, a
name for each of the atoms `p q r s` that the sequent or its certificate
has, the options where the answer is large, and the sequent. -/
def proveHead (j : Seq) (others : List Seq) (how : String) (large : Bool) : String :=
  let atoms := (j :: others).flatMap fun k => (k.goal :: k.unr ++ k.lin).flatMap formAtoms
  let names := ((List.range 4).filter atoms.contains).map fun n =>
    s!"abbrev {atomName n} : Form := .atom {n}\n"
  s!"/-
Written by `dillrun prove` (`Main.lean`) for a sequent typed at a shell.
{how}
The program is not trusted.  The kernel checks the certificate below when
this file is elaborated, in `calculi/DILL`: `lake env lean <file>`.
-/
import DILL.Engine

namespace DILL.Answer

open DILL ProofTools.Explore

" ++ String.join names ++ liftLimits large ++ s!"
/-- The sequent, as it was read. -/
def sequent : Seq := {seqSrc j}
"

def proveFoot : String :=
  "\nend DILL.Answer\n\n#axioms_within_file [propext, Quot.sound]\n"

/-- The facts that a tree gives, as a Lean file. -/
def proveYes (j : Seq) (b : Nat) (c : Cert S) : String :=
  let large := certSize c > 150 || certDepth c > 40 || seqSize j > 150
  proveHead j []
    s!"A derivation of {certSize c} moves, found with {b} {if b == 1 then "copy" else "copies"} allowed along a branch." large ++ s!"
/-- A derivation, with the two cuts allowed (the tree has none): the
kernel checks the tree of moves. -/
def derivation : Fam true sequent :=
  treeCert.verdict _ ({certSrc c})

theorem derivable : Derivable sequent := ⟨derivation⟩

/-- By soundness: true in every phase model. -/
theorem valid : Valid sequent := soundness _ derivable
" ++ proveFoot

/-- The facts that a saturated set gives, as a Lean file. -/
def proveNo (j : Seq) (D : List Seq) : String :=
  let large := D.length > 60 || (D.map seqSize).sum > 1500 || seqSize j > 150
  proveHead j D
    (s!"A saturated set of {D.length} {if D.length == 1 then "sequent" else "sequents"}, of which it is a member." ++
      (if D.length > 200 then "\nA set of this size: the compiled check has passed it; the kernel's check of\na set of 499 sequents did not end in 120 s (`campaign/measurements-sat.md`)." else ""))
    large ++ s!"
/-- A set of sequents that is saturated: of each rule of the figure that
could end in a member, one premise is a member.  The sequent is a member. -/
def saturated : List Seq :=
  [" ++ ",\n   ".intercalate (D.map Refute.srcSeq) ++ "]

/-- The kernel computes the check, once: the sequent is a member of the
set, and the set is saturated.  (Stated through the certifier's check:
stated of `refutedBy` itself, the kernel's run on a set of 200 sequents
passed 8 GB.) -/
theorem checked : noCFBySet.check sequent saturated = true := by decide +kernel

/-- No derivation without cut. -/
theorem notCutFree : ¬ CFDerivable sequent := noCFBySet.verdict _ saturated checked

/-- By cut elimination: no derivation with the cuts either. -/
theorem notDerivable : ¬ Derivable sequent := noDerivableBySet.verdict _ saturated checked

/-- By completeness: false in some phase model. -/
theorem notValid : ¬ Valid sequent := fun h => notDerivable ((Sem.valid_iff_derivable _).mp h)
" ++ proveFoot

def proveUsage : String :=
  "usage: dillrun prove [--ascii] [--short] [--budget=<n>] [--deadline=<seconds>] '<sequent>'    e.g.  dillrun prove '. ; p, p -o q => q'"

/-- The answer for a sequent: the exit code, the verdict, and what is
printed after the first line.  The search for a derivation has a budget
and a cap on its calls; the search for a saturated set has neither, and
`prove` runs this under a deadline. -/
def answer (j : Seq) (maxB : Nat) : UInt32 × String × String :=
  let f := find (cfgOf "focus" 200000) j maxB
  match f.tree with
  | some (b, c) => (0, "derivable", proveYes j b c)
  | none =>
    let searched := (cell f maxB).replace "flag: " ""
    let flag (why : String) : UInt32 × String × String :=
      (3, "flag", s!"-- The search for a derivation: {searched}.\n-- No certificate that there is none: {why}.\n")
    match Refute.outcome j with
    | .refuted D => (1, "not derivable", proveNo j D)
    | .noSet why => flag why
    | .derivable => flag "the search for a set met a derivation, of which it keeps no tree; a larger --budget may find it"
    | .defect _ => flag "DEFECT: the set that was made does not check"

/-- Wait for a task until the deadline. -/
partial def await {α : Type} (t : Task α) (t₀ ms : Nat) : IO (Option α) := do
  if ← IO.hasFinished t then return some t.get
  if (← IO.monoMsNow) - t₀ ≥ ms then return none
  IO.sleep 5
  await t t₀ ms

/-- `dillrun prove`: the answer for a sequent typed in.  The text is the
arguments that are not options, joined by spaces. -/
def prove (args : List String) : IO UInt32 := do
  let ascii := args.contains "--ascii"
  let short := args.contains "--short"
  let mut maxB := 4
  let mut secs := 10
  for a in args do
    if a.startsWith "--budget=" then
      match (a.drop 9).toString.toNat? with
      | some n => maxB := n
      | none => IO.eprintln s!"dillrun prove: bad {a}\n{proveUsage}"; return 2
    else if a.startsWith "--deadline=" then
      match (a.drop 11).toString.toNat? with
      | some n => secs := n
      | none => IO.eprintln s!"dillrun prove: bad {a}\n{proveUsage}"; return 2
    else if a.startsWith "--" && a != "--ascii" && a != "--short" then
      IO.eprintln s!"dillrun prove: no option {a}\n{proveUsage}"; return 2
  let text := " ".intercalate (args.filter fun a => !a.startsWith "--")
  if text.all Char.isWhitespace then
    IO.eprintln proveUsage
    return 2
  let out ← IO.getStdout
  match Parse.seq text with
  | .error f => IO.eprintln s!"dillrun prove: {f.report text}"; return 2
  | .ok j =>
    let shown := if ascii then Parse.asciiSeq j else showSeq j
    let t₀ ← IO.monoMsNow
    let task := Task.spawn (prio := .dedicated) fun _ => answer j maxB
    match ← await task t₀ (secs * 1000) with
    | some (code, verdict, rest) =>
      IO.println s!"-- {verdict}: {shown}"
      unless short do IO.print rest
      out.flush
      return code
    | none =>
      IO.println s!"-- flag: {shown}"
      unless short do
        IO.println s!"-- No answer within {secs} s; a longer deadline: --deadline=<seconds>."
      out.flush
      -- the search is still running: leave without waiting for it
      IO.Process.exit 3

def main (args : List String) : IO UInt32 := do
  match args with
  | "prove" :: rest => prove rest
  | ["corpus"] =>
    for e in entries do
      IO.println s!"{e.name}\t{if e.derivable then "derivable" else "not derivable"}\t{showSeq e.seq}\t{seqSrc e.seq}\t{Parse.asciiSeq e.seq}"
    return 0
  | "status" :: rest =>
    let maxB := natArg rest 0 4
    let cap := natArg rest 1 200000
    IO.println "| entry | sequent | status | the search, left rules chained | the search, left rules as the figure has them | the decision without `!` | |"
    IO.println "|---|---|---|---|---|---|---|"
    let mut bad := 0
    for e in entries do
      let f := find (cfgOf "focus" cap) e.seq maxB
      let g := find (cfgOf "plain" cap) e.seq maxB
      let d := decided e.seq
      let dcell := match d with
        | some true => "a derivation"
        | some false => "none"
        | none => "not applicable"
      let ok := (!f.tree.isSome || e.derivable) && (!g.tree.isSome || e.derivable)
        && (match d with | some b => b == e.derivable | none => true)
        && !f.defect && !g.defect
      let note :=
        if !ok then "DISAGREES"
        else if e.derivable && f.tree.isNone then "flag (derivable, not found)"
        else if e.derivable then "agrees"
        else "flag, as expected"
      if !ok then bad := bad + 1
      IO.println s!"| {e.name} | `{showSeq e.seq}` | {if e.derivable then "derivable" else "not derivable"} | {cell f maxB} | {cell g maxB} | {dcell} | {note} |"
    IO.println s!"\n{entries.length} entries; {bad} where a producer disagrees with the status."
    return (if bad == 0 then 0 else 1)
  | "facts" :: rest =>
    let maxB := natArg rest 0 4
    let cap := natArg rest 1 200000
    IO.print header
    for e in entries do
      let f := find (cfgOf "focus" cap) e.seq maxB
      match f.tree with
      | some (_, c) =>
        IO.println s!"/-- `{showSeq e.seq}`: {e.why}. -/\ndef {e.name} : Fam true ({e.src}) :=\n  treeCert.verdict _ ({certSrc c})\n"
      | none => IO.println s!"-- {e.name}: `{showSeq e.seq}`: flag ({if e.derivable then "DERIVABLE by its status, and not found" else "not derivable, by its status"})\n"
    IO.println "end DILL.Corpus.Facts\n\n#axioms_within_file [propext, Quot.sound]"
    return 0
  | "tree" :: name :: rest =>
    let maxB := natArg rest 0 4
    match entries.find? (·.name == name) with
    | none => IO.eprintln s!"no entry {name}"; return 2
    | some e =>
      let f := find (cfgOf "focus" 200000) e.seq maxB
      match f.tree with
      | some (b, c) =>
        IO.println s!"-- {showSeq e.seq}: budget {b}, {certSize c} moves"
        IO.println s!"{e.src}"
        IO.println (certSrc c)
        match scriptOf e.seq c with
        | some ls => IO.println (scriptSrc ls)
        | none => IO.println "-- no script"
        return 0
      | none => IO.println s!"-- {showSeq e.seq}: {cell f maxB}"; return 0
  | "fuzz" :: count :: bd :: seed :: rest =>
    let maxB := natArg rest 0 3
    let cap := 20000
    let mut seed := seed.toNat!
    let mut found := 0
    let mut exhausted := 0
    let mut flagged := 0
    let mut decidedN := 0
    let mut bad := 0
    for _ in [0:count.toNat!] do
      let (j, seed') := genSeq bd.toNat! seed
      seed := seed'
      let f := find (cfgOf "focus" cap) j maxB
      let g := find (cfgOf "plain" cap) j maxB
      let d := decided j
      if d.isSome then decidedN := decidedN + 1
      let fEx := f.tree.isNone && f.stats.cuts == 0 && !f.stats.capped
      let gEx := g.tree.isNone && g.stats.cuts == 0 && !g.stats.capped
      if f.tree.isSome then found := found + 1
      else if fEx then exhausted := exhausted + 1
      else flagged := flagged + 1
      let mut why : List String := []
      if f.defect || g.defect then why := "a tree that the checker refused" :: why
      if f.tree.isSome && d == some false then why := "chained: a tree, and decided not derivable" :: why
      if g.tree.isSome && d == some false then why := "figure: a tree, and decided not derivable" :: why
      if fEx && d == some true then why := "chained: MISSED (decided derivable)" :: why
      if gEx && d == some true then why := "figure: MISSED (decided derivable)" :: why
      if f.tree.isSome && gEx then why := "figure: MISSED (chained finds a tree)" :: why
      if g.tree.isSome && fEx then why := "chained: MISSED (figure finds a tree)" :: why
      if g.tree.isSome && f.tree.isNone && !fEx && !f.stats.capped then
        why := "chained: not found to the budget, where figure finds a tree" :: why
      match f.tree, g.tree with
      | some (b, _), some (b', _) =>
        if b != b' then why := s!"budgets differ: chained {b}, figure {b'}" :: why
      | _, _ => pure ()
      if !why.isEmpty then
        bad := bad + 1
        IO.println s!"{showSeq j}    [{seqSrc j}]: {"; ".intercalate why}"
    IO.println s!"{count} sequents of size ≤ {bd}, budgets 0 to {maxB}, cap {cap} calls: chained search: {found} derived, {exhausted} nothing and no copy refused, {flagged} flagged at the budget or the cap; {decidedN} decided by the procedure without `!`; {bad} lines above."
    return 0
  | [cmd, mode, fam, n, b] =>
    let n := n.toNat!
    let b := b.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (j, derivable) =>
      if cmd == "cert" && j.unr.isEmpty && (j.goal :: j.lin).all Form.bangFree then
        -- the proved search of `DILL/Decide.lean`, for the kernel to run
        IO.FS.createDirAll "Corpus/out/run"
        IO.FS.writeFile s!"Corpus/out/run/{fam}_{n}_decide.lean"
          ("import DILL.Decide\nopen DILL DILL.Dec\n\n" ++
           "abbrev p : Form := .atom 0\nabbrev q : Form := .atom 1\n" ++
           "abbrev r : Form := .atom 2\nabbrev s : Form := .atom 3\n\n" ++
           "set_option maxRecDepth 100000 in\n" ++
           s!"example : {if derivable then "" else "¬ "}Nonempty (CF ({seqSrc j})) := by decide +kernel\n")
      let t₀ ← IO.monoNanosNow
      let (out, st) := Lazy.proveWith (cfgOf mode 0) j b
      let (kind, sz, dp, cp) := match out with
        | some c => ("pass", certSize c, certDepth c, certCopies c)
        | none => ("none", 0, 0, 0)
      -- printing forces the work before the clock is read again
      let stdout ← IO.getStdout
      IO.println s!"{fam} {n}: {kind}, size {sz}, depth {dp}, copies {cp}, calls {st.calls}, refused {st.cuts}"
      let t₁ ← IO.monoNanosNow
      IO.println s!"search us: {(t₁ - t₀) / 1000}"
      -- flushed: a run cut off in the check has still said what the search did
      stdout.flush
      let ok := match out with
        | some c => Cert.check j c
        | none => false
      IO.println s!"check: {ok}"
      let t₂ ← IO.monoNanosNow
      IO.println s!"check us: {(t₂ - t₁) / 1000}"
      stdout.flush
      if cmd == "cert" then
        match out with
        | some c =>
          if ok then
            IO.FS.createDirAll "Corpus/out/run"
            IO.FS.writeFile s!"Corpus/out/run/{fam}_{n}_{mode}_tree.lean"
              (factFile s!"Corpus.{fam} {n}" s!"treeCert.verdict _ ({certSrc c})")
            match scriptOf j c with
            | some ls =>
              IO.FS.writeFile s!"Corpus/out/run/{fam}_{n}_{mode}_script.lean"
                (factFile s!"Corpus.{fam} {n}" s!"scriptCert.verdict _ {scriptSrc ls}")
            | none => pure ()
        | none => pure ()
      return 0
  | _ =>
    IO.eprintln "usage: dillrun prove [--ascii] [--short] [--budget=<n>] [--deadline=<seconds>] '<sequent>' | corpus | status [<budget> [<cap>]] | facts [<budget> [<cap>]] | tree <name> [<budget>] | run <mode> <family> <n> <budget> | cert <mode> <family> <n> <budget> | fuzz <count> <size> <seed> [<budget>]"
    return 2
