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

    dillrun prove [--ascii] [--short] [--budget=<n>] '<sequent>'
                                        a sequent typed in (the syntax is in
                                        `DILL/Parse.lean`: `. ; p, p -o q => q`):
                                        `derivable` with its tree, `not
                                        derivable` with a saturated set, or
                                        `flag`.  What is printed is a Lean
                                        file, for the kernel to check; with
                                        `--short` the first line only.  The
                                        exit code is 0, 1 or 3 for the three
                                        answers, 2 for a text not read

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

/-- The fact that a tree gives, as a Lean file. -/
def proveYes (j : Seq) (c : Cert S) : String :=
  "import DILL.Corpus.Basic\nopen DILL DILL.Corpus ProofTools.Explore\n\n" ++
  "set_option maxRecDepth 100000 in\n" ++
  s!"example : Fam true ({seqSrc j}) :=\n  treeCert.verdict _ ({certSrc c})"

/-- The fact that a saturated set gives, as a Lean file. -/
def proveNo (j : Seq) (D : List Seq) : String :=
  "import DILL.SatRun\nopen DILL\n" ++
  "abbrev p : Form := .atom 0\nabbrev q : Form := .atom 1\n" ++
  "abbrev r : Form := .atom 2\nabbrev s : Form := .atom 3\n\n" ++
  "set_option maxRecDepth 100000 in\n" ++
  s!"example : Derivable ({Refute.srcSeq j}) → False :=\n  noDerivableBySet.verdict _\n    [" ++
  ",\n     ".intercalate (D.map Refute.srcSeq) ++ "]"

/-- `dillrun prove`: the answer for a sequent typed in. -/
def prove (args : List String) : IO UInt32 := do
  let ascii := args.contains "--ascii"
  let short := args.contains "--short"
  let maxB := match args.find? (·.startsWith "--budget=") with
    | some a => (a.drop 9).toNat!
    | none => 4
  let text := " ".intercalate (args.filter fun a => !a.startsWith "--")
  if text.all Char.isWhitespace then
    IO.eprintln "usage: dillrun prove [--ascii] [--short] [--budget=<n>] '<sequent>'    e.g.  dillrun prove '. ; p, p -o q => q'"
    return 2
  match Parse.seq text with
  | .error e => IO.eprintln s!"not read: {e}"; return 2
  | .ok j =>
    let shown := if ascii then Parse.asciiSeq j else showSeq j
    let f := find (cfgOf "focus" 200000) j maxB
    match f.tree with
    | some (b, c) =>
      IO.println s!"-- derivable: {shown}"
      if !short then
        IO.println s!"-- A derivation of {certSize c} moves, found with {b} copies allowed along a branch."
        IO.println "-- This text is a Lean file: the kernel checks the derivation when it is elaborated."
        IO.println (proveYes j c)
      return 0
    | none =>
      let searched := (cell f maxB).replace "flag: " ""
      let flag (why : String) : IO UInt32 := do
        IO.println s!"-- flag: {shown}"
        if !short then
          IO.println s!"-- The search for a derivation: {searched}."
          IO.println s!"-- No certificate that there is none: {why}."
        return 3
      match Refute.outcome j with
      | .refuted D =>
        IO.println s!"-- not derivable: {shown}"
        if !short then
          IO.println s!"-- A saturated set of {D.length} sequents of which it is a member."
          IO.println "-- This text is a Lean file: the kernel checks the set when it is elaborated."
          IO.println (proveNo j D)
        return 1
      | .noSet why => flag why
      | .derivable => flag "the search for a set met a derivation, of which it keeps no tree; a larger --budget may find it"
      | .defect _ => flag "DEFECT: the set that was made does not check"

def main (args : List String) : IO UInt32 := do
  match args with
  | "prove" :: rest => prove rest
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
    IO.eprintln "usage: dillrun prove [--ascii] [--short] [--budget=<n>] '<sequent>' | status [<budget> [<cap>]] | facts [<budget> [<cap>]] | tree <name> [<budget>] | run <mode> <family> <n> <budget> | cert <mode> <family> <n> <budget> | fuzz <count> <size> <seed> [<budget>]"
    return 2
