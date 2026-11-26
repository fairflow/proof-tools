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

`<producer>` is `lazy` (the search by lazy splitting) or `search` (the
proved search).  Not trusted.  What it prints is checked by the kernel
when the file it wrote is elaborated.
-/
import MALL.Corpus.Basic
import MALL.ModelRun
import MALL.Refute

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
  | ["refute", fam, n] =>
    let n := n.toNat!
    match family fam n with
    | none => IO.eprintln s!"no family {fam}"; return 2
    | some (Γ, _) =>
      let t₀ ← IO.monoMsNow
      let out := refuteSet Γ
      IO.println s!"{fam} {n}: {match out with | some D => s!"a set of {D.length}" | none => "none"}"
      let t₁ ← IO.monoMsNow
      IO.println s!"producer ms: {t₁ - t₀}"
      match out with
      | some D =>
        let ok := refutedBy D Γ
        IO.println s!"check: {ok}"
        let t₂ ← IO.monoMsNow
        IO.println s!"check ms: {t₂ - t₁}"
        IO.println s!"phases: {(Table.ofSet D).card}"
        IO.FS.writeFile s!"Corpus/out/{fam}_{n}_set.lean"
          s!"import MALL.Corpus.Basic\nimport MALL.SatRun\nopen MALL MALL.Corpus\n\nset_option maxRecDepth 100000 in\ntheorem fact : ¬ Derivable (Corpus.{fam} {n}) :=\n  noDerivableBySet.verdict _ ({showFlat D})\n"
      | none => pure ()
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
    IO.eprintln "usage: mallrun facts | status | run <producer> <family> <n> | cert <producer> <family> <n> | model <family> <n> | refute <family> <n> | countermodel <name>"
    return 2
