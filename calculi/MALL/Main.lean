/-
`mallrun`: the producers of the Run stage, compiled.

    mallrun facts                      the facts file, for the corpus
    mallrun status                     one line for each entry of the corpus
    mallrun run <producer> <family> <n>   one member of a family: the
                                       verdict, the size of the tree, the time
    mallrun cert <producer> <family> <n>  the same, and a Lean file that
                                       states the fact with its tree

`<producer>` is `lazy` (the search by lazy splitting) or `search` (the
proved search).  Not trusted.  What it prints is checked by the kernel
when the file it wrote is elaborated.
-/
import MALL.Corpus.Basic

open MALL MALL.Corpus ProofTools ProofTools.Explore

/-- The number of moves of a tree of moves. -/
partial def certSize : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certSize x.2).sum

/-- The nesting of a tree of moves. -/
partial def certDepth : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certDepth x.2).foldl max 0

def showRepr {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100

/-- The fact for an entry, as a Lean declaration. -/
def fact (name src : String) (Γ : List Form) : String :=
  match proveLazy Γ with
  | some c => s!"def {name} : Fam {src} :=\n  treeCert.verdict _ ({showRepr c})\n"
  | none =>
    if noDerivable.check Γ () then
      s!"theorem {name} : ¬ Derivable {src} :=\n  noDerivable.verdict _ ()\n"
    else s!"-- {name}: flag\n"

def header : String :=
"/-
The facts of the corpus.  Written by `mallrun facts` (`Main.lean`); do not
edit.  The kernel checks each when this file is elaborated: for a
derivation, the tree of moves that the search by lazy splitting found;
against one, the decision procedure itself, which the kernel runs.
-/
import MALL.Corpus.Basic

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
    IO.eprintln "usage: mallrun facts | status | run <producer> <family> <n> | cert <producer> <family> <n>"
    return 2
