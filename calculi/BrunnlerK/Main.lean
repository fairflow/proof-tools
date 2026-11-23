/-
`ksearch`: the producer of the Run stage, compiled.

    ksearch facts                 the facts file, for the corpus
    ksearch status                one line for each entry of the corpus
    ksearch run <family> <n>      one member of a family: the verdict, the
                                  size of the certificate, the time
    ksearch cert <family> <n>     the same, and a Lean file that states the
                                  fact with its certificate

Not trusted.  What it prints is checked by the kernel when the file it
wrote is elaborated.
-/
import BrunnlerK.Corpus.Basic

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

def main (args : List String) : IO UInt32 := do
  match args with
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
  | _ => IO.eprintln "usage: ksearch facts | status | run <family> <n> | cert <family> <n>"; return 2
