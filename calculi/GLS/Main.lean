/-
`glsrun`: the producer of the Run stage, compiled.

    glsrun facts                 the facts file, for the corpus
    glsrun status                one line for each entry of the corpus
    glsrun run <family> <n>      one member of a family: the verdict, the
                                 size of the certificate, the time
    glsrun cert <family> <n>     the same, and a Lean file that states the
                                 fact with its certificate
    glsrun setcert <family> <n>  the same by the search over sets

Not trusted.  What it prints is checked by the kernel when the file it
wrote is elaborated.
-/
import GLS.Corpus.Basic
import GLS.SetSearch

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

def main (args : List String) : IO UInt32 := do
  match args with
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
  | _ => IO.eprintln "usage: glsrun facts | status | run <family> <n> | cert <family> <n> | setcert <family> <n>"; return 2
