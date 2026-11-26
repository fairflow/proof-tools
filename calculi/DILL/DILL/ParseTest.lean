/-
Tests of `DILL/Parse.lean`, in two directions.

* The reader reads back what each printer writes: every sequent of the
  corpus from `showSeq` (the source's notation), from `asciiSeq` (the
  signs of a keyboard), and from the two printers of Lean source,
  `seqSrc` and `Refute.srcSeq`.
* Lean itself reads the Lean-source text as the sequent it was written
  from (`leanReads`): `dillrun prove` states its facts of that text, so
  this is what says that the fact is about the sequent in the first
  line.  It is not implied by the first direction.

Then: how the connectives bind; and texts that are not sequents, each
refused, with the place and the report.
-/
import DILL.Parse
import DILL.Corpus.Basic
import DILL.Refute
import Lean

namespace DILL.ParseTest

open DILL DILL.Corpus DILL.Parse

/-- The text is read as the sequent. -/
def reads (text : String) (j : Seq) : Bool :=
  match seq text with
  | .ok j' => j' == j
  | .error _ => false

/-- The text is refused, with a message that has the words given. -/
def refused (text : String) (words : String) : Bool :=
  match seq text with
  | .ok _ => false
  | .error e => (e.msg.splitOn words).length > 1

/-- The text is refused at the character of that number, the first
being 1. -/
def refusedAt (text : String) (n : Nat) : Bool :=
  match seq text with
  | .ok _ => false
  | .error e => e.pos + 1 == n

/-- The report of the fault of a text. -/
def report (text : String) : String :=
  match seq text with
  | .ok _ => "read"
  | .error e => e.report text

/-! ## The corpus, read back -/

#guard entries.length == 56
#guard entries.all fun e => reads (showSeq e.seq) e.seq
#guard entries.all fun e => reads (asciiSeq e.seq) e.seq
#guard entries.all fun e => (asciiSeq e.seq).toList.all fun (c : Char) => c.toNat < 128
#guard entries.all fun e => reads (seqSrc e.seq) e.seq
#guard entries.all fun e => reads (Refute.srcSeq e.seq) e.seq
#guard entries.all fun e => e.src == seqSrc e.seq

/-- Sequents outside the corpus, for what it lacks: atoms past `s`, alone
and inside a formula, `!` at each place, every connective under every
other. -/
def extra : List Seq := [
  [.atom 4] ⨾ [.atom 17 ⊸ .atom 4] ⟹ .atom 12,
  [!(.atom 5)] ⨾ [(!p) ⊗ q, !(p ⊗ q), !(!p)] ⟹ !(.atom 9),
  [p & q ⊕ r] ⨾ [(p ⊸ q) ⊸ r, p ⊸ q ⊸ r, (p ⊗ q) & (r ⊕ s)] ⟹ (!p) ⊸ 𝟏 ⊗ ⊤ ⊕ 𝟎,
  [] ⨾ [𝟏, ⊤, 𝟎] ⟹ ((!(p & q)) ⊕ .atom 4) ⊗ !(𝟏 ⊸ 𝟎),
  [] ⨾ [] ⟹ !p,
  [!p] ⨾ [!p] ⟹ (!p) ⊸ !p]

#guard extra.all fun j => reads (showSeq j) j && reads (asciiSeq j) j
#guard extra.all fun j => reads (seqSrc j) j && reads (Refute.srcSeq j) j

/-! ## Lean reads the Lean source as the same sequent -/

open Lean Elab Command Term Meta in
/-- Lean's reading of a text as a term of type `Seq`, with the notations
of `DILL/Form.lean` and the letters `p q r s` of the corpus: what the
file that `dillrun prove` prints has. -/
unsafe def leanReads (text : String) : TermElabM Seq := do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let e ← elabTermEnsuringType stx (some (mkConst ``Seq))
  synthesizeSyntheticMVarsNoPostponing
  evalExpr Seq (mkConst ``Seq) (← instantiateMVars e)

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  for j in entries.map (·.seq) ++ extra do
    let k ← unsafe leanReads (seqSrc j)
    unless k == j do
      throwError "Lean reads {seqSrc j} (seqSrc) as another sequent than it was written from"
    let k ← unsafe leanReads (Refute.srcSeq j)
    unless k == j do
      throwError "Lean reads {Refute.srcSeq j} (Refute.srcSeq) as another sequent than it was written from"

-- The test can fail: a text that Lean reads as another sequent.
open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let k ← unsafe leanReads "[] ⨾ [p ⊗ q ⊸ r] ⟹ p"
  if k == ([] ⨾ [p ⊗ (q ⊸ r)] ⟹ p) then throwError "the comparison does not tell two sequents apart"

-- Atoms past `s`.
#guard reads (asciiSeq ([.atom 4] ⨾ [.atom 17 ⊸ .atom 4] ⟹ .atom 0)) ([.atom 4] ⨾ [.atom 17 ⊸ .atom 4] ⟹ .atom 0)
#guard asciiSeq ([.atom 4] ⨾ [] ⟹ ⊤) == "a4 ; . => T"

/-! ## The forms of a sequent -/

#guard reads ". ; p, p -o q => q" ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard reads "p, p -o q => q" ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard reads "; p, p -o q => q" ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard reads "p -o q ; p => q" ([p ⊸ q] ⨾ [p] ⟹ q)
#guard reads "p ; => !p" ([p] ⨾ [] ⟹ !p)
#guard reads "=> 1" ([] ⨾ [] ⟹ 𝟏)
#guard reads ". ; . |- T" ([] ⨾ [] ⟹ ⊤)
#guard reads "p;q=>p*q+0" ([p] ⨾ [q] ⟹ (p ⊗ q) ⊕ 𝟎)
#guard reads "· ; p & q ⟹ top" ([] ⨾ [p & q] ⟹ ⊤)
-- As Lean source: zones in brackets, an atom by its number.
#guard reads "[] ⨾ [p, p ⊸ q] ⟹ q" ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard reads "[p] ; [] => Form.atom 12" ([p] ⨾ [] ⟹ .atom 12)
#guard reads "[(Form.atom  4) ⊗ q] ⨾ [] ⟹ (!Form.atom 4)" ([.atom 4 ⊗ q] ⨾ [] ⟹ !(.atom 4))
#guard reads "[p, q] => p * q" ([] ⨾ [p, q] ⟹ p ⊗ q)

/-! ## How the connectives bind: as the notations of `DILL/Form.lean` -/

#guard reads "=> p -o q -o r" ([] ⨾ [] ⟹ p ⊸ q ⊸ r)
#guard reads "=> p -o q -o r" ([] ⨾ [] ⟹ p ⊸ (q ⊸ r))
#guard reads "=> p * q -o r" ([] ⨾ [] ⟹ p ⊗ q ⊸ r)
#guard reads "=> p * q -o r" ([] ⨾ [] ⟹ (p ⊗ q) ⊸ r)
#guard reads "=> p -o q * r -o s" ([] ⨾ [] ⟹ p ⊸ q ⊗ r ⊸ s)
#guard reads "=> p + q & r * s" ([] ⨾ [] ⟹ p ⊕ q & r ⊗ s)
#guard reads "=> p + q & r * s" ([] ⨾ [] ⟹ p ⊕ (q & (r ⊗ s)))
#guard reads "=> p * q & r + s" ([] ⨾ [] ⟹ p ⊗ q & r ⊕ s)
#guard reads "=> p * q & r + s" ([] ⨾ [] ⟹ ((p ⊗ q) & r) ⊕ s)
#guard reads "=> !p * q" ([] ⨾ [] ⟹ (!p) ⊗ q)
#guard reads "=> !!p -o !(p * q)" ([] ⨾ [] ⟹ (!(!p)) ⊸ !(p ⊗ q))
#guard reads "=> (p -o q) -o r" ([] ⨾ [] ⟹ (p ⊸ q) ⊸ r)

/-! ## Refused -/

#guard refused "p => " "a formula expected"
#guard refused "p, x => p" "'x' is not an atom"
#guard refused "p ; q ; r => p" "'=>' expected"
#guard refused "(p * q => p" "')' expected"
#guard refused "p => q, r" "the sequent has ended"
#guard refused "p, => q" "a formula expected"
#guard refused "p q => q" "';' or '=>' expected"
#guard refused "p => q ?" "not a sign"
#guard refused "p" "';' or '=>' expected"
#guard refused "" "a formula expected"
#guard refused "p * => q" "a formula expected"
#guard refused "[p, q ; r => p" "',' or ']' expected"
#guard refused "p => Form.atom" "a number expected"
#guard refused "p => Form.atom x" "a number expected"
#guard refused "p ] => q" "';' or '=>' expected"

/-! ## The place, counted from character 1, and the report -/

#guard refusedAt "p, => q" 4
#guard refusedAt "p => q ?" 8
#guard refusedAt "p, x => p" 4
#guard refusedAt "(p * q => p" 8
#guard refusedAt "p => q, r" 7
-- The end of the text: the character after its last.
#guard refusedAt "p => " 6
#guard refusedAt "p -o" 5
#guard refusedAt "" 1
-- Counted in characters, not bytes: the signs of the source are one each.
#guard refusedAt "· ; p ⊸ q ⟹ q ⟹ r" 15
#guard refusedAt "p => Form.atom x" 16

#guard report "p, => q" ==
  "not a sequent, at character 4: a formula expected, and '=>' is there\n  p, => q\n     ^"
#guard report "p -o" ==
  "not a sequent, at character 5: a formula expected, and the text has ended\n  p -o\n      ^"
-- A line break or a tab in the text is a space in the report, so that the mark stays under its place.
#guard report "p,\n\tx => p" ==
  "not a sequent, at character 5: 'x' is not an atom (the atoms are p q r s, then a4, a5, …)\n  p,  x => p\n      ^"

end DILL.ParseTest
