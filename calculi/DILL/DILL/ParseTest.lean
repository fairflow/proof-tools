/-
Tests of `DILL/Parse.lean`: every sequent of the corpus is read back from
what `showSeq` writes and from what `asciiSeq` writes; how the
connectives bind; and texts that are not sequents, each refused.
-/
import DILL.Parse
import DILL.Corpus.Basic

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
  | .error e => (e.splitOn words).length > 1

/-! ## The corpus, read back -/

#guard entries.length == 56
#guard entries.all fun e => reads (showSeq e.seq) e.seq
#guard entries.all fun e => reads (asciiSeq e.seq) e.seq
#guard entries.all fun e => (asciiSeq e.seq).toList.all fun (c : Char) => c.toNat < 128

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

end DILL.ParseTest
