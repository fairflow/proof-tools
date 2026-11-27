/-
The corpus of the Run stage: sequents of known status, and four families
that grow.  Code and data, not theory.

The status of each entry is the operator's, from the logic GL as it is
usually presented (the axioms K, 4 and Löb's; frames that are transitive
and conversely well-founded), and not from the source, whose Coq files
have no examples beyond the identity.  Nothing rests on a status: each
fact of `GLS/Corpus/Facts.lean` is checked by the kernel with its
certificate, and `glsrun status` reports where the producer disagrees.
-/
import GLS.Run
import GLS.Tactic

namespace GLS.Corpus

open GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1
abbrev r : Form := .var 2

/-- `□…□A`, `n` boxes. -/
def boxes : Nat → Form → Form
  | 0, A => A
  | n + 1, A => □(boxes n A)

/-- An entry of the corpus. -/
structure Entry where
  name : String
  seq : Seq
  /-- The sequent as Lean source. -/
  src : String
  /-- Its status: derivable in GLS (valid), or not. -/
  valid : Bool
  /-- Where the status is from. -/
  why : String

/-- A list of formulas as Lean source. -/
def srcForms (Γ : List Form) : String := "[" ++ ", ".intercalate (Γ.map fun A => A.srcPrec 0) ++ "]"

/-- A sequent as Lean source. -/
def srcSeq (s : Seq) : String := srcForms s.ant ++ " ⇒ " ++ srcForms s.suc

def entry (name : String) (s : Seq) (valid : Bool) (why : String) : Entry :=
  ⟨name, s, srcSeq s, valid, why⟩

/-- **The corpus.** -/
def entries : List Entry := [
  entry "axK" ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) true "the axiom K",
  entry "ax4" ([] ⇒ [□p ⟶ □□p]) true "the axiom 4, a theorem of GL",
  entry "axLob" ([] ⇒ [□(□p ⟶ p) ⟶ □p]) true "Löb's axiom",
  entry "idBoxImp" ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) true "the source's Id_all_form",
  entry "exFalsoBox" ([] ⇒ [□⊥ ⟶ □p]) true "K: ⊥ → p under a box",
  entry "godel2" ([] ⇒ [□(□⊥ ⟶ ⊥) ⟶ □⊥]) true "Löb's axiom at ⊥: the second incompleteness theorem, formalised",
  entry "boxLobBody" ([] ⇒ [□p ⟶ □(□p ⟶ p)]) true "K: p → (□p → p) under a box",
  entry "lobRuleShape" ([□(□p ⟶ p)] ⇒ [□□p, □p]) true "Löb's axiom, weakened",
  entry "notT" ([] ⇒ [□p ⟶ p]) false "reflexivity fails at a leaf",
  entry "notAtom" ([] ⇒ [p]) false "a variable",
  entry "notConsistency" ([] ⇒ [□⊥ ⟶ ⊥]) false "□⊥ is true at a leaf",
  entry "notBoxT" ([] ⇒ [□(□p ⟶ p)]) false "with Löb's axiom it would give □p",
  entry "notConverseK" ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) false "a root with two children",
  entry "notConverse4" ([] ⇒ [□□p ⟶ □p]) false "a root with one child, a leaf where p is false",
  entry "notLobBody" ([] ⇒ [(□p ⟶ p) ⟶ p]) false "a world where p is false with a child where p is false",
  entry "notLinear" ([] ⇒ [□(□p ⟶ q), □(□q ⟶ p)]) false "two leaves that do not see each other"
]

/-! ## Five families that grow -/

/-- `⇒ □p → □ⁿ⁺¹p`: derivable (the axiom 4, `n` times).  A derivation
with GLR nested `n + 1` deep. -/
def boxChain (n : Nat) : Seq := [] ⇒ [□p ⟶ boxes (n + 1) p]

/-- The antecedent `□(p₀ → p₁), …, □(pₙ₋₁ → pₙ)`, as nested implications
before `C`. -/
def chainTo (C : Form) : Nat → Form
  | 0 => C
  | n + 1 => chainTo (□(.var n ⟶ .var (n + 1)) ⟶ C) n

/-- `⇒ □(p₀ → p₁) → … → □(pₙ₋₁ → pₙ) → □p₀ → □pₙ`: derivable (K).  One
GLR, and under it `n` uses of ImpL. -/
def kChain (n : Nat) : Seq := [] ⇒ [chainTo (□(.var 0) ⟶ □(.var n)) n]

/-- `⇒ □ⁿ⁺¹⊥ → □ⁿ⊥`: not derivable.  Refuted on a chain of `n + 1`
worlds. -/
def consis (n : Nat) : Seq := [] ⇒ [boxes (n + 1) ⊥ ⟶ boxes n ⊥]

/-- `D₀ = ⊥`, `Dₙ₊₁ = (□(p → Dₙ) → ⊥) → □((p → ⊥) → Dₙ)`: the disjunction
of two boxes whose bodies need different worlds. -/
def binForm : Nat → Form
  | 0 => ⊥
  | n + 1 => (□(p ⟶ binForm n) ⟶ ⊥) ⟶ □((p ⟶ ⊥) ⟶ binForm n)

/-- `⇒ Dₙ`: not derivable.  Refuted on a binary tree of depth `n`,
`2ⁿ⁺¹ − 1` worlds. -/
def binTree (n : Nat) : Seq := [] ⇒ [binForm n]

/-- `⇒ □p → □ⁿq → □ⁿp`: derivable, as `boxChain` is.  GLR nested `n` deep
with `□ⁿq` before `□p` in the antecedent: written out as a list, the
premise of the last GLR has some `2ⁿ` formulas from `□ⁿq` before the `p`
that IdP asks for.  (A replay that writes the sequents out and looks no
further than it must looks that far here.) -/
def lastChain (n : Nat) : Seq := [] ⇒ [□p ⟶ boxes n q ⟶ boxes n p]

/-- A family by name: the sequent, and its status. -/
def family (name : String) (n : Nat) : Option (Seq × Bool) :=
  if name == "boxChain" then some (boxChain n, true)
  else if name == "kChain" then some (kChain n, true)
  else if name == "consis" then some (consis n, false)
  else if name == "binTree" then some (binTree n, false)
  else if name == "lastChain" then some (lastChain n, true)
  else none

/-- The kernel can run the search: validity decided with no certificate.
(The search at sequents without repeated formulas, `GLS/Decide.lean`;
until 2026-11-27 the search over multisets, `validDecidable`.) -/
instance (s : Seq) : Decidable (Valid s) := validDecidableFast s

/-- The number of nodes of a tree. -/
def nodes (t : Tree) : Nat := t.size

end GLS.Corpus
