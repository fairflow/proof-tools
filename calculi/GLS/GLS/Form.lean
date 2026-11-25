/-
Formulas and sequents of the calculus GLS, as data.

Source: R. Goré, R. Ramanayake, I. Shillito, *Cut-Elimination for
Provability Logic by Terminating Proof-Search: Formalised and
Deconstructed Using Coq* (TABLEAUX 2021), in the authors' Coq
formalisation `github.com/ianshil/CE_GLS`, commit `3dd8619`, file
`GL/GLS_PSGLS_calcs.v` ("the Coq file" below, cited by line).  Theory
file: it ends with its bound on axioms.
-/
import ProofTools.Audit

namespace GLS

/-- **Formulas** (the Coq file, l. 41, `MPropF`): a propositional
variable, `⊥`, an implication, a boxed formula.  The source's variables
are the members of a set with decidable equality (l. 23, 25); here they
are numbered. -/
inductive Form where
  /-- A propositional variable, the source's `# P`. -/
  | var (p : Nat)
  /-- The source's `⊥`. -/
  | bot
  /-- The source's `A → B`. -/
  | imp (A B : Form)
  /-- The source's `Box A`. -/
  | box (A : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

@[inherit_doc] scoped notation "⊥" => Form.bot
@[inherit_doc] scoped infixr:60 " ⟶ " => Form.imp
@[inherit_doc] scoped prefix:max "□" => Form.box

/-- **Sequents** (the Coq file: `rel (list (MPropF V))`, a pair of lists,
"based on multisets", l. 32): an antecedent and a succedent.  The lists
are read as multisets: no rule of the family looks at the order. -/
structure Seq where
  /-- The antecedent, the source's `Γ`. -/
  ant : List Form
  /-- The succedent, the source's `Δ`. -/
  suc : List Form
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The sequent `Γ ⇒ Δ`. -/
scoped infix:50 " ⇒ " => Seq.mk

/-- What a formula of the antecedent gives to the premise of GLR: a boxed
formula `□B` gives `B, □B`, and any other formula gives nothing. -/
def Form.xb : Form → List Form
  | □B => [B, □B]
  | _ => []

/-- **The boxed part of an antecedent, unboxed and kept**: `B, □B` for
each boxed formula `□B` of `Γ`, in order.  The Coq file's
`XBoxed_list (top_boxes Γ)` (l. 154, 161). -/
def xbox (Γ : List Form) : List Form := Γ.flatMap Form.xb

/-- The size of a formula (the Coq file, l. 81, `size_form`): the number
of its variables, `⊥`s and connectives. -/
def Form.size : Form → Nat
  | .var _ => 1
  | ⊥ => 1
  | A ⟶ B => A.size + B.size + 1
  | □A => A.size + 1

end GLS

#axioms_within_file [propext, Quot.sound]
