/-
Formulas of Brünnler's nested sequent systems.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, §2.1.1,
"Formulas", p. 6.  Theory file: it ends with its bound on axioms.
-/
import ProofTools.Audit

namespace BrunnlerK

/-- **Formulas**, in negation normal form (source p. 6):

    A ::= p | p̄ | (A ∨ A) | (A ∧ A) | ◇A | □A

A proposition is a number.  `atom n` is the proposition `p`, and `natom n`
its negation `p̄`: the source's "atoms" are these two forms. -/
inductive Form where
  /-- A proposition `p`. -/
  | atom (n : Nat)
  /-- The negation `p̄` of a proposition. -/
  | natom (n : Nat)
  /-- `A ∨ B`, written `A ⋎ B`. -/
  | or (A B : Form)
  /-- `A ∧ B`, written `A ⋏ B`. -/
  | and (A B : Form)
  /-- `◇A`. -/
  | dia (A : Form)
  /-- `□A`. -/
  | box (A : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

-- The source's connectives.  `∨` and `∧` are Lean's own for propositions,
-- so the formulas' are written `⋎` and `⋏`.  Left-associative, as the
-- source says ("Binary connectives are left-associative").  The source
-- brackets every mixed formula; that `⋏` binds tighter than `⋎` is ours.
@[inherit_doc] scoped infixl:65 " ⋎ " => Form.or
@[inherit_doc] scoped infixl:70 " ⋏ " => Form.and
@[inherit_doc] scoped prefix:max "◇" => Form.dia
@[inherit_doc] scoped prefix:max "□" => Form.box

/-- **The negation `Ā` of a formula**, "defined as usual using the De Morgan
laws" (source p. 6).  The source writes out no clause.  The modal clauses
are as its cut rule and its Definition 2.28 use them: the negation of `□A`
is `◇Ā`, and of `◇A` is `□Ā`. -/
def Form.dual : Form → Form
  | .atom n => .natom n
  | .natom n => .atom n
  | .or A B => .and A.dual B.dual
  | .and A B => .or A.dual B.dual
  | .dia A => .box A.dual
  | .box A => .dia A.dual

@[inherit_doc] scoped prefix:max "∼" => Form.dual

/-- `A ⊃ B` "is defined as `Ā ∨ B`" (source p. 6). -/
def Form.imp (A B : Form) : Form := ∼A ⋎ B

@[inherit_doc] scoped infixr:60 " ⊃ " => Form.imp

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
