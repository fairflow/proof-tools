/-
Formulas and sequents of dual intuitionistic linear logic.

Source: B.-Y. E. Chang, K. Chaudhuri, F. Pfenning, *A judgmental analysis
of linear logic*, CMU-CS-03-131R (revised 29 December 2003), cited as
CCP: the connectives on p. 1 ("⊗, 1, ⊸, &, ⊤, ⊕, 0, !, ?, ⊥, ¬, and" a
modal disjunction), the sequents on pp. 10-11.  The fragment taken has
no `?`, `⊥`, `¬` and no modal disjunction.  Theory file: it ends with its
bound on axioms.
-/
import ProofTools.Audit

namespace DILL

/-- **Propositions** (CCP p. 1, p. 3).  The source's atomic propositions
are parameters; here they are numbered. -/
inductive Form where
  /-- An atomic proposition. -/
  | atom (n : Nat)
  /-- The source's `A ⊗ B`. -/
  | tensor (A B : Form)
  /-- The source's bold `1`, the unit of ⊗. -/
  | one
  /-- The source's `A ⊸ B`, linear implication. -/
  | lolli (A B : Form)
  /-- The source's `A & B`. -/
  | wth (A B : Form)
  /-- The source's `⊤`, the unit of &. -/
  | top
  /-- The source's `A ⊕ B`. -/
  | plus (A B : Form)
  /-- The source's bold `0`, the unit of ⊕. -/
  | zero
  /-- The source's `!A`. -/
  | bang (A : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

@[inherit_doc] scoped notation "𝟏" => Form.one
@[inherit_doc] scoped notation "⊤" => Form.top
@[inherit_doc] scoped notation "𝟎" => Form.zero
@[inherit_doc] scoped infixr:75 " ⊗ " => Form.tensor
@[inherit_doc] scoped infixr:74 " & " => Form.wth
@[inherit_doc] scoped infixr:72 " ⊕ " => Form.plus
@[inherit_doc] scoped infixr:70 " ⊸ " => Form.lolli
/-- The source's `!A`.  Core Lean reads `!` as Boolean negation of all
that follows: write `(!A)` wherever an operator or `::` comes after. -/
scoped prefix:max "!" => Form.bang

/-- The size of a formula: the number of its atoms, constants and
connectives. -/
def Form.size : Form → Nat
  | .atom _ => 1
  | .one => 1
  | .top => 1
  | .zero => 1
  | .tensor A B => A.size + B.size + 1
  | .lolli A B => A.size + B.size + 1
  | .wth A B => A.size + B.size + 1
  | .plus A B => A.size + B.size + 1
  | .bang A => A.size + 1

theorem Form.size_pos (A : Form) : 0 < A.size := by
  cases A <;> simp [Form.size]

/-- The size of a list of formulas: the sum of their sizes. -/
def ssize : List Form → Nat
  | [] => 0
  | A :: Γ => A.size + ssize Γ

/-- `!` does not occur in the formula. -/
def Form.bangFree : Form → Bool
  | .atom _ => true
  | .one => true
  | .top => true
  | .zero => true
  | .tensor A B => A.bangFree && B.bangFree
  | .lolli A B => A.bangFree && B.bangFree
  | .wth A B => A.bangFree && B.bangFree
  | .plus A B => A.bangFree && B.bangFree
  | .bang _ => false

/-- **A sequent** (CCP pp. 10-11): `A₁ valid, …, Aⱼ valid ; B₁ res, …,
Bₖ res ⟹ C goal`.  `unr` is the zone of the valid (unrestricted)
hypotheses, the source's `Γ`; `lin` the zone of the linear ones, its `Δ`;
`goal` the one conclusion. -/
structure Seq where
  /-- The unrestricted zone, the source's `Γ`: a list read through
  membership. -/
  unr : List Form
  /-- The linear zone, the source's `Δ`: a list read as a multiset. -/
  lin : List Form
  /-- The conclusion. -/
  goal : Form
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The source's `Γ ; Δ ⟹ C ; ·`, written `Γ ⨾ Δ ⟹ C`: Lean's own `;`
between tactics cannot also be the sign between the zones. -/
scoped notation:25 Γ:26 " ⨾ " Δ:26 " ⟹ " C:26 => Seq.mk Γ Δ C

end DILL

#axioms_within_file [propext, Quot.sound]
