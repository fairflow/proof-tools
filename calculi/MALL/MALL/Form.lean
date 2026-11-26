/-
Formulas of propositional multiplicative-additive linear logic, and
linear negation.

Source: J.-Y. Girard, *Linear logic*, Theoretical Computer Science 50
(1987) 1-102, p. 21 (the syntax is not numbered): "(i) The atomic
propositions are 1, ⊥, ⊤, 0 together with propositional letters
a, b, c, … and their duals a⊥, b⊥, c⊥, …  (ii) Propositions are
constructed from atomic ones by applying the binary connectives
⊗, ⅋, ⊕, &."  Theory file: it ends with its bound on axioms.
-/
import ProofTools.Audit

namespace MALL

/-- **Propositions** (Girard, p. 21).  The source's letters are
"a, b, c, …"; here they are numbered. -/
inductive Form where
  /-- A propositional letter, the source's `a`. -/
  | atom (n : Nat)
  /-- The dual of a propositional letter, the source's `a⊥`. -/
  | natom (n : Nat)
  /-- The source's bold `1`, the unit of ⊗. -/
  | one
  /-- The source's `⊥`, the unit of ⅋. -/
  | bot
  /-- The source's `⊤`, the unit of &. -/
  | top
  /-- The source's bold `0`, the unit of ⊕. -/
  | zero
  /-- The source's `A ⊗ B`, "times". -/
  | tensor (A B : Form)
  /-- The source's `A ⅋ B`, "par". -/
  | par (A B : Form)
  /-- The source's `A & B`, "with". -/
  | wth (A B : Form)
  /-- The source's `A ⊕ B`, "plus". -/
  | plus (A B : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

@[inherit_doc] scoped notation "𝟏" => Form.one
@[inherit_doc] scoped notation "⊥" => Form.bot
@[inherit_doc] scoped notation "⊤" => Form.top
@[inherit_doc] scoped notation "𝟎" => Form.zero
@[inherit_doc] scoped infixr:75 " ⊗ " => Form.tensor
@[inherit_doc] scoped infixr:74 " & " => Form.wth
@[inherit_doc] scoped infixr:72 " ⅋ " => Form.par
@[inherit_doc] scoped infixr:71 " ⊕ " => Form.plus

/-- **Linear negation** (Girard, p. 21): "linear negation of a
proposition is defined as follows: 1⊥ = ⊥, ⊥⊥ = 1, ⊤⊥ = 0, 0⊥ = ⊤,
a⊥⊥ = a (a⊥ is already in the syntax), (A ⊗ B)⊥ = A⊥ ⅋ B⊥,
(A ⅋ B)⊥ = A⊥ ⊗ B⊥, (A ⊕ B)⊥ = A⊥ & B⊥, (A & B)⊥ = A⊥ ⊕ B⊥". -/
def Form.neg : Form → Form
  | .atom n => .natom n
  | .natom n => .atom n
  | .one => .bot
  | .bot => .one
  | .top => .zero
  | .zero => .top
  | .tensor A B => .par A.neg B.neg
  | .par A B => .tensor A.neg B.neg
  | .wth A B => .plus A.neg B.neg
  | .plus A B => .wth A.neg B.neg

/-- `Aᗮ` is the source's `A⊥`.  (A postfix `⊥` would be read as the
constant.) -/
scoped postfix:max "ᗮ" => Form.neg

/-- Linear negation is an involution. -/
theorem Form.neg_neg (A : Form) : Aᗮᗮ = A := by
  induction A <;> simp_all [Form.neg]

/-- The size of a formula: the number of its letters, constants and
connectives. -/
def Form.size : Form → Nat
  | .atom _ => 1
  | .natom _ => 1
  | .one => 1
  | .bot => 1
  | .top => 1
  | .zero => 1
  | .tensor A B => A.size + B.size + 1
  | .par A B => A.size + B.size + 1
  | .wth A B => A.size + B.size + 1
  | .plus A B => A.size + B.size + 1

theorem Form.size_pos (A : Form) : 0 < A.size := by
  cases A <;> simp [Form.size]

theorem Form.size_neg (A : Form) : Aᗮ.size = A.size := by
  induction A <;> simp_all [Form.neg, Form.size]

/-- The size of a sequent: the sum of the sizes of its formulas. -/
def ssize : List Form → Nat
  | [] => 0
  | A :: Γ => A.size + ssize Γ

end MALL

#axioms_within_file [propext, Quot.sound]
