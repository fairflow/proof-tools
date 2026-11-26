/-
The phase semantics of intuitionistic linear logic.

Source: M. Kanovich, M. Okada, K. Terui, *Intuitionistic phase semantics
is almost classical*, author's final version for Math. Struct. in Comp.
Science (2006), cited as KOT, Section 2: Definition 2.2 (intuitionistic
phase space, p. 3), Definition 2.4 (the operations, p. 4), Definition 2.6
(model, satisfaction, p. 5).  CCP has no semantics.  A set of phases is a
predicate.  The formula of a two-zone sequent is ours (see `Seq.form`).
Theory file: it ends with its bound on axioms.
-/
import DILL.System

namespace DILL

/-- **An intuitionistic phase space** (KOT Definition 2.2): "a
commutative monoid `(M, ·, ε)` and a closure operator `Cl`, that is a
mapping from the subsets of `M` to themselves such that for all
`X, Y ⊆ M`: (Cl1) `X ⊆ Cl(X)`, (Cl2) `Cl(Cl(X)) ⊆ Cl(X)`, (Cl3)
`X ⊆ Y ⟹ Cl(X) ⊆ Cl(Y)`, (Cl4) `Cl(X) · Cl(Y) ⊆ Cl(X · Y)`", where
`X · Y := {x · y | x ∈ X, y ∈ Y}`. -/
structure PhaseSpace where
  /-- The phases. -/
  M : Type
  /-- The product of two phases. -/
  mul : M → M → M
  /-- The neutral element, the source's `ε`. -/
  one : M
  /-- Neutrality. -/
  one_mul : ∀ p, mul one p = p
  /-- Commutativity. -/
  mul_comm : ∀ p q, mul p q = mul q p
  /-- Associativity. -/
  mul_assoc : ∀ p q r, mul (mul p q) r = mul p (mul q r)
  /-- The closure operator. -/
  Cl : (M → Prop) → M → Prop
  /-- (Cl1). -/
  cl_ext : ∀ (X : M → Prop) p, X p → Cl X p
  /-- (Cl2). -/
  cl_idem : ∀ (X : M → Prop) p, Cl (Cl X) p → Cl X p
  /-- (Cl3). -/
  cl_mono : ∀ (X Y : M → Prop), (∀ p, X p → Y p) → ∀ p, Cl X p → Cl Y p
  /-- (Cl4). -/
  cl_mul : ∀ (X Y : M → Prop) r, (∃ p q, Cl X p ∧ Cl Y q ∧ r = mul p q) →
    Cl (fun r => ∃ p q, X p ∧ Y q ∧ r = mul p q) r

namespace PhaseSpace

variable (P : PhaseSpace)

/-- The product of two sets of phases: `X · Y := {x · y | x ∈ X, y ∈ Y}`
(KOT p. 3). -/
def prod (X Y : P.M → Prop) : P.M → Prop := fun r => ∃ p q, X p ∧ Y q ∧ r = P.mul p q

/-- The set `1 := Cl({ε})` (KOT Definition 2.4). -/
def unit : P.M → Prop := P.Cl (fun p => p = P.one)

/-- The set `I := {x ∈ 1 | x · x = x}` (KOT Definition 2.4): the
idempotents of `1`. -/
def idem : P.M → Prop := fun x => P.unit x ∧ P.mul x x = x

/-- "A set `X ⊆ M` is said to be closed if `X = Cl(X)`" (KOT Definition
2.2); the other inclusion is (Cl1). -/
def IsClosed (X : P.M → Prop) : Prop := ∀ p, P.Cl X p → X p

end PhaseSpace

/-- **An intuitionistic phase model** (KOT Definition 2.6): "an
intuitionistic phase space with a valuation `v` that maps each
propositional variable to a closed subset of `M`".  (The source's
valuation also gives a closed set to the constant `⊥`, which the fragment
does not have.) -/
structure PhaseModel extends PhaseSpace where
  /-- The valuation. -/
  val : Nat → M → Prop
  /-- It gives closed sets. -/
  val_closed : ∀ a, toPhaseSpace.IsClosed (val a)

namespace PhaseModel

variable (S : PhaseModel)

/-- **The interpretation of a formula** (KOT Definition 2.6: "the
valuation `v` is naturally extended to all formulas of ILL using the
operations in Definition 2.4"): `X ⊗ Y := Cl(X · Y)`, `1 := Cl({ε})`,
`X & Y := X ∩ Y`, `⊤ := M`, `X ⊕ Y := Cl(X ∪ Y)`, `0 := Cl(∅)`,
`X ⊸ Y := {z ∈ M | ∀ x ∈ X (x · z ∈ Y)}`, `!X := Cl(X ∩ I)`. -/
def interp : Form → S.M → Prop
  | .atom a => S.val a
  | .tensor A B => S.Cl (S.prod (interp A) (interp B))
  | .one => S.unit
  | .lolli A B => fun z => ∀ x, interp A x → interp B (S.mul x z)
  | .wth A B => fun p => interp A p ∧ interp B p
  | .top => fun _ => True
  | .plus A B => S.Cl (fun p => interp A p ∨ interp B p)
  | .zero => S.Cl (fun _ => False)
  | .bang A => S.Cl (fun p => interp A p ∧ S.idem p)

end PhaseModel

/-- The tensor of a list of formulas, `1` for the empty list. -/
def tensorAll : List Form → Form
  | [] => 𝟏
  | A :: Γ => A ⊗ tensorAll Γ

/-- **A sequent as a formula**: `G₁, …, Gₙ ; D₁, …, Dₘ ⟹ C` is
`(!G₁ ⊗ … ⊗ !Gₙ ⊗ D₁ ⊗ … ⊗ Dₘ ⊗ 1) ⊸ C`.  This reading is ours: KOT
satisfy formulas only.  It is the one-zone sequent `!Γ, Δ ⊢ C` (CCP
Theorem 7, p. 20) read as a formula. -/
def Seq.form (j : Seq) : Form := tensorAll (j.unr.map Form.bang ++ j.lin) ⊸ j.goal

/-- The sequent is **satisfied in the model** (KOT Definition 2.6: "A
formula `A` is satisfied in model `(M, ·, ε, Cl, v)` if and only if
`ε ∈ v(A)`"), at the formula of the sequent. -/
def PhaseModel.Sat (S : PhaseModel) (j : Seq) : Prop := S.interp j.form S.one

/-- **Valid**: satisfied in every intuitionistic phase model. -/
def Valid (j : Seq) : Prop := ∀ S : PhaseModel, S.Sat j

end DILL

#axioms_within_file [propext, Quot.sound]
