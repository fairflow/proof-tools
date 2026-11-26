/-
The goals of the campaign, as named statements: each is a proposition, or
a type where the goal is data.  Nothing is proved here.  The proofs are in
the files that `campaign/statements.md` names.

Theory file: it ends with its bound on axioms.
-/
import MALL.Semantics

namespace MALL

open List

/-! ## Soundness and completeness (Girard, 1.16 and 1.17) -/

/-- **Soundness** (Proposition 1.16): "Linear sequent calculus is sound
w.r.t. validity in phase structures." -/
def Soundness : Prop := ∀ Γ : List Form, Derivable Γ → Valid Γ

/-- **Completeness** (Theorem 1.17): "Linear sequent calculus is complete
w.r.t. phase semantics."  In the form of Lafont's Theorem 1, (2) ⟹ (4):
what is valid has a derivation without cut. -/
def Completeness : Prop := ∀ Γ : List Form, Valid Γ → Nonempty (CF Γ)

/-! ## Cut elimination -/

/-- **Cut elimination, as a proposition** (Lafont, Theorem 1,
(1) ⟹ (4)). -/
def CutEliminationProp : Prop := ∀ Γ : List Form, Derivable Γ → Nonempty (CF Γ)

/-- **A cut is admissible without cut**, as a function: from derivations
without cut of `⊢ A, Γ` and `⊢ A⊥, Δ`, one of `⊢ Γ, Δ`. -/
abbrev CutAdmissible : Type :=
  (A : Form) → (Γ Δ : List Form) → CF (A :: Γ) → CF (Aᗮ :: Δ) → CF (Γ ++ Δ)

/-- **Cut elimination, as a function** on derivations. -/
abbrev CutElimination : Type := (Γ : List Form) → Fam Γ → CF Γ

/-! ## Exchange (the source's rule EXCH) -/

/-- **Exchange keeps the height**: the permuted derivation is no
higher. -/
def ExchangeKeepsHeight : Prop :=
  ∀ (Γ Γ' : List Form) (e : Γ ~ Γ') (d : Fam Γ), (d.exch e).height = d.height

/-! ## The axiom restricted to letters (the remark of p. 22) -/

/-- Every logical axiom of the derivation is at a letter: `⊢ a, a⊥`. -/
def CF.Atomic : {Ξ : List Form} → CF Ξ → Prop
  | _, .ax A _ => (∃ a, A = .atom a) ∨ (∃ a, A = .natom a)
  | _, .top _ _ => True
  | _, .wth _ _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .plus₁ _ _ _ _ d => d.Atomic
  | _, .plus₂ _ _ _ _ d => d.Atomic
  | _, .one _ => True
  | _, .bot _ _ d => d.Atomic
  | _, .tensor _ _ _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .par _ _ _ _ d => d.Atomic

/-- **Identity expansion** ("It is enough to restrict [the logical axiom]
to the case of a propositional letter a", p. 22): a derivation without cut
gives one whose axioms are all at letters. -/
abbrev IdentityExpansion : Type := (Γ : List Form) → CF Γ → { d : CF Γ // d.Atomic }

/-! ## Weakening and contraction (forbidden, p. 22) -/

/-- **Weakening**: REFUTED. -/
def Weakening : Prop := ∀ (Γ : List Form) (A : Form), Derivable Γ → Derivable (A :: Γ)

/-- **Contraction**: REFUTED. -/
def Contraction : Prop := ∀ (Γ : List Form) (A : Form), Derivable (A :: A :: Γ) → Derivable (A :: Γ)

/-! ## Inversions -/

/-- **⅋ is invertible.** -/
abbrev ParInversion : Type := (A B : Form) → (Γ : List Form) → CF (A ⅋ B :: Γ) → CF (A :: B :: Γ)

/-- **⊥ is invertible.** -/
abbrev BotInversion : Type := (Γ : List Form) → CF (⊥ :: Γ) → CF Γ

/-- **& is invertible** (Girard, p. 24, (vii): "⊢ B & C, D is provable iff
⊢ B, D and ⊢ C, D are both provable"). -/
abbrev WithInversion : Type :=
  (A B : Form) → (Γ : List Form) → CF (A & B :: Γ) → CF (A :: Γ) × CF (B :: Γ)

/-! ## Decidability (LMSS, Theorem 2.2) -/

/-- **Derivability is decidable.** -/
abbrev DerivableDecidable : Type := (Γ : List Form) → Decidable (Derivable Γ)

/-- **Validity is decidable.** -/
abbrev ValidDecidable : Type := (Γ : List Form) → Decidable (Valid Γ)

/-! ## The disjunction property, for ⊕ -/

/-- **The disjunction property**: a derivation of `⊢ A ⊕ B` gives one of
`⊢ A` or one of `⊢ B`. -/
def DisjunctionProperty : Prop :=
  ∀ A B : Form, Derivable [A ⊕ B] → Derivable [A] ∨ Derivable [B]

/-! ## The subformula property (LMSS, Corollary A.4) -/

/-- `C` is a subformula of `D`. -/
inductive Form.IsSub (C : Form) : Form → Prop where
  | refl : IsSub C C
  | tensor₁ {A B : Form} : IsSub C A → IsSub C (A ⊗ B)
  | tensor₂ {A B : Form} : IsSub C B → IsSub C (A ⊗ B)
  | par₁ {A B : Form} : IsSub C A → IsSub C (A ⅋ B)
  | par₂ {A B : Form} : IsSub C B → IsSub C (A ⅋ B)
  | wth₁ {A B : Form} : IsSub C A → IsSub C (A & B)
  | wth₂ {A B : Form} : IsSub C B → IsSub C (A & B)
  | plus₁ {A B : Form} : IsSub C A → IsSub C (A ⊕ B)
  | plus₂ {A B : Form} : IsSub C B → IsSub C (A ⊕ B)

/-- The property holds of every sequent of the derivation. -/
def CF.All (P : List Form → Prop) : {Ξ : List Form} → CF Ξ → Prop
  | Ξ, .ax _ _ => P Ξ
  | Ξ, .top _ _ => P Ξ
  | Ξ, .wth _ _ _ _ d₁ d₂ => P Ξ ∧ d₁.All P ∧ d₂.All P
  | Ξ, .plus₁ _ _ _ _ d => P Ξ ∧ d.All P
  | Ξ, .plus₂ _ _ _ _ d => P Ξ ∧ d.All P
  | Ξ, .one _ => P Ξ
  | Ξ, .bot _ _ d => P Ξ ∧ d.All P
  | Ξ, .tensor _ _ _ _ _ d₁ d₂ => P Ξ ∧ d₁.All P ∧ d₂.All P
  | Ξ, .par _ _ _ _ d => P Ξ ∧ d.All P

/-- **The subformula property**: in a derivation without cut, every formula
of every sequent is a subformula of a formula of the conclusion. -/
def SubformulaProperty : Prop :=
  ∀ (Ξ : List Form) (d : CF Ξ), d.All fun Θ => ∀ C ∈ Θ, ∃ D ∈ Ξ, C.IsSub D

/-! ## The finite model property (Lafont, Theorem 2) -/

/-- **The finite model property**: what is valid in every finite phase
structure is derivable. -/
def FiniteModelProperty : Prop :=
  ∀ Γ : List Form, (∀ S : PhaseStructure, S.Finite → S.Sat Γ) → Derivable Γ

end MALL

#axioms_within_file [propext, Quot.sound]
