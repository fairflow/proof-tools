/-
The goals of the campaign, as named statements: each is a proposition, or
a type where the goal is data.  Nothing is proved here.  The proofs are in
the files that `campaign/statements.md` names.

CCP is Chang, Chaudhuri, Pfenning, CMU-CS-03-131R; Pfenning is the
lecture notes *Linear Logic* (draft of 26 January 2002); KOT is Kanovich,
Okada, Terui (2006).  Theory file: it ends with its bound on axioms.
-/
import DILL.Semantics
import DILL.ILL

namespace DILL

open List

/-! ## Soundness and completeness for the phase semantics (KOT Theorem 2.9) -/

/-- **Soundness**: what is derivable, with the cuts, is valid. -/
def Soundness : Prop := ∀ j : Seq, Derivable j → Valid j

/-- **Completeness, without cut** (KOT Theorem 2.9 with Remark 2.11):
what is valid has a derivation without cut. -/
def Completeness : Prop := ∀ j : Seq, Valid j → Nonempty (CF j)

/-- **Cut elimination, as a proposition**: from soundness and
completeness. -/
def CutEliminationProp : Prop := ∀ j : Seq, Derivable j → Nonempty (CF j)

/-! ## The structural properties (CCP Theorem 2, and p. 2) -/

/-- **Weakening of the unrestricted zone** (CCP Theorem 2.1): "If
`Γ ; Δ ⟹ γ`, then `Γ, A ; Δ ⟹ γ`." -/
abbrev WeakeningU : Type :=
  (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

/-- **Contraction of the unrestricted zone** (CCP Theorem 2.2): "If
`Γ, A, A ; Δ ⟹ γ`, then `Γ, A ; Δ ⟹ γ`." -/
abbrev ContractionU : Type :=
  (c : Bool) → (Γ Δ : List Form) → (A C : Form) →
    Fam c (A :: A :: Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

/-- **Exchange in the linear zone keeps the height.** -/
def ExchangeKeepsHeight : Prop :=
  ∀ (c : Bool) (Γ Δ Δ' : List Form) (C : Form) (e : Δ ~ Δ') (d : Fam c (Γ ⨾ Δ ⟹ C)),
    (d.exch e).height = d.height

/-- **Exchange in the unrestricted zone**, with the height kept. -/
def ExchangeUKeepsHeight : Prop :=
  ∀ (c : Bool) (Γ Γ' Δ : List Form) (C : Form), Γ ~ Γ' → ∀ d : Fam c (Γ ⨾ Δ ⟹ C),
    ∃ d' : Fam c (Γ' ⨾ Δ ⟹ C), d'.height = d.height

/-- **Weakening of the linear zone**: expected REFUTED (CCP p. 2:
"disallowing weakening and contraction"). -/
def WeakeningL : Prop :=
  ∀ (Γ Δ : List Form) (A C : Form), Derivable (Γ ⨾ Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)

/-- **Contraction of the linear zone**: expected REFUTED. -/
def ContractionL : Prop :=
  ∀ (Γ Δ : List Form) (A C : Form),
    Derivable (Γ ⨾ A :: A :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)

/-! ## Cut (CCP Principle 7 and Theorem 3; Pfenning 3.8 and 3.9) -/

/-- **The cut on a linear hypothesis is admissible without cut** (CCP
Principle 7.2): "If `Γ ; Δ ⟹ A` and `Γ ; Δ′, A ⟹ γ`, then
`Γ ; Δ, Δ′ ⟹ γ`", as a function on derivations. -/
abbrev CutAdmissible : Type :=
  (Γ Δ Δ' : List Form) → (A C : Form) →
    CF (Γ ⨾ Δ ⟹ A) → CF (Γ ⨾ A :: Δ' ⟹ C) → CF (Γ ⨾ Δ ++ Δ' ⟹ C)

/-- **The cut on a valid hypothesis is admissible without cut** (CCP
Principle 7.1): "If `Γ ; · ⟹ A` and `Γ, A ; Δ′ ⟹ γ`, then
`Γ ; Δ′ ⟹ γ`", as a function on derivations. -/
abbrev CutUAdmissible : Type :=
  (Γ Δ' : List Form) → (A C : Form) →
    CF (Γ ⨾ [] ⟹ A) → CF (A :: Γ ⨾ Δ' ⟹ C) → CF (Γ ⨾ Δ' ⟹ C)

/-- **Cut elimination** (Pfenning 3.9), as a function on derivations. -/
abbrev CutElimination : Type := (j : Seq) → Fam true j → CF j

/-! ## The invertible rules (CCP Lemma 6), and the deduction theorems -/

/-- **⊗L is invertible.** -/
abbrev TensorLInv : Type :=
  (Γ Δ : List Form) → (A B C : Form) → CF (Γ ⨾ A ⊗ B :: Δ ⟹ C) → CF (Γ ⨾ A :: B :: Δ ⟹ C)

/-- **1L is invertible.** -/
abbrev OneLInv : Type :=
  (Γ Δ : List Form) → (C : Form) → CF (Γ ⨾ 𝟏 :: Δ ⟹ C) → CF (Γ ⨾ Δ ⟹ C)

/-- **⊸R is invertible.** -/
abbrev LolliRInv : Type :=
  (Γ Δ : List Form) → (A B : Form) → CF (Γ ⨾ Δ ⟹ A ⊸ B) → CF (Γ ⨾ A :: Δ ⟹ B)

/-- **&R is invertible.** -/
abbrev WithRInv : Type :=
  (Γ Δ : List Form) → (A B : Form) → CF (Γ ⨾ Δ ⟹ A & B) → CF (Γ ⨾ Δ ⟹ A) × CF (Γ ⨾ Δ ⟹ B)

/-- **⊕L is invertible.** -/
abbrev PlusLInv : Type :=
  (Γ Δ : List Form) → (A B C : Form) →
    CF (Γ ⨾ (A ⊕ B) :: Δ ⟹ C) → CF (Γ ⨾ A :: Δ ⟹ C) × CF (Γ ⨾ B :: Δ ⟹ C)

/-- **!L is invertible.** -/
abbrev BangLInv : Type :=
  (Γ Δ : List Form) → (A C : Form) → CF (Γ ⨾ (!A) :: Δ ⟹ C) → CF (A :: Γ ⨾ Δ ⟹ C)

/-- **!R is weakly invertible**: invertible at an empty linear zone. -/
abbrev BangRInv : Type :=
  (Γ : List Form) → (A : Form) → CF (Γ ⨾ [] ⟹ !A) → CF (Γ ⨾ [] ⟹ A)

/-- **The deduction theorem for a linear hypothesis**: it is discharged
by ⊸. -/
def DeductionLinear : Prop :=
  ∀ (Γ Δ : List Form) (A B : Form),
    Derivable (Γ ⨾ A :: Δ ⟹ B) ↔ Derivable (Γ ⨾ Δ ⟹ A ⊸ B)

/-- **The deduction theorem for a valid hypothesis**: it is discharged
by `!` on the left. -/
def DeductionUnrestricted : Prop :=
  ∀ (Γ Δ : List Form) (A C : Form),
    Derivable (A :: Γ ⨾ Δ ⟹ C) ↔ Derivable (Γ ⨾ (!A) :: Δ ⟹ C)

/-- **⊗R is invertible**: expected REFUTED (CCP Lemma 6). -/
def TensorRInv : Prop :=
  ∀ (Γ Δ Δ' : List Form) (A B : Form),
    Derivable (Γ ⨾ Δ ++ Δ' ⟹ A ⊗ B) → Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ Δ' ⟹ B)

/-- **⊸L is invertible**: expected REFUTED (CCP Lemma 6, p. 18). -/
def LolliLInv : Prop :=
  ∀ (Γ Δ Δ' : List Form) (A B C : Form),
    Derivable (Γ ⨾ A ⊸ B :: (Δ ++ Δ') ⟹ C) →
      Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ B :: Δ' ⟹ C)

/-- **&L₁ is invertible**: expected REFUTED. -/
def WithL₁Inv : Prop :=
  ∀ (Γ Δ : List Form) (A B C : Form),
    Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)

/-- **&L₂ is invertible**: expected REFUTED. -/
def WithL₂Inv : Prop :=
  ∀ (Γ Δ : List Form) (A B C : Form),
    Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ B :: Δ ⟹ C)

/-- **⊕R₁ is invertible**: expected REFUTED. -/
def PlusR₁Inv : Prop :=
  ∀ (Γ Δ : List Form) (A B : Form), Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ A)

/-- **⊕R₂ is invertible**: expected REFUTED. -/
def PlusR₂Inv : Prop :=
  ∀ (Γ Δ : List Form) (A B : Form), Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ B)

/-! ## init restricted to atoms -/

/-- Every instance of init in the derivation is at an atom. -/
def Fam.Atomic {c : Bool} : {j : Seq} → Fam c j → Prop
  | _, .init A _ => ∃ a, A = .atom a
  | _, .copy _ _ d => d.Atomic
  | _, .tensorL _ _ _ _ d => d.Atomic
  | _, .tensorR _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .oneL _ _ d => d.Atomic
  | _, .oneR _ => True
  | _, .lolliL _ _ _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .lolliR d => d.Atomic
  | _, .withL₁ _ _ _ _ d => d.Atomic
  | _, .withL₂ _ _ _ _ d => d.Atomic
  | _, .withR d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .topR => True
  | _, .zeroL _ _ => True
  | _, .plusL _ _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .plusR₁ d => d.Atomic
  | _, .plusR₂ d => d.Atomic
  | _, .bangL _ _ _ d => d.Atomic
  | _, .bangR _ d => d.Atomic
  | _, .cut _ _ _ _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic
  | _, .cutU _ _ d₁ d₂ => d₁.Atomic ∧ d₂.Atomic

/-- **Identity expansion**: a derivation without cut gives one whose
instances of init are all at atoms. -/
abbrev IdentityExpansion : Type := (j : Seq) → CF j → { d : CF j // d.Atomic }

/-! ## The subformula property -/

/-- `C` is a subformula of `D`. -/
inductive Form.IsSub (C : Form) : Form → Prop where
  | refl : IsSub C C
  | tensor₁ {A B : Form} : IsSub C A → IsSub C (A ⊗ B)
  | tensor₂ {A B : Form} : IsSub C B → IsSub C (A ⊗ B)
  | lolli₁ {A B : Form} : IsSub C A → IsSub C (A ⊸ B)
  | lolli₂ {A B : Form} : IsSub C B → IsSub C (A ⊸ B)
  | wth₁ {A B : Form} : IsSub C A → IsSub C (A & B)
  | wth₂ {A B : Form} : IsSub C B → IsSub C (A & B)
  | plus₁ {A B : Form} : IsSub C A → IsSub C (A ⊕ B)
  | plus₂ {A B : Form} : IsSub C B → IsSub C (A ⊕ B)
  | bang {A : Form} : IsSub C A → IsSub C (!A)

/-- The formulas of a sequent: its conclusion and both zones. -/
def Seq.forms (j : Seq) : List Form := j.goal :: (j.unr ++ j.lin)

/-- The property holds of every sequent of the derivation: of its
conclusion, and of every sequent of the derivations of its premises. -/
def Fam.All {c : Bool} (P : Seq → Prop) : {j : Seq} → Fam c j → Prop
  | j, d => P j ∧
    match d with
    | .init _ _ => True
    | .copy _ _ d => d.All P
    | .tensorL _ _ _ _ d => d.All P
    | .tensorR _ _ _ d₁ d₂ => d₁.All P ∧ d₂.All P
    | .oneL _ _ d => d.All P
    | .oneR _ => True
    | .lolliL _ _ _ _ _ d₁ d₂ => d₁.All P ∧ d₂.All P
    | .lolliR d => d.All P
    | .withL₁ _ _ _ _ d => d.All P
    | .withL₂ _ _ _ _ d => d.All P
    | .withR d₁ d₂ => d₁.All P ∧ d₂.All P
    | .topR => True
    | .zeroL _ _ => True
    | .plusL _ _ _ _ d₁ d₂ => d₁.All P ∧ d₂.All P
    | .plusR₁ d => d.All P
    | .plusR₂ d => d.All P
    | .bangL _ _ _ d => d.All P
    | .bangR _ d => d.All P
    | .cut _ _ _ _ _ d₁ d₂ => d₁.All P ∧ d₂.All P
    | .cutU _ _ d₁ d₂ => d₁.All P ∧ d₂.All P

/-- **The subformula property**: in a derivation without cut, every
formula of every sequent is a subformula of a formula of the
conclusion. -/
def SubformulaProperty : Prop :=
  ∀ (j : Seq) (d : CF j), d.All fun j' => ∀ C ∈ j'.forms, ∃ D ∈ j.forms, C.IsSub D

/-! ## Consistency and the disjunction property (Pfenning 3.11, 3.12) -/

/-- **Consistency**: `· ; · ⟹ 0` is not derivable. -/
def Consistency : Prop := ¬ Derivable ([] ⨾ [] ⟹ 𝟎)

/-- **The disjunction property**: a derivation of `· ; · ⟹ A ⊕ B` gives
one of `· ; · ⟹ A` or one of `· ; · ⟹ B`. -/
def DisjunctionProperty : Prop :=
  ∀ A B : Form, Derivable ([] ⨾ [] ⟹ A ⊕ B) →
    Derivable ([] ⨾ [] ⟹ A) ∨ Derivable ([] ⨾ [] ⟹ B)

/-! ## The translation to and from one-zone ILL (CCP Theorem 7, items 1 and 3) -/

/-- **From two zones to one** (CCP Theorem 7.3: "If `Γ ; Δ ⟹ C` then
`!Γ, Δ ⟶ C` in ILL"), as a function on derivations, with cut and
without. -/
abbrev ToILL : Type :=
  (c : Bool) → (Γ Δ : List Form) → (C : Form) →
    Fam c (Γ ⨾ Δ ⟹ C) → ILL c (Γ.map Form.bang ++ Δ) C

/-- **From one zone to two** (CCP Theorem 7.1: "If `!Γ, Δ ⟶ C` in ILL
then `Γ ; Δ ⟹ C`"), as a function on derivations. -/
abbrev OfILL : Type :=
  (Γ Δ : List Form) → (C : Form) →
    ILL true (Γ.map Form.bang ++ Δ) C → Fam true (Γ ⨾ Δ ⟹ C)

/-- **The two calculi derive the same**: `Γ ; Δ ⟹ C` exactly when
`!Γ, Δ ⊢ C`. -/
def ILLEquivalence : Prop :=
  ∀ (Γ Δ : List Form) (C : Form),
    Derivable (Γ ⨾ Δ ⟹ C) ↔ ILLDerivable (Γ.map Form.bang ++ Δ) C

/-! ## Decidability without `!` -/

/-- **Derivability is decidable where `!` does not occur and the
unrestricted zone is empty.** -/
abbrev BangFreeDecidable : Type :=
  (Δ : List Form) → (C : Form) → (∀ A ∈ C :: Δ, A.bangFree = true) →
    Decidable (Derivable ([] ⨾ Δ ⟹ C))

end DILL

#axioms_within_file [propext, Quot.sound]
