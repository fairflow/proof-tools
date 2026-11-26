/-
Further results: exchange, the logical axiom restricted to letters,
decidability, weakening and contraction refuted, the disjunction property
for ⊕, the subformula property.

Sources: J.-Y. Girard, *Linear logic* (1987), p. 22 (the remark on the
axiom; "weakening is forbidden as well"); Lincoln, Mitchell, Scedrov and
Shankar (1992), Theorem 2.2 (decidability) and Corollary A.4 (the
subformula property).  Theory file: it ends with its bound on axioms.
-/
import MALL.Completeness
import MALL.Decide

namespace MALL

open List

/-! ## Exchange -/

/-- **Exchange keeps the height.**  It changes the hypothesis of the last
rule and nothing else. -/
theorem exchangeKeepsHeight : ExchangeKeepsHeight := fun _ _ e d => d.height_exch e

/-! ## The logical axiom, from axioms at letters -/

/-- The logical axiom `⊢ A, A⊥`, derived with axioms at letters only: by
recursion on the formula. -/
def idExp : (A : Form) → CF [A, Aᗮ]
  | .atom a => .ax (.atom a) (.refl _)
  | .natom a => .ax (.natom a) (.refl _)
  | .one => .bot [𝟏] (by decide) (.one (.refl _))
  | .bot => .bot [𝟏] (.refl _) (.one (.refl _))
  | .top => .top [𝟎] (.refl _)
  | .zero => .top [𝟎] (by decide)
  | .tensor A B =>
      .par Aᗮ Bᗮ [A ⊗ B] (by show [A ⊗ B, Aᗮ ⅋ Bᗮ] ~ _; perm_count [])
        (.tensor A B [Aᗮ] [Bᗮ] (by perm_count []) (idExp A) (idExp B))
  | .par A B =>
      .par A B [Aᗮ ⊗ Bᗮ] (.refl _)
        (.tensor Aᗮ Bᗮ [A] [B] (by perm_count [])
          ((idExp A).exch (by perm_count [])) ((idExp B).exch (by perm_count [])))
  | .wth A B =>
      .wth A B [Aᗮ ⊕ Bᗮ] (.refl _)
        (.plus₁ Aᗮ Bᗮ [A] (by perm_count []) ((idExp A).exch (by perm_count [])))
        (.plus₂ Aᗮ Bᗮ [B] (by perm_count []) ((idExp B).exch (by perm_count [])))
  | .plus A B =>
      .wth Aᗮ Bᗮ [A ⊕ B] (by show [A ⊕ B, Aᗮ & Bᗮ] ~ _; perm_count [])
        (.plus₁ A B [Aᗮ] (by perm_count []) (idExp A))
        (.plus₂ A B [Bᗮ] (by perm_count []) (idExp B))

theorem CF.atomic_exch {Ξ Ξ' : List Form} (e : Ξ ~ Ξ') (d : CF Ξ) :
    (d.exch e).Atomic ↔ d.Atomic := by
  cases d <;> exact Iff.rfl

theorem idExp_atomic : ∀ A : Form, (idExp A).Atomic
  | .atom a => .inl ⟨a, rfl⟩
  | .natom a => .inr ⟨a, rfl⟩
  | .one => trivial
  | .bot => trivial
  | .top => trivial
  | .zero => trivial
  | .tensor A B => ⟨idExp_atomic A, idExp_atomic B⟩
  | .par A B => ⟨(CF.atomic_exch _ _).2 (idExp_atomic A), (CF.atomic_exch _ _).2 (idExp_atomic B)⟩
  | .wth A B => ⟨(CF.atomic_exch _ _).2 (idExp_atomic A), (CF.atomic_exch _ _).2 (idExp_atomic B)⟩
  | .plus A B => ⟨idExp_atomic A, idExp_atomic B⟩

/-- Each logical axiom of a derivation replaced by its derivation from
axioms at letters. -/
def CF.expand : {Ξ : List Form} → CF Ξ → CF Ξ
  | _, .ax A h => (idExp A).exch h.symm
  | _, .top Γ h => .top Γ h
  | _, .wth A B Γ h d₁ d₂ => .wth A B Γ h d₁.expand d₂.expand
  | _, .plus₁ A B Γ h d => .plus₁ A B Γ h d.expand
  | _, .plus₂ A B Γ h d => .plus₂ A B Γ h d.expand
  | _, .one h => .one h
  | _, .bot Γ h d => .bot Γ h d.expand
  | _, .tensor A B Γ Δ h d₁ d₂ => .tensor A B Γ Δ h d₁.expand d₂.expand
  | _, .par A B Γ h d => .par A B Γ h d.expand

theorem CF.expand_atomic : {Ξ : List Form} → (d : CF Ξ) → d.expand.Atomic
  | _, .ax A _ => (CF.atomic_exch _ _).2 (idExp_atomic A)
  | _, .top _ _ => trivial
  | _, .wth _ _ _ _ d₁ d₂ => ⟨d₁.expand_atomic, d₂.expand_atomic⟩
  | _, .plus₁ _ _ _ _ d => d.expand_atomic
  | _, .plus₂ _ _ _ _ d => d.expand_atomic
  | _, .one _ => trivial
  | _, .bot _ _ d => d.expand_atomic
  | _, .tensor _ _ _ _ _ d₁ d₂ => ⟨d₁.expand_atomic, d₂.expand_atomic⟩
  | _, .par _ _ _ _ d => d.expand_atomic

/-- **Identity expansion** (Girard, p. 22: "It is enough to restrict it to
the case of a propositional letter a"). -/
def identityExpansion : IdentityExpansion := fun _ d => ⟨d.expand, d.expand_atomic⟩

/-! ## Decidability -/

instance decDerivable (Γ : List Form) : Decidable (Derivable Γ) :=
  decidable_of_iff _ (derivable_iff_cf Γ).symm

instance decValid (Γ : List Form) : Decidable (Valid Γ) :=
  decidable_of_iff _ (valid_iff_derivable Γ).symm

/-- **Derivability is decidable** (LMSS, Theorem 2.2): by the search for a
derivation without cut, and cut elimination. -/
@[reducible] def derivableDecidable : DerivableDecidable := fun Γ => decDerivable Γ

/-- **Validity is decidable**: by soundness and completeness. -/
@[reducible] def validDecidable : ValidDecidable := fun Γ => decValid Γ

/-! ## Weakening and contraction -/

/-- `⊢ 1, 1` is not derivable. -/
theorem not_derivable_one_one : ¬ Derivable [𝟏, 𝟏] := by decide +kernel

/-- **Weakening is REFUTED**: `⊢ 1` is derivable and `⊢ 1, 1` is not. -/
theorem not_weakening : ¬ Weakening := fun h =>
  not_derivable_one_one (h [𝟏] 𝟏 ⟨.one (.refl _)⟩)

/-- `⊢ a ⊕ a⊥` is not derivable. -/
theorem not_derivable_plus : ¬ Derivable [Form.atom 0 ⊕ Form.natom 0] := by decide +kernel

/-- `⊢ a ⊕ a⊥, a ⊕ a⊥` is derivable. -/
theorem derivable_plus_plus :
    Derivable [Form.atom 0 ⊕ Form.natom 0, Form.atom 0 ⊕ Form.natom 0] := by decide +kernel

/-- **Contraction is REFUTED**: `⊢ a ⊕ a⊥, a ⊕ a⊥` is derivable and
`⊢ a ⊕ a⊥` is not. -/
theorem not_contraction : ¬ Contraction := fun h =>
  not_derivable_plus (h [] _ derivable_plus_plus)

/-! ## The disjunction property -/

/-- The last rule of a derivation without cut of `⊢ A ⊕ B` is 1⊕ or 2⊕. -/
theorem disjunction_cf {A B : Form} (d : CF [A ⊕ B]) : Nonempty (CF [A]) ∨ Nonempty (CF [B]) := by
  cases d with
  | ax X h =>
    have e : (1 : Nat) = 2 := h.length_eq
    exact absurd e (by decide)
  | top Γ h => cases perm_singleton_eq h.symm
  | wth A' B' Γ h _ _ => cases perm_singleton_eq h.symm
  | plus₁ A' B' Γ h d =>
    have e := perm_singleton_eq h.symm
    injection e with e₁ e₂
    injection e₁ with eA eB
    subst eA eB e₂
    exact .inl ⟨d⟩
  | plus₂ A' B' Γ h d =>
    have e := perm_singleton_eq h.symm
    injection e with e₁ e₂
    injection e₁ with eA eB
    subst eA eB e₂
    exact .inr ⟨d⟩
  | one h => cases perm_singleton_eq h.symm
  | bot Γ h _ => cases perm_singleton_eq h.symm
  | tensor A' B' Γ Δ h _ _ => cases perm_singleton_eq h.symm
  | par A' B' Γ h _ => cases perm_singleton_eq h.symm

/-- **The disjunction property**, for ⊕. -/
theorem disjunctionProperty : DisjunctionProperty := fun _ _ h =>
  let ⟨d⟩ := cutEliminationProp _ h
  (disjunction_cf d).imp (fun ⟨d⟩ => ⟨d.toFam⟩) (fun ⟨d⟩ => ⟨d.toFam⟩)

/-! ## The subformula property -/

theorem Form.IsSub.trans {C X D : Form} (h₁ : C.IsSub X) (h₂ : X.IsSub D) : C.IsSub D := by
  induction h₂ with
  | refl => exact h₁
  | tensor₁ _ ih => exact .tensor₁ ih
  | tensor₂ _ ih => exact .tensor₂ ih
  | par₁ _ ih => exact .par₁ ih
  | par₂ _ ih => exact .par₂ ih
  | wth₁ _ ih => exact .wth₁ ih
  | wth₂ _ ih => exact .wth₂ ih
  | plus₁ _ ih => exact .plus₁ ih
  | plus₂ _ ih => exact .plus₂ ih

/-- Every formula of `Θ` is a subformula of a formula of `Ξ`. -/
def SubOf (Ξ Θ : List Form) : Prop := ∀ C ∈ Θ, ∃ D ∈ Ξ, C.IsSub D

theorem SubOf.step {Ξ Θ Θ' : List Form} (h : SubOf Ξ Θ) (h' : SubOf Θ Θ') : SubOf Ξ Θ' :=
  fun C hC =>
    let ⟨X, hX, hCX⟩ := h' C hC
    let ⟨D, hD, hXD⟩ := h X hX
    ⟨D, hD, hCX.trans hXD⟩

/-- The premise `X₁, …, Γ` of a rule with conclusion `Θ ~ P, Γ`, where
each `Xᵢ` is a subformula of `P`. -/
theorem subOf_prem {Θ Γ Xs : List Form} {P : Form} (h : Θ ~ P :: Γ)
    (hX : ∀ X ∈ Xs, X.IsSub P) : SubOf Θ (Xs ++ Γ) := fun C hC =>
  (mem_append.1 hC).elim
    (fun hC => ⟨P, h.mem_iff.2 (mem_cons_self ..), hX C hC⟩)
    (fun hC => ⟨C, h.mem_iff.2 (mem_cons.2 (.inr hC)), .refl⟩)

theorem CF.all_subOf (Ξ₀ : List Form) : {Ξ : List Form} → (d : CF Ξ) → SubOf Ξ₀ Ξ →
    d.All (SubOf Ξ₀)
  | _, .ax _ _, h => h
  | _, .top _ _, h => h
  | _, .wth A B Γ e d₁ d₂, h =>
    ⟨h, d₁.all_subOf Ξ₀ (h.step (subOf_prem (Xs := [A]) e (by
        intro X hX; cases mem_singleton.1 hX; exact .wth₁ .refl))),
      d₂.all_subOf Ξ₀ (h.step (subOf_prem (Xs := [B]) e (by
        intro X hX; cases mem_singleton.1 hX; exact .wth₂ .refl)))⟩
  | _, .plus₁ A B Γ e d, h =>
    ⟨h, d.all_subOf Ξ₀ (h.step (subOf_prem (Xs := [A]) e (by
        intro X hX; cases mem_singleton.1 hX; exact .plus₁ .refl)))⟩
  | _, .plus₂ A B Γ e d, h =>
    ⟨h, d.all_subOf Ξ₀ (h.step (subOf_prem (Xs := [B]) e (by
        intro X hX; cases mem_singleton.1 hX; exact .plus₂ .refl)))⟩
  | _, .one _, h => h
  | _, .bot Γ e d, h =>
    ⟨h, d.all_subOf Ξ₀ (h.step (subOf_prem (Xs := []) e (by intro X hX; cases hX)))⟩
  | _, .tensor A B Γ Δ e d₁ d₂, h =>
    ⟨h, d₁.all_subOf Ξ₀ (h.step fun C hC => (mem_cons.1 hC).elim
        (fun eC => ⟨A ⊗ B, e.mem_iff.2 (mem_cons_self ..), eC ▸ .tensor₁ .refl⟩)
        (fun hC => ⟨C, e.mem_iff.2 (mem_cons.2 (.inr (mem_append.2 (.inl hC)))), .refl⟩)),
      d₂.all_subOf Ξ₀ (h.step fun C hC => (mem_cons.1 hC).elim
        (fun eC => ⟨A ⊗ B, e.mem_iff.2 (mem_cons_self ..), eC ▸ .tensor₂ .refl⟩)
        (fun hC => ⟨C, e.mem_iff.2 (mem_cons.2 (.inr (mem_append.2 (.inr hC)))), .refl⟩))⟩
  | _, .par A B Γ e d, h =>
    ⟨h, d.all_subOf Ξ₀ (h.step (subOf_prem (Xs := [A, B]) e (by
        intro X hX
        rcases mem_cons.1 hX with rfl | hX
        · exact .par₁ .refl
        · cases mem_singleton.1 hX; exact .par₂ .refl)))⟩

/-- **The subformula property** (LMSS, Corollary A.4). -/
theorem subformulaProperty : SubformulaProperty := fun Ξ d =>
  d.all_subOf Ξ fun C hC => ⟨C, hC, .refl⟩

end MALL

#axioms_within_file [propext, Quot.sound]
