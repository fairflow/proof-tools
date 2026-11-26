/-
Results that need no cut: the structural properties of the two zones,
init restricted to atoms, the subformula property, and, for the calculus
without cut, consistency, the disjunction property, and the two
underivable sequents that refute weakening and contraction of the linear
zone.

Sources: CCP (Chang, Chaudhuri, Pfenning, CMU-CS-03-131R), Theorem 2,
p. 11 (weakening and contraction of the valid hypotheses), p. 2
("disallowing weakening and contraction" of the linear ones); Pfenning,
*Linear Logic* (draft of 26 January 2002), 3.11 and 3.12 (consistency,
the disjunction property).  Theory file: it ends with its bound on
axioms.

The helpers are in the namespace `DILL.Res`; the goals of the campaign
are in `DILL`.
-/
import DILL.Statements

namespace DILL

open List

/-! ## The structural properties -/

/-- **Weakening of the unrestricted zone** (CCP Theorem 2.1). -/
def weakeningU : WeakeningU := fun _ _ _ A _ d => d.weakenU A

/-- **Contraction of the unrestricted zone** (CCP Theorem 2.2). -/
def contractionU : ContractionU := fun _ _ _ _ _ d => d.contractU

/-- **Exchange in the linear zone keeps the height.** -/
theorem exchangeKeepsHeight : ExchangeKeepsHeight := fun _ _ _ _ _ e d => d.height_exch e

/-- **Exchange in the unrestricted zone**, with the height kept. -/
theorem exchangeUKeepsHeight : ExchangeUKeepsHeight := fun _ _ _ _ _ p d =>
  ⟨d.mono fun _ h => p.mem_iff.1 h, Fam.height_mono _ d⟩

namespace Res

/-! ## init, from init at atoms -/

/-- `Γ ; A ⟹ A`, derived with init at atoms only: by recursion on the
formula.  The unrestricted zone is a parameter of the recursion, since
the case of `!A` asks for the derivation at `Γ, A`. -/
def idExp : (A : Form) → (Γ : List Form) → CF (Γ ⨾ [A] ⟹ A)
  | .atom a, _ => .init (.atom a) (.refl _)
  | .tensor A B, Γ =>
      .tensorL A B [] (.refl _) (.tensorR [A] [B] (.refl _) (idExp A Γ) (idExp B Γ))
  | .one, _ => .oneL [] (.refl _) (.oneR (.refl _))
  | .lolli A B, Γ =>
      .lolliR (.lolliL A B [A] [] (.swap _ _ _) (idExp A Γ) (idExp B Γ))
  | .wth A B, Γ =>
      .withR (.withL₁ A B [] (.refl _) (idExp A Γ)) (.withL₂ A B [] (.refl _) (idExp B Γ))
  | .top, _ => .topR
  | .plus A B, Γ =>
      .plusL A B [] (.refl _) (.plusR₁ (idExp A Γ)) (.plusR₂ (idExp B Γ))
  | .zero, _ => .zeroL [] (.refl _)
  | .bang A, Γ =>
      .bangL A [] (.refl _) (.bangR (.refl _) (.copy A (.head _) (idExp A (A :: Γ))))

theorem idExp_atomic : ∀ (A : Form) (Γ : List Form), (idExp A Γ).Atomic
  | .atom a, _ => ⟨a, rfl⟩
  | .tensor A B, Γ => ⟨idExp_atomic A Γ, idExp_atomic B Γ⟩
  | .one, _ => trivial
  | .lolli A B, Γ => ⟨idExp_atomic A Γ, idExp_atomic B Γ⟩
  | .wth A B, Γ => ⟨idExp_atomic A Γ, idExp_atomic B Γ⟩
  | .top, _ => trivial
  | .plus A B, Γ => ⟨idExp_atomic A Γ, idExp_atomic B Γ⟩
  | .zero, _ => trivial
  | .bang A, Γ => idExp_atomic A (A :: Γ)

/-- Each instance of init replaced by its derivation from init at
atoms.  At init the linear zone `Ξ ~ [A]` is `[A]`, and the derivation is
carried along that equation, not through `Fam.exch`: `Fam.exch` is
compiled by well-founded recursion, which neither `decide` nor the kernel
unfolds, and this function is to be run by both. -/
def expand : {j : Seq} → CF j → CF j
  | _, .init A h => perm_singleton_eq h ▸ idExp A _
  | _, .copy A hΓ d => .copy A hΓ (expand d)
  | _, .tensorL A B Δ h d => .tensorL A B Δ h (expand d)
  | _, .tensorR Δ Δ' h d₁ d₂ => .tensorR Δ Δ' h (expand d₁) (expand d₂)
  | _, .oneL Δ h d => .oneL Δ h (expand d)
  | _, .oneR h => .oneR h
  | _, .lolliL A B Δ Δ' h d₁ d₂ => .lolliL A B Δ Δ' h (expand d₁) (expand d₂)
  | _, .lolliR d => .lolliR (expand d)
  | _, .withL₁ A B Δ h d => .withL₁ A B Δ h (expand d)
  | _, .withL₂ A B Δ h d => .withL₂ A B Δ h (expand d)
  | _, .withR d₁ d₂ => .withR (expand d₁) (expand d₂)
  | _, .topR => .topR
  | _, .zeroL Δ h => .zeroL Δ h
  | _, .plusL A B Δ h d₁ d₂ => .plusL A B Δ h (expand d₁) (expand d₂)
  | _, .plusR₁ d => .plusR₁ (expand d)
  | _, .plusR₂ d => .plusR₂ (expand d)
  | _, .bangL A Δ h d => .bangL A Δ h (expand d)
  | _, .bangR h d => .bangR h (expand d)

theorem expand_atomic : {j : Seq} → (d : CF j) → (expand d).Atomic
  | _, .init A h => by
      have e := perm_singleton_eq h
      subst e
      exact idExp_atomic A _
  | _, .copy _ _ d => expand_atomic d
  | _, .tensorL _ _ _ _ d => expand_atomic d
  | _, .tensorR _ _ _ d₁ d₂ => ⟨expand_atomic d₁, expand_atomic d₂⟩
  | _, .oneL _ _ d => expand_atomic d
  | _, .oneR _ => trivial
  | _, .lolliL _ _ _ _ _ d₁ d₂ => ⟨expand_atomic d₁, expand_atomic d₂⟩
  | _, .lolliR d => expand_atomic d
  | _, .withL₁ _ _ _ _ d => expand_atomic d
  | _, .withL₂ _ _ _ _ d => expand_atomic d
  | _, .withR d₁ d₂ => ⟨expand_atomic d₁, expand_atomic d₂⟩
  | _, .topR => trivial
  | _, .zeroL _ _ => trivial
  | _, .plusL _ _ _ _ d₁ d₂ => ⟨expand_atomic d₁, expand_atomic d₂⟩
  | _, .plusR₁ d => expand_atomic d
  | _, .plusR₂ d => expand_atomic d
  | _, .bangL _ _ _ d => expand_atomic d
  | _, .bangR _ d => expand_atomic d

end Res

/-- **Identity expansion**: init is needed at atoms only. -/
def identityExpansion : IdentityExpansion := fun _ d => ⟨Res.expand d, Res.expand_atomic d⟩

/-! ## The subformula property -/

namespace Res

theorem isSub_trans {C X D : Form} (h₁ : C.IsSub X) (h₂ : X.IsSub D) : C.IsSub D := by
  induction h₂ with
  | refl => exact h₁
  | tensor₁ _ ih => exact .tensor₁ ih
  | tensor₂ _ ih => exact .tensor₂ ih
  | lolli₁ _ ih => exact .lolli₁ ih
  | lolli₂ _ ih => exact .lolli₂ ih
  | wth₁ _ ih => exact .wth₁ ih
  | wth₂ _ ih => exact .wth₂ ih
  | plus₁ _ ih => exact .plus₁ ih
  | plus₂ _ ih => exact .plus₂ ih
  | bang _ ih => exact .bang ih

/-- `X` is a subformula of a formula of `Ξ₀`. -/
def In (Ξ₀ : List Form) (X : Form) : Prop := ∃ D ∈ Ξ₀, X.IsSub D

theorem In.sub {Ξ₀ : List Form} {X P : Form} (h : In Ξ₀ P) (hs : X.IsSub P) : In Ξ₀ X :=
  let ⟨D, hD, hPD⟩ := h
  ⟨D, hD, isSub_trans hs hPD⟩

/-- The formulas of a sequent, from its three parts. -/
theorem forms_in {Ξ₀ Γ Ξ : List Form} {C : Form} (hC : In Ξ₀ C) (hΓ : ∀ X ∈ Γ, In Ξ₀ X)
    (hΞ : ∀ X ∈ Ξ, In Ξ₀ X) : ∀ X ∈ (Γ ⨾ Ξ ⟹ C).forms, In Ξ₀ X := by
  intro X hX
  have hX : X ∈ C :: (Γ ++ Ξ) := hX
  rcases mem_cons.1 hX with e | hX
  · exact e ▸ hC
  · rcases mem_append.1 hX with hX | hX
    · exact hΓ X hX
    · exact hΞ X hX

/-- The principal formula of a left rule. -/
theorem perm_head {Ξ₀ Ξ Δ : List Form} {P : Form} (h : Ξ ~ P :: Δ)
    (hΞ : ∀ X ∈ Ξ, In Ξ₀ X) : In Ξ₀ P :=
  hΞ P (h.mem_iff.2 (mem_cons_self ..))

/-- The side formulas of a left rule. -/
theorem perm_tail {Ξ₀ Ξ Δ : List Form} {P : Form} (h : Ξ ~ P :: Δ)
    (hΞ : ∀ X ∈ Ξ, In Ξ₀ X) : ∀ X ∈ Δ, In Ξ₀ X :=
  fun X hX => hΞ X (h.mem_iff.2 (mem_cons_of_mem _ hX))

theorem cons_in {Ξ₀ Δ : List Form} {A : Form} (hA : In Ξ₀ A) (hΔ : ∀ X ∈ Δ, In Ξ₀ X) :
    ∀ X ∈ A :: Δ, In Ξ₀ X :=
  fun X hX => (mem_cons.1 hX).elim (fun e => e ▸ hA) (hΔ X)

theorem left_in {Ξ₀ Δ Δ' : List Form} (h : ∀ X ∈ Δ ++ Δ', In Ξ₀ X) : ∀ X ∈ Δ, In Ξ₀ X :=
  fun X hX => h X (mem_append.2 (.inl hX))

theorem right_in {Ξ₀ Δ Δ' : List Form} (h : ∀ X ∈ Δ ++ Δ', In Ξ₀ X) : ∀ X ∈ Δ', In Ξ₀ X :=
  fun X hX => h X (mem_append.2 (.inr hX))

theorem perm_in {Ξ₀ Ξ Θ : List Form} (h : Ξ ~ Θ) (hΞ : ∀ X ∈ Ξ, In Ξ₀ X) :
    ∀ X ∈ Θ, In Ξ₀ X :=
  fun X hX => hΞ X (h.mem_iff.2 hX)

/-- Where the formulas of the conclusion are subformulas of formulas of
`Ξ₀`, so are those of every sequent of the derivation: each rule has in
its premises only subformulas of formulas of its conclusion. -/
theorem all_sub (Ξ₀ : List Form) : {Γ Ξ : List Form} → {C : Form} →
    (d : CF (Γ ⨾ Ξ ⟹ C)) → In Ξ₀ C → (∀ X ∈ Γ, In Ξ₀ X) → (∀ X ∈ Ξ, In Ξ₀ X) →
    d.All fun j' => ∀ X ∈ j'.forms, In Ξ₀ X
  | _, _, _, .init _ _, hC, hΓ, hΞ => ⟨forms_in hC hΓ hΞ, trivial⟩
  | _, _, _, .copy A hA d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC hΓ (cons_in (hΓ A hA) hΞ)⟩
  | _, _, _, .tensorL _ _ _ h d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC hΓ
        (cons_in ((perm_head h hΞ).sub (.tensor₁ .refl))
          (cons_in ((perm_head h hΞ).sub (.tensor₂ .refl)) (perm_tail h hΞ)))⟩
  | _, _, _, .tensorR _ _ h d₁ d₂, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ,
        all_sub Ξ₀ d₁ (hC.sub (.tensor₁ .refl)) hΓ (left_in (perm_in h hΞ)),
        all_sub Ξ₀ d₂ (hC.sub (.tensor₂ .refl)) hΓ (right_in (perm_in h hΞ))⟩
  | _, _, _, .oneL _ h d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC hΓ (perm_tail h hΞ)⟩
  | _, _, _, .oneR _, hC, hΓ, hΞ => ⟨forms_in hC hΓ hΞ, trivial⟩
  | _, _, _, .lolliL _ _ _ _ h d₁ d₂, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ,
        all_sub Ξ₀ d₁ ((perm_head h hΞ).sub (.lolli₁ .refl)) hΓ (left_in (perm_tail h hΞ)),
        all_sub Ξ₀ d₂ hC hΓ
          (cons_in ((perm_head h hΞ).sub (.lolli₂ .refl)) (right_in (perm_tail h hΞ)))⟩
  | _, _, _, .lolliR d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ,
        all_sub Ξ₀ d (hC.sub (.lolli₂ .refl)) hΓ (cons_in (hC.sub (.lolli₁ .refl)) hΞ)⟩
  | _, _, _, .withL₁ _ _ _ h d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC hΓ
        (cons_in ((perm_head h hΞ).sub (.wth₁ .refl)) (perm_tail h hΞ))⟩
  | _, _, _, .withL₂ _ _ _ h d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC hΓ
        (cons_in ((perm_head h hΞ).sub (.wth₂ .refl)) (perm_tail h hΞ))⟩
  | _, _, _, .withR d₁ d₂, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d₁ (hC.sub (.wth₁ .refl)) hΓ hΞ,
        all_sub Ξ₀ d₂ (hC.sub (.wth₂ .refl)) hΓ hΞ⟩
  | _, _, _, .topR, hC, hΓ, hΞ => ⟨forms_in hC hΓ hΞ, trivial⟩
  | _, _, _, .zeroL _ _, hC, hΓ, hΞ => ⟨forms_in hC hΓ hΞ, trivial⟩
  | _, _, _, .plusL _ _ _ h d₁ d₂, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ,
        all_sub Ξ₀ d₁ hC hΓ (cons_in ((perm_head h hΞ).sub (.plus₁ .refl)) (perm_tail h hΞ)),
        all_sub Ξ₀ d₂ hC hΓ (cons_in ((perm_head h hΞ).sub (.plus₂ .refl)) (perm_tail h hΞ))⟩
  | _, _, _, .plusR₁ d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d (hC.sub (.plus₁ .refl)) hΓ hΞ⟩
  | _, _, _, .plusR₂ d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d (hC.sub (.plus₂ .refl)) hΓ hΞ⟩
  | _, _, _, .bangL _ _ h d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d hC
        (cons_in ((perm_head h hΞ).sub (.bang .refl)) hΓ) (perm_tail h hΞ)⟩
  | _, _, _, .bangR _ d, hC, hΓ, hΞ =>
      ⟨forms_in hC hΓ hΞ, all_sub Ξ₀ d (hC.sub (.bang .refl)) hΓ (fun _ hX => nomatch hX)⟩

end Res

/-- **The subformula property**: in a derivation without cut, every
formula of every sequent is a subformula of a formula of the
conclusion. -/
theorem subformulaProperty : SubformulaProperty := fun ⟨Γ, Ξ, C⟩ d =>
  Res.all_sub (C :: (Γ ++ Ξ)) d ⟨C, mem_cons_self .., .refl⟩
    (fun X hX => ⟨X, mem_cons_of_mem _ (mem_append.2 (.inl hX)), .refl⟩)
    (fun X hX => ⟨X, mem_cons_of_mem _ (mem_append.2 (.inr hX)), .refl⟩)

/-! ## Without cut: consistency, the disjunction property -/

namespace Res

theorem nil_not_perm_cons {a : Form} {l : List Form} (h : [] ~ a :: l) : False := by
  cases perm_nil_eq h.symm

/-- What a one-formula linear zone is a permutation of begins with that
formula. -/
theorem singleton_perm_cons {a b : Form} {l : List Form} (h : [a] ~ b :: l) : b = a :=
  mem_singleton.1 (h.mem_iff.2 (mem_cons_self ..))

/-- `· ; · ⟹ a` has no derivation without cut, for an atom `a`. -/
theorem not_cf_atom {a : Nat} (d : CF ([] ⨾ [] ⟹ .atom a)) : False := by
  cases d <;> first
    | contradiction
    | exact nil_not_perm_cons (by assumption)

end Res

/-- **Consistency, without cut** (Pfenning 3.11): `· ; · ⟹ 0` has no
derivation without cut.  No rule concludes it: each left rule and init
want a linear hypothesis, copy a valid one, and no right rule has `0`. -/
theorem consistencyCF : ¬ Nonempty (CF ([] ⨾ [] ⟹ 𝟎)) := by
  rintro ⟨d⟩
  cases d <;> first
    | contradiction
    | exact Res.nil_not_perm_cons (by assumption)

/-- **The disjunction property, without cut** (Pfenning 3.12): the last
rule of a derivation without cut of `· ; · ⟹ A ⊕ B` is ⊕R₁ or ⊕R₂. -/
def disjunctionCF : (A B : Form) → CF ([] ⨾ [] ⟹ A ⊕ B) →
    Sum (CF ([] ⨾ [] ⟹ A)) (CF ([] ⨾ [] ⟹ B))
  | _, _, .init _ h => (Res.nil_not_perm_cons h).elim
  | _, _, .copy _ hΓ _ => nomatch hΓ
  | _, _, .tensorL _ _ _ h _ => (Res.nil_not_perm_cons h).elim
  | _, _, .oneL _ h _ => (Res.nil_not_perm_cons h).elim
  | _, _, .lolliL _ _ _ _ h _ _ => (Res.nil_not_perm_cons h).elim
  | _, _, .withL₁ _ _ _ h _ => (Res.nil_not_perm_cons h).elim
  | _, _, .withL₂ _ _ _ h _ => (Res.nil_not_perm_cons h).elim
  | _, _, .zeroL _ h => (Res.nil_not_perm_cons h).elim
  | _, _, .plusL _ _ _ h _ _ => (Res.nil_not_perm_cons h).elim
  | _, _, .bangL _ _ h _ => (Res.nil_not_perm_cons h).elim
  | _, _, .plusR₁ d => .inl d
  | _, _, .plusR₂ d => .inr d

/-! ## Weakening and contraction of the linear zone, without cut -/

namespace Res

/-- `· ; · ⟹ 1`. -/
def cf_one : CF ([] ⨾ [] ⟹ 𝟏) := .oneR (.refl _)

/-- `· ; a, a ⟹ a ⊗ a`. -/
def cf_tensor : CF ([] ⨾ [.atom 0, .atom 0] ⟹ .atom 0 ⊗ .atom 0) :=
  .tensorR [.atom 0] [.atom 0] (.refl _) (.init _ (.refl _)) (.init _ (.refl _))

end Res

/-- `· ; a ⟹ 1` has no derivation without cut (and `· ; · ⟹ 1` has
one, `Res.cf_one`): weakening of the linear zone fails without cut. -/
theorem not_cf_weak : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ 𝟏)) := by
  rintro ⟨d⟩
  cases d <;> first
    | contradiction
    | (have h' := Res.singleton_perm_cons (by assumption); cases h')
    | (have h' := perm_nil_eq (by assumption); cases h')

/-- `· ; a ⟹ a ⊗ a` has no derivation without cut (and `· ; a, a ⟹
a ⊗ a` has one, `Res.cf_tensor`): contraction of the linear zone fails
without cut. -/
theorem not_cf_contr : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ .atom 0 ⊗ .atom 0)) := by
  rintro ⟨d⟩
  cases d
  case tensorR Δ Δ' h d₁ d₂ =>
    cases Δ with
    | nil => exact Res.not_cf_atom d₁
    | cons x Δ =>
      cases Δ' with
      | nil => exact Res.not_cf_atom d₂
      | cons y Δ' =>
        have := h.length_eq
        simp only [length_cons, length_append, length_nil] at this
        omega
  all_goals first
    | contradiction
    | (have h' := Res.singleton_perm_cons (by assumption); cases h')

/-! ## The same with cut, from cut elimination

Each takes cut elimination as a hypothesis, the named statement
`CutEliminationProp`; nothing here proves it. -/

namespace Res

/-- **Consistency**, from cut elimination. -/
theorem consistency (ce : CutEliminationProp) : Consistency := fun h =>
  consistencyCF (ce _ h)

/-- **The disjunction property**, from cut elimination. -/
theorem disjunctionProperty (ce : CutEliminationProp) : DisjunctionProperty := fun A B h =>
  let ⟨d⟩ := ce _ h
  match disjunctionCF A B d with
  | .inl d => .inl ⟨d.lift⟩
  | .inr d => .inr ⟨d.lift⟩

/-- **Weakening of the linear zone is REFUTED**, given cut elimination:
`· ; · ⟹ 1` is derivable and `· ; a ⟹ 1` is not. -/
theorem not_weakeningL (ce : CutEliminationProp) : ¬ WeakeningL := fun h =>
  not_cf_weak (ce _ (h [] [] (.atom 0) 𝟏 ⟨cf_one.lift⟩))

/-- **Contraction of the linear zone is REFUTED**, given cut elimination:
`· ; a, a ⟹ a ⊗ a` is derivable and `· ; a ⟹ a ⊗ a` is not. -/
theorem not_contractionL (ce : CutEliminationProp) : ¬ ContractionL := fun h =>
  not_cf_contr (ce _ (h [] [] (.atom 0) (.atom 0 ⊗ .atom 0) ⟨cf_tensor.lift⟩))

end Res

/-! ## Tests -/

/-- Identity expansion at `!(a ⊸ b) ⊗ 1`, run by the kernel: the one
init becomes a derivation of height 8. -/
example : ((identityExpansion _
    (.init ((!(.atom 0 ⊸ .atom 1)) ⊗ 𝟏) (.refl _) : CF ([] ⨾ [_] ⟹ _))).1).height = 8 := by
  decide

/-- The same below a rule, at a zone that is a permutation and not the
list of the rule: `· ; b, a ⊗ 𝟏 ⟹ (a ⊗ 𝟏) ⊗ b`. -/
example : ((identityExpansion _
    (.tensorR [.atom 0 ⊗ 𝟏] [.atom 1] (.swap _ _ _) (.init _ (.refl _)) (.init _ (.refl _)) :
      CF ([] ⨾ [.atom 1, .atom 0 ⊗ 𝟏] ⟹ (.atom 0 ⊗ 𝟏) ⊗ .atom 1))).1).height = 5 := by
  decide

/-- The disjunction property, run: a derivation of `· ; · ⟹ 𝟎 ⊕ 𝟏` gives
one of `· ; · ⟹ 𝟏`. -/
example : (disjunctionCF 𝟎 𝟏 (.plusR₂ (.oneR (.refl _)))).isRight = true := by decide

end DILL

#axioms_within_file [propext, Quot.sound]
