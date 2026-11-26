/-
Craig interpolation for MALL, with Lyndon's condition, as a function on
derivations without cut, by Maehara's method: for every division of the
sequent of a derivation in two parts `Γ`, `Δ`, a formula `C` with
`⊢ C, Γ` and `⊢ C⊥, Δ`, every literal of which occurs in `Δ` and, negated,
in `Γ` (`craigInterpolation`).  For an implication, with cut elimination:
`craigForFormulas`.

The recursion (`CF.interp`) is structural, on the derivation, for all
divisions at once.  At each rule the principal formula `X` is in `Γ` or
in `Δ` (`Interpolant.side`).  If it is in `Γ`, the interpolant is built
from those of the premises, divided as the rule divides them
(`Interpolant.atAx`, …, `Interpolant.atPar`).  If it is in `Δ`, the same
is done for the division reversed, and the result is negated
(`Interpolant.flip`).  With `X` in `Γ` the interpolants are:

    ax     ⊥ where `A⊥` is in `Γ` too, and `A⊥` where it is in `Δ`
    1      ⊥
    ⊤      𝟎
    ⊥ ⅋ ⊕  that of the premise
    &      C₁ ⊕ C₂
    ⊗      C₁ ⅋ C₂, the context divided in four by `split4`

and with `X` in `Δ` their duals.

Theory file: it ends with its bound on axioms.
-/
import MALL.Cut
import MALL.Split

namespace MALL

open List

/-! ## Literals and letters -/

/-- The literals of `A⊥` are those of `A`, negated. -/
theorem Form.lits_neg (A : Form) : Aᗮ.lits = A.lits.map Form.neg := by
  induction A <;> simp_all [Form.neg, Form.lits]

theorem Form.mem_lits_neg {ℓ A : Form} : ℓ ∈ Aᗮ.lits ↔ ℓᗮ ∈ A.lits := by
  rw [Form.lits_neg]
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    rwa [Form.neg_neg]
  · intro h
    exact List.mem_map.2 ⟨ℓᗮ, h, Form.neg_neg ℓ⟩

theorem mem_litsL {ℓ : Form} {Γ : List Form} : ℓ ∈ litsL Γ ↔ ∃ A ∈ Γ, ℓ ∈ A.lits :=
  List.mem_flatMap

theorem mem_litsL_cons {ℓ A : Form} {Γ : List Form} :
    ℓ ∈ litsL (A :: Γ) ↔ ℓ ∈ A.lits ∨ ℓ ∈ litsL Γ := by
  simp [litsL]

theorem mem_litsL_append {ℓ : Form} {Γ Δ : List Form} :
    ℓ ∈ litsL (Γ ++ Δ) ↔ ℓ ∈ litsL Γ ∨ ℓ ∈ litsL Δ := by
  simp [litsL]

theorem litsL_perm {Γ Γ' : List Form} (e : Γ ~ Γ') {ℓ : Form} (h : ℓ ∈ litsL Γ) :
    ℓ ∈ litsL Γ' := by
  obtain ⟨A, hA, hℓ⟩ := mem_litsL.1 h
  exact mem_litsL.2 ⟨A, e.mem_iff.1 hA, hℓ⟩

theorem mem_lettersL {a : Nat} {Γ : List Form} : a ∈ lettersL Γ ↔ ∃ A ∈ Γ, a ∈ A.letters :=
  List.mem_flatMap

/-- A letter of a formula is the letter of one of its literals. -/
theorem Form.letters_of_lits {a : Nat} {A : Form} (h : a ∈ A.letters) :
    ∃ ℓ ∈ A.lits, a ∈ ℓ.letters := by
  induction A with
  | atom n => exact ⟨.atom n, by simp [Form.lits], h⟩
  | natom n => exact ⟨.natom n, by simp [Form.lits], h⟩
  | one | bot | top | zero => simp [Form.letters] at h
  | tensor A B ihA ihB | par A B ihA ihB | wth A B ihA ihB | plus A B ihA ihB =>
    simp only [Form.letters, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨ℓ, hℓ, ha⟩ := ihA h
      exact ⟨ℓ, by simp [Form.lits, hℓ], ha⟩
    · obtain ⟨ℓ, hℓ, ha⟩ := ihB h
      exact ⟨ℓ, by simp [Form.lits, hℓ], ha⟩

/-- The letter of a literal of a formula is a letter of the formula. -/
theorem Form.letters_of_mem_lits {a : Nat} {ℓ A : Form} (hℓ : ℓ ∈ A.lits) (ha : a ∈ ℓ.letters) :
    a ∈ A.letters := by
  induction A with
  | atom n | natom n =>
    simp only [Form.lits, List.mem_singleton] at hℓ
    subst hℓ
    exact ha
  | one | bot | top | zero => simp [Form.lits] at hℓ
  | tensor A B ihA ihB | par A B ihA ihB | wth A B ihA ihB | plus A B ihA ihB =>
    simp only [Form.lits, List.mem_append] at hℓ
    simp only [Form.letters, List.mem_append]
    rcases hℓ with hℓ | hℓ
    · exact .inl (ihA hℓ)
    · exact .inr (ihB hℓ)

/-- The letter of a literal of a sequent is a letter of the sequent. -/
theorem lettersL_of_litsL {a : Nat} {ℓ : Form} {Γ : List Form} (hℓ : ℓ ∈ litsL Γ)
    (ha : a ∈ ℓ.letters) : a ∈ lettersL Γ := by
  obtain ⟨A, hA, h⟩ := mem_litsL.1 hℓ
  exact mem_lettersL.2 ⟨A, hA, Form.letters_of_mem_lits h ha⟩

/-! ## Facts on permutations -/

/-- A formula of a sequent divided in two that is not in the first part is
in the second. -/
theorem mem_right_of_not_left {X : Form} {Θ Γ Δ : List Form} (e : X :: Θ ~ Γ ++ Δ)
    (hm : X ∉ Γ) : X ∈ Δ :=
  (mem_append.1 (e.mem_iff.1 (mem_cons_self ..))).resolve_left hm

/-- A sequent of one formula, divided: the part that has the formula is
the whole. -/
theorem division_one {X : Form} {Γ Δ : List Form} (e : [X] ~ Γ ++ Δ) (hm : X ∈ Γ) :
    Γ ~ [X] ∧ Δ = [] := by
  have hp := perm_cons_erase hm
  have h₀ : Γ.erase X ++ Δ ~ [] := by perm_count [e, hp]
  have h₁ := List.append_eq_nil_iff.1 (perm_nil_eq h₀)
  rw [h₁.1] at hp
  exact ⟨hp, h₁.2⟩

/-- A sequent of two formulas, divided, with the first formula in the
first part and the second part not empty: one formula in each part. -/
theorem division_two {A B : Form} {Γ Δ : List Form} (e : [A, B] ~ Γ ++ Δ) (hm : A ∈ Γ)
    (hΔ : Δ ≠ []) : Γ ~ [A] ∧ Δ ~ [B] := by
  have hp := perm_cons_erase hm
  have h₀ : [B] ~ Γ.erase A ++ Δ := by perm_count [e, hp]
  by_cases hB : B ∈ Γ.erase A
  · exact absurd (division_one h₀ hB).2 hΔ
  · have hB' : B ∈ Δ := mem_right_of_not_left h₀ hB
    have h₁ := division_one (X := B) (Γ := Δ) (Δ := Γ.erase A) (by perm_count [h₀]) hB'
    rw [h₁.2] at hp
    exact ⟨hp, h₁.1⟩

/-! ## Interpolants: the two parts exchanged, and permuted -/

/-- **The division reversed**: the interpolant negated, and the two
derivations exchanged. -/
def Interpolant.flip {Γ Δ : List Form} (i : Interpolant Γ Δ) : Interpolant Δ Γ where
  C := i.Cᗮ
  left := i.right
  right := i.left.exch (by rw [Form.neg_neg])
  lits := fun ℓ hℓ => by
    have h := i.lits ℓᗮ (Form.mem_lits_neg.1 hℓ)
    rw [Form.neg_neg] at h
    exact ⟨h.2, h.1⟩

/-- An interpolant of a division is one of any permutation of its parts. -/
def Interpolant.exch {Γ Γ' Δ Δ' : List Form} (eΓ : Γ ~ Γ') (eΔ : Δ ~ Δ')
    (i : Interpolant Γ Δ) : Interpolant Γ' Δ' where
  C := i.C
  left := i.left.exch (eΓ.cons _)
  right := i.right.exch (eΔ.cons _)
  lits := fun ℓ hℓ => ⟨litsL_perm eΓ (i.lits ℓ hℓ).1, litsL_perm eΔ (i.lits ℓ hℓ).2⟩

/-- **The principal formula `X` of a rule is in one of the two parts.**
`f` is what is done where it is in the first; where it is in the second,
`f` at the division reversed, and the result reversed. -/
def Interpolant.side (X : Form) {Θ Γ Δ : List Form} (e : X :: Θ ~ Γ ++ Δ)
    (f : (Γ Δ : List Form) → X :: Θ ~ Γ ++ Δ → X ∈ Γ → Interpolant Γ Δ) : Interpolant Γ Δ :=
  if hm : X ∈ Γ then f Γ Δ e hm
  else (f Δ Γ (by perm_count [e]) (mem_right_of_not_left e hm)).flip

/-! ## The rules, with the principal formula in the first part -/

/-- ⊤ in the first part: the interpolant `𝟎`, by `⊢ 𝟎, ⊤, Γ` and
`⊢ ⊤, Δ`. -/
def Interpolant.topL (Γ Δ : List Form) : Interpolant (⊤ :: Γ) Δ where
  C := 𝟎
  left := .top (𝟎 :: Γ) (.swap ..)
  right := .top Δ (.refl _)
  lits := fun _ h => nomatch h

/-- ⊥ in the first part: the interpolant of the premise. -/
def Interpolant.botL {Γ Δ : List Form} (i : Interpolant Γ Δ) : Interpolant (⊥ :: Γ) Δ where
  C := i.C
  left := .bot (i.C :: Γ) (.swap ..) i.left
  right := i.right
  lits := fun ℓ hℓ => ⟨mem_litsL_cons.2 (.inr (i.lits ℓ hℓ).1), (i.lits ℓ hℓ).2⟩

/-- ⅋ in the first part: the interpolant of the premise. -/
def Interpolant.parL {A B : Form} {Γ Δ : List Form} (i : Interpolant (A :: B :: Γ) Δ) :
    Interpolant (A ⅋ B :: Γ) Δ where
  C := i.C
  left := .par A B (i.C :: Γ) (.swap ..) (i.left.exch (by perm_count []))
  right := i.right
  lits := fun ℓ hℓ => by
    refine ⟨?_, (i.lits ℓ hℓ).2⟩
    have h := (i.lits ℓ hℓ).1
    simp only [mem_litsL_cons, Form.lits, List.mem_append] at h ⊢
    rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h

/-- 1⊕ in the first part: the interpolant of the premise. -/
def Interpolant.plusL₁ {A : Form} (B : Form) {Γ Δ : List Form} (i : Interpolant (A :: Γ) Δ) :
    Interpolant ((A ⊕ B) :: Γ) Δ where
  C := i.C
  left := .plus₁ A B (i.C :: Γ) (.swap ..) (i.left.exch (.swap ..))
  right := i.right
  lits := fun ℓ hℓ => by
    refine ⟨?_, (i.lits ℓ hℓ).2⟩
    have h := (i.lits ℓ hℓ).1
    simp only [mem_litsL_cons, Form.lits, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (.inl h)
    · exact .inr h

/-- 2⊕ in the first part: the interpolant of the premise. -/
def Interpolant.plusL₂ (A : Form) {B : Form} {Γ Δ : List Form} (i : Interpolant (B :: Γ) Δ) :
    Interpolant ((A ⊕ B) :: Γ) Δ where
  C := i.C
  left := .plus₂ A B (i.C :: Γ) (.swap ..) (i.left.exch (.swap ..))
  right := i.right
  lits := fun ℓ hℓ => by
    refine ⟨?_, (i.lits ℓ hℓ).2⟩
    have h := (i.lits ℓ hℓ).1
    simp only [mem_litsL_cons, Form.lits, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (.inr h)
    · exact .inr h

/-- & in the first part: the interpolant `C₁ ⊕ C₂`.  `⊢ C₁ ⊕ C₂, A & B, Γ`
is by &, with 1⊕ above its first premise and 2⊕ above its second;
`⊢ C₁⊥ & C₂⊥, Δ` is by &. -/
def Interpolant.wthL {A B : Form} {Γ Δ : List Form} (i₁ : Interpolant (A :: Γ) Δ)
    (i₂ : Interpolant (B :: Γ) Δ) : Interpolant (A & B :: Γ) Δ where
  C := .plus i₁.C i₂.C
  left := .wth A B (.plus i₁.C i₂.C :: Γ) (.swap ..)
    (.plus₁ i₁.C i₂.C (A :: Γ) (.swap ..) i₁.left)
    (.plus₂ i₁.C i₂.C (B :: Γ) (.swap ..) i₂.left)
  right := .wth i₁.Cᗮ i₂.Cᗮ Δ (.refl _) i₁.right i₂.right
  lits := fun ℓ hℓ => by
    simp only [Form.lits, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ
    · refine ⟨?_, (i₁.lits ℓ hℓ).2⟩
      have h := (i₁.lits ℓ hℓ).1
      simp only [mem_litsL_cons, Form.lits, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · refine ⟨?_, (i₂.lits ℓ hℓ).2⟩
      have h := (i₂.lits ℓ hℓ).1
      simp only [mem_litsL_cons, Form.lits, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (.inr h)
      · exact .inr h

/-- ⊗ in the first part: the interpolant `C₁ ⅋ C₂`.
`⊢ C₁ ⅋ C₂, A ⊗ B, Γ₁, Γ₂` is by ⅋, with ⊗ above it from `⊢ A, C₁, Γ₁`
and `⊢ B, C₂, Γ₂`; `⊢ C₁⊥ ⊗ C₂⊥, Δ₁, Δ₂` is by ⊗. -/
def Interpolant.tensorL {A B : Form} {Γ₁ Γ₂ Δ₁ Δ₂ : List Form}
    (i₁ : Interpolant (A :: Γ₁) Δ₁) (i₂ : Interpolant (B :: Γ₂) Δ₂) :
    Interpolant (A ⊗ B :: (Γ₁ ++ Γ₂)) (Δ₁ ++ Δ₂) where
  C := i₁.C ⅋ i₂.C
  left := .par i₁.C i₂.C (A ⊗ B :: (Γ₁ ++ Γ₂)) (.refl _)
    (.tensor A B (i₁.C :: Γ₁) (i₂.C :: Γ₂) (by perm_count [])
      (i₁.left.exch (.swap ..)) (i₂.left.exch (.swap ..)))
  right := .tensor i₁.Cᗮ i₂.Cᗮ Δ₁ Δ₂ (.refl _) i₁.right i₂.right
  lits := fun ℓ hℓ => by
    simp only [Form.lits, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ
    · refine ⟨?_, mem_litsL_append.2 (.inl (i₁.lits ℓ hℓ).2)⟩
      have h := (i₁.lits ℓ hℓ).1
      simp only [mem_litsL_cons, mem_litsL_append, Form.lits, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
    · refine ⟨?_, mem_litsL_append.2 (.inr (i₂.lits ℓ hℓ).2)⟩
      have h := (i₂.lits ℓ hℓ).1
      simp only [mem_litsL_cons, mem_litsL_append, Form.lits, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)

/-! ## The rules, at a division with the principal formula in the first
part

Each takes, for a premise of the rule, the interpolants of all its
divisions. -/

/-- The logical axiom `⊢ A, A⊥`, with `A` in the first part.  Where the
second part is empty the interpolant is `⊥`, by `⊢ ⊥, A, A⊥` and `⊢ 𝟏`.
Where it is not, it is `A⊥`, and the interpolant is `A⊥`, by `⊢ A⊥, A` and
`⊢ A⊥⊥, A⊥`: two logical axioms. -/
def Interpolant.atAx (A : Form) (Γ Δ : List Form) (e : [A, Aᗮ] ~ Γ ++ Δ) (hm : A ∈ Γ) :
    Interpolant Γ Δ :=
  if hΔ : Δ = [] then
    { C := ⊥
      left := .bot Γ (.refl _) (.ax A (by subst hΔ; perm_count [e]))
      right := .one (by subst hΔ; exact .refl _)
      lits := fun _ h => nomatch h }
  else
    have hd := division_two e hm hΔ
    { C := Aᗮ
      left := .ax A (by perm_count [hd.1])
      right := .ax Aᗮ (by perm_count [hd.2])
      lits := fun ℓ hℓ =>
        ⟨mem_litsL.2 ⟨A, hm, Form.mem_lits_neg.1 hℓ⟩,
          mem_litsL.2 ⟨Aᗮ, hd.2.mem_iff.2 (mem_cons_self ..), hℓ⟩⟩ }

/-- `⊢ 𝟏`, with `𝟏` in the first part, which is then the whole: the
interpolant `⊥`, by `⊢ ⊥, 𝟏` and `⊢ 𝟏`. -/
def Interpolant.atOne (Γ Δ : List Form) (e : [𝟏] ~ Γ ++ Δ) (hm : 𝟏 ∈ Γ) : Interpolant Γ Δ :=
  have hd := division_one e hm
  { C := ⊥
    left := .bot Γ (.refl _) (.one hd.1)
    right := .one (by rw [hd.2]; exact .refl _)
    lits := fun _ h => nomatch h }

/-- ⊤, in the first part. -/
def Interpolant.atTop (Θ Γ Δ : List Form) (_e : ⊤ :: Θ ~ Γ ++ Δ) (hm : ⊤ ∈ Γ) :
    Interpolant Γ Δ :=
  (Interpolant.topL (Γ.erase ⊤) Δ).exch (perm_cons_erase hm).symm (.refl _)

/-- ⊥, in the first part. -/
def Interpolant.atBot {Θ : List Form}
    (r : (Γ Δ : List Form) → Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : ⊥ :: Θ ~ Γ ++ Δ) (hm : ⊥ ∈ Γ) : Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  (r (Γ.erase ⊥) Δ (by perm_count [e, hp])).botL.exch hp.symm (.refl _)

/-- ⅋, in the first part: the premise has `A`, `B` there. -/
def Interpolant.atPar {A B : Form} {Θ : List Form}
    (r : (Γ Δ : List Form) → A :: B :: Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : A ⅋ B :: Θ ~ Γ ++ Δ) (hm : A ⅋ B ∈ Γ) : Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  (r (A :: B :: Γ.erase (A ⅋ B)) Δ (by perm_count [e, hp])).parL.exch hp.symm (.refl _)

/-- 1⊕, in the first part: the premise has `A` there. -/
def Interpolant.atPlus₁ {A B : Form} {Θ : List Form}
    (r : (Γ Δ : List Form) → A :: Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : (A ⊕ B) :: Θ ~ Γ ++ Δ) (hm : (A ⊕ B) ∈ Γ) : Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  ((r (A :: Γ.erase (.plus A B)) Δ (by perm_count [e, hp])).plusL₁ B).exch hp.symm (.refl _)

/-- 2⊕, in the first part: the premise has `B` there. -/
def Interpolant.atPlus₂ {A B : Form} {Θ : List Form}
    (r : (Γ Δ : List Form) → B :: Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : (A ⊕ B) :: Θ ~ Γ ++ Δ) (hm : (A ⊕ B) ∈ Γ) : Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  ((r (B :: Γ.erase (.plus A B)) Δ (by perm_count [e, hp])).plusL₂ A).exch hp.symm (.refl _)

/-- &, in the first part: the two premises have `A` and `B` there. -/
def Interpolant.atWth {A B : Form} {Θ : List Form}
    (r₁ : (Γ Δ : List Form) → A :: Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (r₂ : (Γ Δ : List Form) → B :: Θ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : A & B :: Θ ~ Γ ++ Δ) (hm : A & B ∈ Γ) : Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  (Interpolant.wthL (r₁ (A :: Γ.erase (A & B)) Δ (by perm_count [e, hp]))
    (r₂ (B :: Γ.erase (A & B)) Δ (by perm_count [e, hp]))).exch hp.symm (.refl _)

/-- ⊗, in the first part.  The rule divides its context in `Θ₁`, `Θ₂`,
and the division of the sequent divides it in the rest of `Γ` and `Δ`:
`split4` gives the four parts, and the premises are divided as
`(A, Γ₁ ; Δ₁)` and `(B, Γ₂ ; Δ₂)`. -/
def Interpolant.atTensor {A B : Form} {Θ₁ Θ₂ : List Form}
    (r₁ : (Γ Δ : List Form) → A :: Θ₁ ~ Γ ++ Δ → Interpolant Γ Δ)
    (r₂ : (Γ Δ : List Form) → B :: Θ₂ ~ Γ ++ Δ → Interpolant Γ Δ)
    (Γ Δ : List Form) (e : A ⊗ B :: (Θ₁ ++ Θ₂) ~ Γ ++ Δ) (hm : A ⊗ B ∈ Γ) :
    Interpolant Γ Δ :=
  have hp := perm_cons_erase hm
  let s := split4 (Γ.erase (A ⊗ B)) Δ Θ₁ Θ₂ (by perm_count [e, hp])
  (Interpolant.tensorL (r₁ (A :: s.Γ₁) s.Δ₁ (by perm_count [s.h₁]))
    (r₂ (B :: s.Γ₂) s.Δ₂ (by perm_count [s.h₂]))).exch
    (by perm_count [hp, s.hΓ]) s.hΔ.symm

/-! ## Interpolation -/

/-- **The interpolants of a derivation without cut**, for every division
of its sequent in two, by recursion on the derivation. -/
def CF.interp : {Ξ : List Form} → CF Ξ → (Γ Δ : List Form) → Ξ ~ Γ ++ Δ → Interpolant Γ Δ
  | _, .ax A h, _, _, e => .side A (h.symm.trans e) (Interpolant.atAx A)
  | _, .top Θ h, _, _, e => .side ⊤ (h.symm.trans e) (Interpolant.atTop Θ)
  | _, .wth A B _ h d₁ d₂, _, _, e =>
    .side (A & B) (h.symm.trans e) (Interpolant.atWth d₁.interp d₂.interp)
  | _, .plus₁ A B _ h d, _, _, e =>
    .side (.plus A B) (h.symm.trans e) (Interpolant.atPlus₁ d.interp)
  | _, .plus₂ A B _ h d, _, _, e =>
    .side (.plus A B) (h.symm.trans e) (Interpolant.atPlus₂ d.interp)
  | _, .one h, _, _, e => .side 𝟏 (h.symm.trans e) Interpolant.atOne
  | _, .bot _ h d, _, _, e => .side ⊥ (h.symm.trans e) (Interpolant.atBot d.interp)
  | _, .tensor A B _ _ h d₁ d₂, _, _, e =>
    .side (A ⊗ B) (h.symm.trans e) (Interpolant.atTensor d₁.interp d₂.interp)
  | _, .par A B _ h d, _, _, e =>
    .side (A ⅋ B) (h.symm.trans e) (Interpolant.atPar d.interp)

/-- **Craig interpolation, with Lyndon's condition** (Maehara's method):
an interpolant from a derivation without cut, for any division of its
sequent. -/
def craigInterpolation : CraigInterpolation :=
  fun Γ Δ d => d.interp Γ Δ (.refl _)

/-- **The letters of an interpolant occur in both parts.** -/
theorem Interpolant.letters {Γ Δ : List Form} (i : Interpolant Γ Δ) :
    ∀ a ∈ i.C.letters, a ∈ lettersL Γ ∧ a ∈ lettersL Δ := by
  intro a ha
  obtain ⟨ℓ, hℓ, haℓ⟩ := Form.letters_of_lits ha
  have h := i.lits ℓ hℓ
  exact ⟨lettersL_of_litsL h.1 (by rw [Form.letters_neg]; exact haℓ), lettersL_of_litsL h.2 haℓ⟩

/-- **Craig interpolation, for an implication**: cut elimination, then
the interpolant of `⊢ A⊥, B` divided between its two formulas. -/
theorem craigForFormulas : CraigForFormulas := by
  intro A B ⟨d⟩
  let i : Interpolant [Aᗮ] [B] := craigInterpolation [Aᗮ] [B] (cutElimination _ d)
  refine ⟨i.C, ⟨(i.left.exch (.swap ..)).toFam⟩, ⟨i.right.toFam⟩, fun a ha => ?_⟩
  have h := i.letters a ha
  simp only [lettersL, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Form.letters_neg] at h
  exact h

end MALL

#axioms_within_file [propext, Quot.sound]
