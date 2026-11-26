/-
Cut elimination for MALL, as a function on derivations: a cut between two
derivations without cut is admissible without cut (`cutAdmissible`), and
so every derivation has one without cut (`cutElimination`).  The
inversions of ⅋, ⊥ and & follow, each by one cut.

The cut is stated for sequents up to permutation: from `d₁ : CF Γ₀` with
`Γ₀ ~ A :: Γ` and `d₂ : CF Δ₀` with `Δ₀ ~ A⊥ :: Δ`, a derivation of
`⊢ Γ, Δ` (`CutAt A`).  No rule of MALL uses a premise twice, so the
measure is lexicographic and every recursion is structural:

1. the size of the cut formula (`cutN`, by recursion on a bound `n` with
   `A.size ≤ n`);
2. the derivation on the left (`push`, by recursion on it, at `A`);
3. the derivation on the right (`push` again, at `A⊥`).

`push` takes a cut on `C` up through a derivation to the rules that
introduce `C`; what it finds there is a `Prin C Γ`, and what is done with
it is the argument `H`.  `reduce` is the `H` of the left derivation: for
each rule that introduces `A` it pushes `A⊥` up the right derivation, and
where the two rules meet it cuts on the immediate subformulas.

Theory file: it ends with its bound on axioms.
-/
import MALL.Statements

namespace MALL

open List

/-- **A last rule that introduces `C`**, in the context `Γ`: the
conclusion is `⊢ C, Γ`, and `C` is the principal formula (for the logical
axiom, either of its two formulas).  What `push` finds at the top of a
cut on `C`. -/
inductive Prin : Form → List Form → Type where
  /-- The logical axiom `⊢ A, A⊥`: the context is `A⊥`. -/
  | ax (A : Form) {Γ : List Form} (h : Γ ~ [Aᗮ]) : Prin A Γ
  /-- ⊤, in any context. -/
  | top (Γ : List Form) : Prin ⊤ Γ
  /-- &. -/
  | wth (A B : Form) {Γ : List Form} (d₁ : CF (A :: Γ)) (d₂ : CF (B :: Γ)) : Prin (A & B) Γ
  /-- 1⊕. -/
  | plus₁ (A B : Form) {Γ : List Form} (d : CF (A :: Γ)) : Prin (A ⊕ B) Γ
  /-- 2⊕. -/
  | plus₂ (A B : Form) {Γ : List Form} (d : CF (B :: Γ)) : Prin (A ⊕ B) Γ
  /-- 1: the context is empty. -/
  | one {Γ : List Form} (h : Γ ~ []) : Prin 𝟏 Γ
  /-- ⊥. -/
  | bot {Γ : List Form} (d : CF Γ) : Prin ⊥ Γ
  /-- ⊗: the context is the two contexts of the premises. -/
  | tensor (A B : Form) (Γ₁ Γ₂ : List Form) {Γ : List Form} (h : Γ ~ Γ₁ ++ Γ₂)
      (d₁ : CF (A :: Γ₁)) (d₂ : CF (B :: Γ₂)) : Prin (A ⊗ B) Γ
  /-- ⅋. -/
  | par (A B : Form) {Γ : List Form} (d : CF (A :: B :: Γ)) : Prin (A ⅋ B) Γ

/-- **A cut on `A`**, for sequents up to permutation. -/
abbrev CutAt (A : Form) : Type :=
  {Γ₀ Δ₀ : List Form} → (Γ Δ : List Form) →
    CF Γ₀ → Γ₀ ~ A :: Γ → CF Δ₀ → Δ₀ ~ Aᗮ :: Δ → CF (Γ ++ Δ)

/-! ## Facts on permutations -/

/-- A sequent `⊢ P, P⊥` that has `C` has `C⊥` for the rest. -/
theorem ax_rest {P C : Form} {Γ₀ Γ : List Form} (h : Γ₀ ~ [P, Pᗮ]) (e : Γ₀ ~ C :: Γ) :
    Γ ~ [Cᗮ] := by
  by_cases hP : P = C
  · subst hP
    perm_count [h, e]
  · have hc := perm_cons_cases (h.symm.trans e) hP
    have hm : C ∈ [Pᗮ] := hc.1.mem_iff.2 (List.mem_cons_self ..)
    have hC : C = Pᗮ := by
      rcases List.mem_cons.1 hm with e' | e'
      · exact e'
      · cases e'
    subst hC
    rw [Form.neg_neg]
    perm_count [h, e]

/-- `B⊥` is `A` where `B` is `A⊥`. -/
theorem perm_neg {Γ : List Form} {A B : Form} (h : Γ ~ [Bᗮ]) (hB : B = Aᗮ) : Γ ~ [A] := by
  subst hB
  rw [Form.neg_neg] at h
  exact h

/-! ## A cut, pushed up one derivation -/

/-- **A cut on `C`, pushed up a derivation** of `⊢ C, Γ`, with `Δ` the
context of the other premise of the cut.  Where the last rule introduces
`C`, the result is what `H` gives.  Where it introduces another formula,
`C` is in the context of the rule: the cut goes to the premises that have
`C` (both for &, one for ⊗, none for ⊤), and the same rule is applied
below, with `Δ` in its context. -/
def push {C : Form} {Δ : List Form} (H : (Γ : List Form) → Prin C Γ → CF (Γ ++ Δ)) :
    {Γ₀ : List Form} → CF Γ₀ → (Γ : List Form) → Γ₀ ~ C :: Γ → CF (Γ ++ Δ)
  | _, .ax _ h, Γ, e => H Γ (.ax C (ax_rest h e))
  | _, .top Γ' h, Γ, e =>
    if hP : ⊤ = C then H Γ (hP ▸ Prin.top Γ)
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .top (Γ'.erase C ++ Δ) (by perm_count [hc.2])
  | _, .wth A B Γ' h d₁ d₂, Γ, e =>
    if hP : A & B = C then
      (H Γ' (hP ▸ Prin.wth A B d₁ d₂)).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .wth A B (Γ'.erase C ++ Δ) (by perm_count [hc.2])
        (push H d₁ (A :: Γ'.erase C) (by perm_count [hc.1]))
        (push H d₂ (B :: Γ'.erase C) (by perm_count [hc.1]))
  | _, .plus₁ A B Γ' h d, Γ, e =>
    if hP : (A ⊕ B) = C then
      (H Γ' (hP ▸ Prin.plus₁ A B d)).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .plus₁ A B (Γ'.erase C ++ Δ) (by perm_count [hc.2])
        (push H d (A :: Γ'.erase C) (by perm_count [hc.1]))
  | _, .plus₂ A B Γ' h d, Γ, e =>
    if hP : (A ⊕ B) = C then
      (H Γ' (hP ▸ Prin.plus₂ A B d)).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .plus₂ A B (Γ'.erase C ++ Δ) (by perm_count [hc.2])
        (push H d (B :: Γ'.erase C) (by perm_count [hc.1]))
  | _, .one h, Γ, e =>
    have hh : C :: Γ = [𝟏] := perm_singleton_eq (e.symm.trans h)
    H Γ ((List.cons.inj hh).1 ▸ Prin.one (by rw [(List.cons.inj hh).2]))
  | _, .bot Γ' h d, Γ, e =>
    if hP : ⊥ = C then
      (H Γ' (hP ▸ Prin.bot d)).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .bot (Γ'.erase C ++ Δ) (by perm_count [hc.2]) (push H d (Γ'.erase C) hc.1)
  | _, .tensor A B Γ₁ Γ₂ h d₁ d₂, Γ, e =>
    if hP : A ⊗ B = C then
      H Γ (hP ▸ Prin.tensor A B Γ₁ Γ₂ (by subst hP; perm_count [h, e]) d₁ d₂)
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      have hm : C ∈ Γ₁ ++ Γ₂ := hc.1.mem_iff.2 (List.mem_cons_self ..)
      if hm₁ : C ∈ Γ₁ then
        .tensor A B (Γ₁.erase C ++ Δ) Γ₂ (by perm_count [h, e, perm_cons_erase hm₁])
          (push H d₁ (A :: Γ₁.erase C) (by perm_count [perm_cons_erase hm₁])) d₂
      else
        have hm₂ : C ∈ Γ₂ := (List.mem_append.1 hm).resolve_left hm₁
        .tensor A B Γ₁ (Γ₂.erase C ++ Δ) (by perm_count [h, e, perm_cons_erase hm₂]) d₁
          (push H d₂ (B :: Γ₂.erase C) (by perm_count [perm_cons_erase hm₂]))
  | _, .par A B Γ' h d, Γ, e =>
    if hP : A ⅋ B = C then
      (H Γ' (hP ▸ Prin.par A B d)).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .par A B (Γ'.erase C ++ Δ) (by perm_count [hc.2])
        (push H d (A :: B :: Γ'.erase C) (by perm_count [hc.1]))

/-! ## The two rules meet -/

/-- **The principal cases.**  The left premise of a cut on `A` ends with
a rule that introduces `A`; `d₂` is the right premise, of `⊢ A⊥, Δ`.  The
cut on `A⊥` is pushed up `d₂`.  At a logical axiom of `d₂` the result is
the left premise itself.  At the rule of `d₂` that introduces `A⊥`, the
dual of the rule on the left, the result is by cuts on the immediate
subformulas of `A` (`ih`).  The rules that are not dual do not meet: the
formulas they introduce are not `A` and `A⊥`. -/
def reduce {Δ₀ Δ : List Form} (d₂ : CF Δ₀) :
    {A : Form} → {Γ : List Form} → Prin A Γ → ((B : Form) → B.size < A.size → CutAt B) →
      Δ₀ ~ Aᗮ :: Δ → CF (Γ ++ Δ)
  -- a logical axiom on the left: the right premise is the result
  | _, _, .ax _ h, _, e₂ => d₂.exch (by perm_count [h, e₂])
  -- ⊤ on the left, 𝟎 on the right: no rule introduces 𝟎
  | _, Γ, .top _, _, e₂ =>
    (push (C := 𝟎) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' => .top Γ (by have h' : Δ' ~ [⊤] := h'; perm_count [h'])) d₂ Δ e₂).exch
      (by perm_count [])
  -- & on the left, ⊕ on the right
  | _, Γ, .wth A₁ A₂ p₁ p₂, ih, e₂ =>
    (push (C := .plus A₁ᗮ A₂ᗮ) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' =>
        .wth A₁ A₂ Γ (by have h' : Δ' ~ [A₁ & A₂] := perm_neg h' rfl; perm_count [h']) p₁ p₂
      | .plus₁ _ _ q =>
        (ih A₁ (by simp only [Form.size]; omega) Γ Δ' p₁ (.refl _) q (.refl _)).exch
          (by perm_count [])
      | .plus₂ _ _ q =>
        (ih A₂ (by simp only [Form.size]; omega) Γ Δ' p₂ (.refl _) q (.refl _)).exch
          (by perm_count [])) d₂ Δ e₂).exch
      (by perm_count [])
  -- ⊕ on the left, & on the right
  | _, Γ, .plus₁ A₁ A₂ p, ih, e₂ =>
    (push (C := A₁ᗮ & A₂ᗮ) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' =>
        .plus₁ A₁ A₂ Γ (by have h' : Δ' ~ [.plus A₁ A₂] := perm_neg h' rfl; perm_count [h']) p
      | .wth _ _ q₁ _ =>
        (ih A₁ (by simp only [Form.size]; omega) Γ Δ' p (.refl _) q₁ (.refl _)).exch
          (by perm_count [])) d₂ Δ e₂).exch
      (by perm_count [])
  | _, Γ, .plus₂ A₁ A₂ p, ih, e₂ =>
    (push (C := A₁ᗮ & A₂ᗮ) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' =>
        .plus₂ A₁ A₂ Γ (by have h' : Δ' ~ [.plus A₁ A₂] := perm_neg h' rfl; perm_count [h']) p
      | .wth _ _ _ q₂ =>
        (ih A₂ (by simp only [Form.size]; omega) Γ Δ' p (.refl _) q₂ (.refl _)).exch
          (by perm_count [])) d₂ Δ e₂).exch
      (by perm_count [])
  -- 𝟏 on the left, ⊥ on the right
  | _, Γ, .one h, _, e₂ =>
    (push (C := ⊥) (Δ := []) (fun Δ' pr =>
      match pr with
      | .ax _ h' => .one (by have h' : Δ' ~ [𝟏] := h'; perm_count [h'])
      | .bot q => q.exch (by perm_count [])) d₂ Δ e₂).exch
      (by perm_count [h])
  -- ⊥ on the left, 𝟏 on the right
  | _, Γ, .bot p, _, e₂ =>
    (push (C := 𝟏) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' => .bot Γ (by have h' : Δ' ~ [⊥] := h'; perm_count [h']) p
      | .one h' => p.exch (by perm_count [h'])) d₂ Δ e₂).exch
      (by perm_count [])
  -- ⊗ on the left, ⅋ on the right: two cuts
  | _, Γ, .tensor A₁ A₂ Γ₁ Γ₂ h p₁ p₂, ih, e₂ =>
    (push (C := A₁ᗮ ⅋ A₂ᗮ) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' =>
        .tensor A₁ A₂ Γ₁ Γ₂
          (by have h' : Δ' ~ [A₁ ⊗ A₂] := perm_neg h' rfl; perm_count [h', h]) p₁ p₂
      | .par _ _ q =>
        -- q : ⊢ A₁⊥, A₂⊥, Δ'
        let r₁ : CF (Γ₁ ++ A₂ᗮ :: Δ') :=
          ih A₁ (by simp only [Form.size]; omega) Γ₁ (A₂ᗮ :: Δ') p₁ (.refl _) q (.refl _)
        let r₂ : CF (Γ₂ ++ (Γ₁ ++ Δ')) :=
          ih A₂ (by simp only [Form.size]; omega) Γ₂ (Γ₁ ++ Δ') p₂ (.refl _) r₁
            (by perm_count [])
        r₂.exch (by perm_count [h])) d₂ Δ e₂).exch
      (by perm_count [])
  -- ⅋ on the left, ⊗ on the right: two cuts
  | _, Γ, .par A₁ A₂ p, ih, e₂ =>
    (push (C := A₁ᗮ ⊗ A₂ᗮ) (Δ := Γ) (fun Δ' pr =>
      match pr with
      | .ax _ h' =>
        .par A₁ A₂ Γ (by have h' : Δ' ~ [A₁ ⅋ A₂] := perm_neg h' rfl; perm_count [h']) p
      | .tensor _ _ Δ₁ Δ₂ h' q₁ q₂ =>
        -- p : ⊢ A₁, A₂, Γ;  q₁ : ⊢ A₁⊥, Δ₁;  q₂ : ⊢ A₂⊥, Δ₂
        let r₁ : CF (A₂ :: (Γ ++ Δ₁)) :=
          ih A₁ (by simp only [Form.size]; omega) (A₂ :: Γ) Δ₁ p (.refl _) q₁ (.refl _)
        let r₂ : CF ((Γ ++ Δ₁) ++ Δ₂) :=
          ih A₂ (by simp only [Form.size]; omega) (Γ ++ Δ₁) Δ₂ r₁ (.refl _) q₂ (.refl _)
        r₂.exch (by perm_count [h'])) d₂ Δ e₂).exch
      (by perm_count [])

/-- **A cut on `A`, from cuts on the smaller formulas**: the cut is pushed
up the left premise, and `reduce` is what is done at the rules that
introduce `A`. -/
def cutStep (A : Form) (ih : (B : Form) → B.size < A.size → CutAt B) : CutAt A :=
  fun Γ _ d₁ e₁ d₂ e₂ => push (fun _ pr => reduce d₂ pr ih e₂) d₁ Γ e₁

/-- **A cut on a formula of size at most `n`.**  The bound is there for
the recursion to be structural. -/
def cutN : (n : Nat) → (A : Form) → A.size ≤ n → CutAt A
  | 0, A, h => absurd h (by have := A.size_pos; omega)
  | n + 1, A, h => cutStep A fun B hB => cutN n B (by omega)

/-- **The cut rule is admissible without cut.** -/
def cutAdmissible : CutAdmissible :=
  fun A Γ Δ d₁ d₂ => cutN A.size A (Nat.le_refl _) Γ Δ d₁ (.refl _) d₂ (.refl _)

/-- **Cut elimination**, by recursion on the derivation: every rule but
cut as it is, on the results for its premises, and at a cut
`cutAdmissible` on the two results. -/
def cutElimination : CutElimination
  | _, .ax A h => .ax A h
  | _, .cut A Γ Δ h d₁ d₂ =>
    (cutAdmissible A Γ Δ (cutElimination _ d₁) (cutElimination _ d₂)).exch h.symm
  | _, .top Γ h => .top Γ h
  | _, .wth A B Γ h d₁ d₂ => .wth A B Γ h (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .plus₁ A B Γ h d => .plus₁ A B Γ h (cutElimination _ d)
  | _, .plus₂ A B Γ h d => .plus₂ A B Γ h (cutElimination _ d)
  | _, .one h => .one h
  | _, .bot Γ h d => .bot Γ h (cutElimination _ d)
  | _, .tensor A B Γ Δ h d₁ d₂ => .tensor A B Γ Δ h (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .par A B Γ h d => .par A B Γ h (cutElimination _ d)

/-! ## Inversions, each by one cut -/

/-- **⅋ is invertible**: a cut against `⊢ A⊥ ⊗ B⊥, A, B`. -/
def parInversion : ParInversion := fun A B Γ d =>
  (cutAdmissible (A ⅋ B) Γ [A, B] d
    (.tensor Aᗮ Bᗮ [A] [B] (.refl _) (.ax A (.swap ..)) (.ax B (.swap ..)))).exch
    (by perm_count [])

/-- **⊥ is invertible**: a cut against `⊢ 𝟏`. -/
def botInversion : BotInversion := fun Γ d =>
  (cutAdmissible ⊥ Γ [] d (.one (.refl _))).exch (by perm_count [])

/-- **& is invertible**: cuts against `⊢ A⊥ ⊕ B⊥, A` and
`⊢ A⊥ ⊕ B⊥, B`. -/
def withInversion : WithInversion := fun A B Γ d =>
  ((cutAdmissible (A & B) Γ [A] d
      (.plus₁ Aᗮ Bᗮ [A] (.refl _) (.ax A (.swap ..)))).exch (by perm_count []),
   (cutAdmissible (A & B) Γ [B] d
      (.plus₂ Aᗮ Bᗮ [B] (.refl _) (.ax B (.swap ..)))).exch (by perm_count []))

end MALL

#axioms_within_file [propext, Quot.sound]
