/-
Cut elimination for dual intuitionistic linear logic, as a function on
derivations: the cut on a linear hypothesis and the cut on a valid
hypothesis are admissible without cut (`cutAdmissible`,
`cutUAdmissible`), and so every derivation has one without cut
(`cutElimination`).

Source: CCP Theorem 3 (p. 12); Pfenning's notes, Theorem 3.8.  The
induction there is on the cut formula, then the linear cut before the
unrestricted one at the same formula, then the two derivations.

The two cuts are stated with three unrestricted zones, `Γ₁` of the left
premise, `Γ₂` of the right premise and `Γ'` of the conclusion, of which
only inclusions are asked (`CutLAt`, `CutUAt`).  So where a cut goes up
past !L, which puts a formula into the zone of one premise, the other
premise is not weakened, and every recursion is structural (the three on
derivations are stated over a sequent `j : Seq`, with `j.unr`, `j.lin`
and `j.goal` in their types: Lean's structural recursion wants the index
of the family to be a variable):

1. the size of the cut formula (`cutN`, by recursion on a bound);
2. at one formula `A`, the linear cut (`pushR`, `pushL`) before the
   unrestricted one (`pushU`): the case of copy on `A` in `pushU` is a
   linear cut on `A`, and the case of `!` in `pushL` an unrestricted cut
   on a smaller formula;
3. for the linear cut, the right premise (`pushR`, up to the rule that
   introduces `A` on the left, or init), then the left premise (`pushL`,
   up to the rule that introduces `A` on the right, or init); for the
   unrestricted cut, the right premise (`pushU`).

Theory file: it ends with its bound on axioms.
-/
import DILL.Statements

namespace DILL

open List

namespace Cut

/-- Every member of `Γ` is a member of `Γ'`. -/
abbrev Incl (Γ Γ' : List Form) : Prop := ∀ B, B ∈ Γ → B ∈ Γ'

/-- **A cut on a linear hypothesis `A`**, the zones of the premises
inside the zone of the conclusion, the linear zone of the right premise
up to permutation. -/
abbrev CutLAt (A : Form) : Type :=
  {Γ₁ Γ₂ Γ' Δ Ξ : List Form} → {C : Form} → (Δ' : List Form) → Incl Γ₁ Γ' → Incl Γ₂ Γ' →
    CF (Γ₁ ⨾ Δ ⟹ A) → CF (Γ₂ ⨾ Ξ ⟹ C) → Ξ ~ A :: Δ' → CF (Γ' ⨾ Δ ++ Δ' ⟹ C)

/-- **A cut on a valid hypothesis `A`**: the zone of the right premise
is inside the zone of the conclusion with `A`. -/
abbrev CutUAt (A : Form) : Type :=
  {Γ₁ Γ₂ Γ' Δ' : List Form} → {C : Form} → Incl Γ₁ Γ' → (∀ B, B ∈ Γ₂ → B = A ∨ B ∈ Γ') →
    CF (Γ₁ ⨾ [] ⟹ A) → CF (Γ₂ ⨾ Δ' ⟹ C) → CF (Γ' ⨾ Δ' ⟹ C)

/-- The same derivation, at an equal conclusion. -/
def castGoal {Γ Δ : List Form} {A B : Form} (h : A = B) (d : CF (Γ ⨾ Δ ⟹ A)) :
    CF (Γ ⨾ Δ ⟹ B) := h ▸ d

/-- **A last rule that introduces `A` on the left**: the conclusion is
`Γ ; A, Δ ⟹ C`, and `A` is the principal formula.  What `pushR` finds at
the top of a cut on `A`. -/
inductive LPrin (Γ : List Form) : Form → List Form → Form → Type where
  | tensorL (A B : Form) {Δ : List Form} {C : Form}
      (d : CF (Γ ⨾ A :: B :: Δ ⟹ C)) : LPrin Γ (A ⊗ B) Δ C
  | oneL {Δ : List Form} {C : Form} (d : CF (Γ ⨾ Δ ⟹ C)) : LPrin Γ 𝟏 Δ C
  | lolliL (A B : Form) (Δ₁ Δ₂ : List Form) {Δ : List Form} {C : Form} (h : Δ ~ Δ₁ ++ Δ₂)
      (d₁ : CF (Γ ⨾ Δ₁ ⟹ A)) (d₂ : CF (Γ ⨾ B :: Δ₂ ⟹ C)) : LPrin Γ (A ⊸ B) Δ C
  | withL₁ (A B : Form) {Δ : List Form} {C : Form}
      (d : CF (Γ ⨾ A :: Δ ⟹ C)) : LPrin Γ (A & B) Δ C
  | withL₂ (A B : Form) {Δ : List Form} {C : Form}
      (d : CF (Γ ⨾ B :: Δ ⟹ C)) : LPrin Γ (A & B) Δ C
  | zeroL {Δ : List Form} {C : Form} : LPrin Γ 𝟎 Δ C
  | plusL (A B : Form) {Δ : List Form} {C : Form}
      (d₁ : CF (Γ ⨾ A :: Δ ⟹ C)) (d₂ : CF (Γ ⨾ B :: Δ ⟹ C)) : LPrin Γ (A ⊕ B) Δ C
  | bangL (A : Form) {Δ : List Form} {C : Form}
      (d : CF (A :: Γ ⨾ Δ ⟹ C)) : LPrin Γ (!A) Δ C

/-- The same rule, at an equal principal formula. -/
def LPrin.cast {Γ Δ : List Form} {A A' C : Form} (h : A = A') (p : LPrin Γ A Δ C) :
    LPrin Γ A' Δ C := h ▸ p

/-- The derivation that ends with the rule. -/
def LPrin.toCF {Γ : List Form} : {A : Form} → {Δ : List Form} → {C : Form} →
    LPrin Γ A Δ C → CF (Γ ⨾ A :: Δ ⟹ C)
  | _, _, _, .tensorL A B d => .tensorL A B _ (.refl _) d
  | _, _, _, .oneL d => .oneL _ (.refl _) d
  | _, _, _, .lolliL A B Δ₁ Δ₂ h d₁ d₂ => .lolliL A B Δ₁ Δ₂ (h.cons _) d₁ d₂
  | _, _, _, .withL₁ A B d => .withL₁ A B _ (.refl _) d
  | _, _, _, .withL₂ A B d => .withL₂ A B _ (.refl _) d
  | _, _, _, .zeroL => .zeroL _ (.refl _)
  | _, _, _, .plusL A B d₁ d₂ => .plusL A B _ (.refl _) d₁ d₂
  | _, _, _, .bangL A d => .bangL A _ (.refl _) d

/-! ## The linear cut, pushed up the left premise -/

/-- **A linear cut on `A`, pushed up its left premise** `j`, that is
`Γ₁ ; Δ ⟹ A`, the right premise ending with the rule `p` that introduces `A`.  A left
rule or copy of the left premise is applied below the cut; at init the
result is the right premise; at the right rule for `A` the two rules
meet, and the result is by cuts on the immediate subformulas (`ihL`,
and `ihU` for `!`). -/
def pushL {Γ₂ Δ' : List Form} {C : Form} :
    {j : Seq} → CF j → LPrin Γ₂ j.goal Δ' C →
      ((B : Form) → B.size < j.goal.size → CutLAt B) →
      ((B : Form) → B.size < j.goal.size → CutUAt B) →
      (Γ' : List Form) → Incl j.unr Γ' → Incl Γ₂ Γ' → CF (Γ' ⨾ j.lin ++ Δ' ⟹ C)
  -- init on the left: the right premise is the result
  | _, .init _ h, p, _, _, _, _, s₂ => (p.toCF.mono s₂).exch (by perm_count [h])
  -- copy and the left rules: the cut goes to the premise that has the goal `A`
  | _, .copy B hΓ d, p, ihL, ihU, Γ', s₁, s₂ =>
    .copy B (s₁ B hΓ) (pushL d p ihL ihU Γ' s₁ s₂)
  | _, .tensorL A₁ B₁ Δ₀ h d, p, ihL, ihU, Γ', s₁, s₂ =>
    .tensorL A₁ B₁ (Δ₀ ++ Δ') (by perm_count [h]) (pushL d p ihL ihU Γ' s₁ s₂)
  | _, .oneL Δ₀ h d, p, ihL, ihU, Γ', s₁, s₂ =>
    .oneL (Δ₀ ++ Δ') (by perm_count [h]) (pushL d p ihL ihU Γ' s₁ s₂)
  | _, .lolliL A₁ B₁ Δ₁ Δ₂ h d₁ d₂, p, ihL, ihU, Γ', s₁, s₂ =>
    .lolliL A₁ B₁ Δ₁ (Δ₂ ++ Δ') (by perm_count [h]) (d₁.mono s₁) (pushL d₂ p ihL ihU Γ' s₁ s₂)
  | _, .withL₁ A₁ B₁ Δ₀ h d, p, ihL, ihU, Γ', s₁, s₂ =>
    .withL₁ A₁ B₁ (Δ₀ ++ Δ') (by perm_count [h]) (pushL d p ihL ihU Γ' s₁ s₂)
  | _, .withL₂ A₁ B₁ Δ₀ h d, p, ihL, ihU, Γ', s₁, s₂ =>
    .withL₂ A₁ B₁ (Δ₀ ++ Δ') (by perm_count [h]) (pushL d p ihL ihU Γ' s₁ s₂)
  | _, .zeroL Δ₀ h, _, _, _, _, _, _ => .zeroL (Δ₀ ++ Δ') (by perm_count [h])
  | _, .plusL A₁ B₁ Δ₀ h d₁ d₂, p, ihL, ihU, Γ', s₁, s₂ =>
    .plusL A₁ B₁ (Δ₀ ++ Δ') (by perm_count [h])
      (pushL d₁ p ihL ihU Γ' s₁ s₂) (pushL d₂ p ihL ihU Γ' s₁ s₂)
  | _, .bangL B Δ₀ h d, p, ihL, ihU, Γ', s₁, s₂ =>
    .bangL B (Δ₀ ++ Δ') (by perm_count [h])
      (pushL d p ihL ihU (B :: Γ') (cons_sub s₁) (fun x hx => .tail _ (s₂ x hx)))
  -- ⊗R meets ⊗L: two cuts
  | _, .tensorR (A := A₁) (B := B₁) Δ₁ Δ₂ h d₁ d₂, p, ihL, _, Γ', s₁, s₂ =>
    match p with
    | .tensorL _ _ e =>
      let r₁ : CF (Γ' ⨾ Δ₁ ++ B₁ :: Δ' ⟹ C) :=
        ihL A₁ (by simp only [Form.size]; omega) (B₁ :: Δ') s₁ s₂ d₁ e (.refl _)
      let r₂ : CF (Γ' ⨾ Δ₂ ++ (Δ₁ ++ Δ') ⟹ C) :=
        ihL B₁ (by simp only [Form.size]; omega) (Δ₁ ++ Δ') s₁ (fun _ hx => hx) d₂ r₁
          (by perm_count [])
      r₂.exch (by perm_count [h])
  -- 1R meets 1L
  | _, .oneR h, p, _, _, _, _, s₂ =>
    match p with
    | .oneL e => (e.mono s₂).exch (by perm_count [h])
  -- ⊸R meets ⊸L: two cuts
  | _, .lolliR (Ξ := Δ) (A := A₁) (B := B₁) d, p, ihL, _, Γ', s₁, s₂ =>
    match p with
    | .lolliL _ _ Δ₁ Δ₂ h' e₁ e₂ =>
      let r₁ : CF (Γ' ⨾ Δ₁ ++ Δ ⟹ B₁) :=
        ihL A₁ (by simp only [Form.size]; omega) Δ s₂ s₁ e₁ d (.refl _)
      let r₂ : CF (Γ' ⨾ (Δ₁ ++ Δ) ++ Δ₂ ⟹ C) :=
        ihL B₁ (by simp only [Form.size]; omega) Δ₂ (fun _ hx => hx) s₂ r₁ e₂ (.refl _)
      r₂.exch (by perm_count [h'])
  -- &R meets &L₁ or &L₂
  | _, .withR (A := A₁) (B := B₁) d₁ d₂, p, ihL, _, _, s₁, s₂ =>
    match p with
    | .withL₁ _ _ e => ihL A₁ (by simp only [Form.size]; omega) Δ' s₁ s₂ d₁ e (.refl _)
    | .withL₂ _ _ e => ihL B₁ (by simp only [Form.size]; omega) Δ' s₁ s₂ d₂ e (.refl _)
  -- ⊤R: no rule introduces ⊤ on the left
  | _, .topR, p, _, _, _, _, _ => nomatch p
  -- ⊕R₁, ⊕R₂ meet ⊕L
  | _, .plusR₁ (A := A₁) d, p, ihL, _, _, s₁, s₂ =>
    match p with
    | .plusL _ _ e₁ _ => ihL A₁ (by simp only [Form.size]; omega) Δ' s₁ s₂ d e₁ (.refl _)
  | _, .plusR₂ (B := B₁) d, p, ihL, _, _, s₁, s₂ =>
    match p with
    | .plusL _ _ _ e₂ => ihL B₁ (by simp only [Form.size]; omega) Δ' s₁ s₂ d e₂ (.refl _)
  -- !R meets !L: an unrestricted cut on the smaller formula
  | _, .bangR (A := A₁) h d, p, _, ihU, _, s₁, s₂ =>
    match p with
    | .bangL _ e =>
      (ihU A₁ (by simp only [Form.size]; omega) s₁
        (fun B hB => (List.mem_cons.1 hB).imp id (s₂ B)) d e).exch (by perm_count [h])

/-! ## The linear cut, pushed up the right premise -/

/-- **A linear cut on `A`, pushed up its right premise** `j`, that is
`Γ₂ ; Ξ ⟹ C` with `Ξ ~ A, Δ'`; `D` is the left premise.  At init the result is `D`.
At a left rule on `A` the cut goes on up `D` (`pushL`).  At any other
rule, `A` is in the linear zone of a premise: the cut goes to the
premises that have `A`, and the same rule is applied below; above !L the
zone of the conclusion has the new formula. -/
def pushR {A : Form} {Γ₁ Δ : List Form} (D : CF (Γ₁ ⨾ Δ ⟹ A))
    (ihL : (B : Form) → B.size < A.size → CutLAt B)
    (ihU : (B : Form) → B.size < A.size → CutUAt B) :
    {j : Seq} → CF j → (Γ' Δ' : List Form) →
      Incl Γ₁ Γ' → Incl j.unr Γ' → j.lin ~ A :: Δ' → CF (Γ' ⨾ Δ ++ Δ' ⟹ j.goal)
  | _, .init B h, _, Δ', s₁, _, e =>
    have hh : A :: Δ' = [B] := perm_singleton_eq (e.symm.trans h)
    have hΔ' : Δ' = [] := (List.cons.inj hh).2
    castGoal (List.cons.inj hh).1 ((D.mono s₁).exch (by subst hΔ'; perm_count []))
  | _, .copy B hΓ d, Γ', Δ', s₁, s₂, e =>
    .copy B (s₂ B hΓ)
      ((pushR D ihL ihU d Γ' (B :: Δ') s₁ s₂ (by perm_count [e])).exch (by perm_count []))
  | _, .tensorL A₁ B₁ Δ₀ h d, Γ', Δ', s₁, s₂, e =>
    if hP : A₁ ⊗ B₁ = A then
      (pushL D ((LPrin.tensorL A₁ B₁ d).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .tensorL A₁ B₁ (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        ((pushR D ihL ihU d Γ' (A₁ :: B₁ :: Δ₀.erase A) s₁ s₂ (by perm_count [hc.1])).exch
          (by perm_count []))
  | _, .tensorR Δ₁ Δ₂ h d₁ d₂, Γ', Δ', s₁, s₂, e =>
    have hm : A ∈ Δ₁ ++ Δ₂ := (h.symm.trans e).mem_iff.2 (List.mem_cons_self ..)
    if hm₁ : A ∈ Δ₁ then
      .tensorR (Δ ++ Δ₁.erase A) Δ₂ (by perm_count [h, e, perm_cons_erase hm₁])
        (pushR D ihL ihU d₁ Γ' (Δ₁.erase A) s₁ s₂ (perm_cons_erase hm₁)) (d₂.mono s₂)
    else
      have hm₂ : A ∈ Δ₂ := (List.mem_append.1 hm).resolve_left hm₁
      .tensorR Δ₁ (Δ ++ Δ₂.erase A) (by perm_count [h, e, perm_cons_erase hm₂]) (d₁.mono s₂)
        (pushR D ihL ihU d₂ Γ' (Δ₂.erase A) s₁ s₂ (perm_cons_erase hm₂))
  | _, .oneL Δ₀ h d, Γ', Δ', s₁, s₂, e =>
    if hP : 𝟏 = A then
      (pushL D ((LPrin.oneL d).cast hP) ihL ihU Γ' s₁ s₂).exch (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .oneL (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        (pushR D ihL ihU d Γ' (Δ₀.erase A) s₁ s₂ hc.1)
  | _, .oneR h, _, _, _, _, e =>
    absurd (perm_nil_eq (e.symm.trans h)) (List.cons_ne_nil _ _)
  | _, .lolliL A₁ B₁ Δ₁ Δ₂ h d₁ d₂, Γ', Δ', s₁, s₂, e =>
    if hP : A₁ ⊸ B₁ = A then
      pushL D ((LPrin.lolliL A₁ B₁ Δ₁ Δ₂ (by subst hP; perm_count [h, e]) d₁ d₂).cast hP)
        ihL ihU Γ' s₁ s₂
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      have hm : A ∈ Δ₁ ++ Δ₂ := hc.1.mem_iff.2 (List.mem_cons_self ..)
      if hm₁ : A ∈ Δ₁ then
        .lolliL A₁ B₁ (Δ ++ Δ₁.erase A) Δ₂ (by perm_count [h, e, perm_cons_erase hm₁])
          (pushR D ihL ihU d₁ Γ' (Δ₁.erase A) s₁ s₂ (perm_cons_erase hm₁)) (d₂.mono s₂)
      else
        have hm₂ : A ∈ Δ₂ := (List.mem_append.1 hm).resolve_left hm₁
        .lolliL A₁ B₁ Δ₁ (Δ ++ Δ₂.erase A) (by perm_count [h, e, perm_cons_erase hm₂])
          (d₁.mono s₂)
          ((pushR D ihL ihU d₂ Γ' (B₁ :: Δ₂.erase A) s₁ s₂
            (by perm_count [perm_cons_erase hm₂])).exch (by perm_count []))
  | _, .lolliR (A := A₁) d, Γ', Δ', s₁, s₂, e =>
    .lolliR ((pushR D ihL ihU d Γ' (A₁ :: Δ') s₁ s₂ (by perm_count [e])).exch
      (by perm_count []))
  | _, .withL₁ A₁ B₁ Δ₀ h d, Γ', Δ', s₁, s₂, e =>
    if hP : A₁ & B₁ = A then
      (pushL D ((LPrin.withL₁ A₁ B₁ d).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .withL₁ A₁ B₁ (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        ((pushR D ihL ihU d Γ' (A₁ :: Δ₀.erase A) s₁ s₂ (by perm_count [hc.1])).exch
          (by perm_count []))
  | _, .withL₂ A₁ B₁ Δ₀ h d, Γ', Δ', s₁, s₂, e =>
    if hP : A₁ & B₁ = A then
      (pushL D ((LPrin.withL₂ A₁ B₁ d).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .withL₂ A₁ B₁ (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        ((pushR D ihL ihU d Γ' (B₁ :: Δ₀.erase A) s₁ s₂ (by perm_count [hc.1])).exch
          (by perm_count []))
  | _, .withR d₁ d₂, Γ', Δ', s₁, s₂, e =>
    .withR (pushR D ihL ihU d₁ Γ' Δ' s₁ s₂ e) (pushR D ihL ihU d₂ Γ' Δ' s₁ s₂ e)
  | _, .topR, _, _, _, _, _ => .topR
  | _, .zeroL (Γ := Γ₂) (C := C) Δ₀ h, Γ', Δ', s₁, s₂, e =>
    if hP : 𝟎 = A then
      (pushL D ((LPrin.zeroL (Γ := Γ₂) (Δ := Δ₀) (C := C)).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .zeroL (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
  | _, .plusL A₁ B₁ Δ₀ h d₁ d₂, Γ', Δ', s₁, s₂, e =>
    if hP : (A₁ ⊕ B₁) = A then
      (pushL D ((LPrin.plusL A₁ B₁ d₁ d₂).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .plusL A₁ B₁ (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        ((pushR D ihL ihU d₁ Γ' (A₁ :: Δ₀.erase A) s₁ s₂ (by perm_count [hc.1])).exch
          (by perm_count []))
        ((pushR D ihL ihU d₂ Γ' (B₁ :: Δ₀.erase A) s₁ s₂ (by perm_count [hc.1])).exch
          (by perm_count []))
  | _, .plusR₁ d, Γ', Δ', s₁, s₂, e => .plusR₁ (pushR D ihL ihU d Γ' Δ' s₁ s₂ e)
  | _, .plusR₂ d, Γ', Δ', s₁, s₂, e => .plusR₂ (pushR D ihL ihU d Γ' Δ' s₁ s₂ e)
  | _, .bangL B Δ₀ h d, Γ', Δ', s₁, s₂, e =>
    if hP : Form.bang B = A then
      (pushL D ((LPrin.bangL B d).cast hP) ihL ihU Γ' s₁ s₂).exch
        (by subst hP; perm_count [h, e])
    else
      have hc := perm_cons_cases (h.symm.trans e) hP
      .bangL B (Δ ++ Δ₀.erase A) (by perm_count [hc.2])
        (pushR D ihL ihU d (B :: Γ') (Δ₀.erase A) (fun x hx => .tail _ (s₁ x hx))
          (cons_sub s₂) hc.1)
  | _, .bangR h _, _, _, _, _, e =>
    absurd (perm_nil_eq (e.symm.trans h)) (List.cons_ne_nil _ _)

/-! ## The unrestricted cut -/

/-- **A cut on a valid hypothesis `A`, pushed up its right premise** `j`,
that is `Γ₂ ; Ξ ⟹ C`; `D` is the left premise, `Γ₁ ; · ⟹ A`.  Every rule is
applied again below, on the results for its premises; at copy on `A`,
the copied `A` is cut by the linear cut on `A` (`cl`) against `D`. -/
def pushU {A : Form} {Γ₁ : List Form} (cl : CutLAt A) (D : CF (Γ₁ ⨾ [] ⟹ A)) :
    {j : Seq} → CF j → (Γ' : List Form) → Incl Γ₁ Γ' →
      (∀ B, B ∈ j.unr → B = A ∨ B ∈ Γ') → CF (Γ' ⨾ j.lin ⟹ j.goal)
  | _, .init B h, _, _, _ => .init B h
  | _, .copy (Ξ := Ξ) B hΓ d, Γ', s₁, s₂ =>
    if hB : B = A then
      cl Ξ s₁ (fun _ hx => hx) D (pushU cl D d Γ' s₁ s₂) (by subst hB; exact .refl _)
    else .copy B ((s₂ B hΓ).resolve_left hB) (pushU cl D d Γ' s₁ s₂)
  | _, .tensorL A₁ B₁ Δ₀ h d, Γ', s₁, s₂ => .tensorL A₁ B₁ Δ₀ h (pushU cl D d Γ' s₁ s₂)
  | _, .tensorR Δ₁ Δ₂ h d₁ d₂, Γ', s₁, s₂ =>
    .tensorR Δ₁ Δ₂ h (pushU cl D d₁ Γ' s₁ s₂) (pushU cl D d₂ Γ' s₁ s₂)
  | _, .oneL Δ₀ h d, Γ', s₁, s₂ => .oneL Δ₀ h (pushU cl D d Γ' s₁ s₂)
  | _, .oneR h, _, _, _ => .oneR h
  | _, .lolliL A₁ B₁ Δ₁ Δ₂ h d₁ d₂, Γ', s₁, s₂ =>
    .lolliL A₁ B₁ Δ₁ Δ₂ h (pushU cl D d₁ Γ' s₁ s₂) (pushU cl D d₂ Γ' s₁ s₂)
  | _, .lolliR d, Γ', s₁, s₂ => .lolliR (pushU cl D d Γ' s₁ s₂)
  | _, .withL₁ A₁ B₁ Δ₀ h d, Γ', s₁, s₂ => .withL₁ A₁ B₁ Δ₀ h (pushU cl D d Γ' s₁ s₂)
  | _, .withL₂ A₁ B₁ Δ₀ h d, Γ', s₁, s₂ => .withL₂ A₁ B₁ Δ₀ h (pushU cl D d Γ' s₁ s₂)
  | _, .withR d₁ d₂, Γ', s₁, s₂ =>
    .withR (pushU cl D d₁ Γ' s₁ s₂) (pushU cl D d₂ Γ' s₁ s₂)
  | _, .topR, _, _, _ => .topR
  | _, .zeroL Δ₀ h, _, _, _ => .zeroL Δ₀ h
  | _, .plusL A₁ B₁ Δ₀ h d₁ d₂, Γ', s₁, s₂ =>
    .plusL A₁ B₁ Δ₀ h (pushU cl D d₁ Γ' s₁ s₂) (pushU cl D d₂ Γ' s₁ s₂)
  | _, .plusR₁ d, Γ', s₁, s₂ => .plusR₁ (pushU cl D d Γ' s₁ s₂)
  | _, .plusR₂ d, Γ', s₁, s₂ => .plusR₂ (pushU cl D d Γ' s₁ s₂)
  | _, .bangL B Δ₀ h d, Γ', s₁, s₂ =>
    .bangL B Δ₀ h (pushU cl D d (B :: Γ') (fun x hx => .tail _ (s₁ x hx)) (fun x hx => by
      rcases List.mem_cons.1 hx with hx | hx
      · exact .inr (hx ▸ List.mem_cons_self ..)
      · exact (s₂ x hx).imp id (List.mem_cons_of_mem _)))
  | _, .bangR h d, Γ', s₁, s₂ => .bangR h (pushU cl D d Γ' s₁ s₂)

/-! ## The two cuts, by the size of the cut formula -/

/-- The two cuts on `A`. -/
structure Cuts (A : Form) where
  /-- The cut on a linear hypothesis. -/
  lin : CutLAt A
  /-- The cut on a valid hypothesis. -/
  unr : CutUAt A

/-- **The two cuts on a formula of size at most `n`.**  The bound is
there for the recursion to be structural. -/
def cutN : (n : Nat) → (A : Form) → A.size ≤ n → Cuts A
  | 0, A, h => absurd h (by have := A.size_pos; omega)
  | n + 1, A, h =>
    let cl : CutLAt A := fun Δ' s₁ s₂ D E e =>
      pushR D (fun B hB => (cutN n B (by omega)).lin) (fun B hB => (cutN n B (by omega)).unr)
        E _ Δ' s₁ s₂ e
    ⟨cl, fun s₁ s₂ D E => pushU cl D E _ s₁ s₂⟩

end Cut

/-- **The cut on a linear hypothesis is admissible without cut** (CCP
Theorem 3, with Principle 7.2). -/
def cutAdmissible : CutAdmissible := fun _ _ Δ' A _ d₁ d₂ =>
  (Cut.cutN A.size A (Nat.le_refl _)).lin Δ' (fun _ h => h) (fun _ h => h) d₁ d₂ (.refl _)

/-- **The cut on a valid hypothesis is admissible without cut** (CCP
Theorem 3, with Principle 7.1). -/
def cutUAdmissible : CutUAdmissible := fun _ _ A _ d₁ d₂ =>
  (Cut.cutN A.size A (Nat.le_refl _)).unr (fun _ h => h) (fun _ h => List.mem_cons.1 h) d₁ d₂

/-- **Cut elimination** (Pfenning 3.9), by recursion on the derivation:
every rule but the cuts as it is, on the results for its premises; at a
cut, the admissible cut on the two results. -/
def cutElimination : CutElimination
  | _, .init A h => .init A h
  | _, .copy A hΓ d => .copy A hΓ (cutElimination _ d)
  | _, .tensorL A B Δ h d => .tensorL A B Δ h (cutElimination _ d)
  | _, .tensorR Δ Δ' h d₁ d₂ => .tensorR Δ Δ' h (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .oneL Δ h d => .oneL Δ h (cutElimination _ d)
  | _, .oneR h => .oneR h
  | _, .lolliL A B Δ Δ' h d₁ d₂ =>
    .lolliL A B Δ Δ' h (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .lolliR d => .lolliR (cutElimination _ d)
  | _, .withL₁ A B Δ h d => .withL₁ A B Δ h (cutElimination _ d)
  | _, .withL₂ A B Δ h d => .withL₂ A B Δ h (cutElimination _ d)
  | _, .withR d₁ d₂ => .withR (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .topR => .topR
  | _, .zeroL Δ h => .zeroL Δ h
  | _, .plusL A B Δ h d₁ d₂ => .plusL A B Δ h (cutElimination _ d₁) (cutElimination _ d₂)
  | _, .plusR₁ d => .plusR₁ (cutElimination _ d)
  | _, .plusR₂ d => .plusR₂ (cutElimination _ d)
  | _, .bangL A Δ h d => .bangL A Δ h (cutElimination _ d)
  | _, .bangR h d => .bangR h (cutElimination _ d)
  | _, .cut _ A Δ Δ' h d₁ d₂ =>
    (cutAdmissible _ Δ Δ' A _ (cutElimination _ d₁) (cutElimination _ d₂)).exch h.symm
  | _, .cutU _ A d₁ d₂ => cutUAdmissible _ _ A _ (cutElimination _ d₁) (cutElimination _ d₂)

/-! ## Tests: the function computes -/

namespace Cut

/-- One cut, on `a ⊗ b`: `· ; a, b ⟹ a ⊗ b` against
`· ; a ⊗ b ⟹ b ⊗ a`. -/
def exCut : Fam true ([] ⨾ [.atom 0, .atom 1] ⟹ .atom 1 ⊗ .atom 0) :=
  .cut rfl (.atom 0 ⊗ .atom 1) [.atom 0, .atom 1] [] (by decide)
    (.tensorR [.atom 0] [.atom 1] (.refl _) (.init _ (.refl _)) (.init _ (.refl _)))
    (.tensorL (.atom 0) (.atom 1) [] (.refl _)
      (.tensorR [.atom 1] [.atom 0] (by decide) (.init _ (.refl _)) (.init _ (.refl _))))

/-- One cut on a valid hypothesis, `a ⊸ a`, which the right premise
copies twice: `· ; · ⟹ a ⊸ a` against `a ⊸ a ; a ⟹ a`. -/
def exCutU : Fam true ([] ⨾ [.atom 0] ⟹ .atom 0) :=
  .cutU rfl (.atom 0 ⊸ .atom 0) (.lolliR (.init _ (.refl _)))
    (.copy (.atom 0 ⊸ .atom 0) (.head _)
      (.lolliL (.atom 0) (.atom 0) [.atom 0] [] (.refl _)
        (.copy (.atom 0 ⊸ .atom 0) (.head _)
          (.lolliL (.atom 0) (.atom 0) [.atom 0] [] (.refl _)
            (.init _ (.refl _)) (.init _ (.refl _))))
        (.init _ (.refl _))))

/-- One cut, on `!(a & a)`, which the right premise copies twice:
`· ; !a ⟹ !(a & a)` against `· ; !(a & a) ⟹ a ⊗ a`. -/
def exBang : Fam true ([] ⨾ [!(.atom 0)] ⟹ .atom 0 ⊗ .atom 0) :=
  .cut rfl (!(.atom 0 & .atom 0)) [!(.atom 0)] [] (by decide)
    (.bangL (.atom 0) [] (.refl _)
      (.bangR (.refl _) (.withR
        (.copy (.atom 0) (.head _) (.init _ (.refl _)))
        (.copy (.atom 0) (.head _) (.init _ (.refl _))))))
    (.bangL (.atom 0 & .atom 0) [] (.refl _)
      (.copy (.atom 0 & .atom 0) (.head _)
        (.copy (.atom 0 & .atom 0) (.head _)
          (.tensorR [.atom 0 & .atom 0] [.atom 0 & .atom 0] (.refl _)
            (.withL₁ (.atom 0) (.atom 0) [] (.refl _) (.init _ (.refl _)))
            (.withL₂ (.atom 0) (.atom 0) [] (.refl _) (.init _ (.refl _)))))))

example : CF ([] ⨾ [.atom 0, .atom 1] ⟹ .atom 1 ⊗ .atom 0) := cutElimination _ exCut
example : CF ([] ⨾ [.atom 0] ⟹ .atom 0) := cutElimination _ exCutU
example : CF ([] ⨾ [!(.atom 0)] ⟹ .atom 0 ⊗ .atom 0) := cutElimination _ exBang

#eval (cutElimination _ exCut).height
#eval (cutElimination _ exCutU).height
#eval (cutElimination _ exBang).height

/-
`decide` does not prove these heights: `Fam.exch` of `DILL/System.lean`
is compiled by well-founded recursion (its index `Γ ⨾ Ξ ⟹ C` is not a
variable), and neither `decide` nor the kernel reduces it.  The three
recursions of this file are structural: they are stated over a sequent
`j` for that reason.
-/

end Cut

end DILL

#axioms_within_file [propext, Quot.sound]
