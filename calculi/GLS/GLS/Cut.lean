/-
Goal 6: cut admissibility for GLS by the source's induction, a function
that makes a derivation of the conclusion of a cut from the derivations of
its two premises.

Source: the Coq file `GL/GLS_additive_cut.v` (`GLS_cut_adm_main`,
`GLS_cut_adm`) of `ianshil/CE_GLS`: induction on the size of the cut
formula, then on the measure that ends proof search in PSGLS at the
conclusion of the cut.  The source's second measure is `mhd`, the maximal
height of a derivation in PSGLS; here it is `weight U`
(`GLS/Measure.lean`), which falls from the conclusion of a rule of PSGLS to
each premise (`PSPrem.step`).

Nothing here uses the semantics: no model, no search, no soundness, no
completeness.  Theory file: it ends with its bound on axioms.
-/
import GLS.Contract
import GLS.Search

namespace GLS

/-- What GLR gives of what GLR gives: `xbox (xbox Γ)` is `xbox Γ` with
more formulas, up to a permutation. -/
theorem xbox_xbox_perm (Γ : List Form) :
    (xbox (xbox Γ)).Perm (xbox Γ ++ xbox (Γ.filterMap Form.unbox?)) := by
  induction Γ with
  | nil => exact .refl _
  | cons A Γ ih =>
    cases A with
    | var p =>
      have e : (Form.var p :: Γ).filterMap Form.unbox? = Γ.filterMap Form.unbox? := rfl
      rw [e]; perm_count [ih]
    | bot =>
      have e : (⊥ :: Γ).filterMap Form.unbox? = Γ.filterMap Form.unbox? := rfl
      rw [e]; perm_count [ih]
    | imp A₁ A₂ =>
      have e : ((A₁ ⟶ A₂) :: Γ).filterMap Form.unbox? = Γ.filterMap Form.unbox? := rfl
      rw [e]; perm_count [ih]
    | box E =>
      have e : (□E :: Γ).filterMap Form.unbox? = E :: Γ.filterMap Form.unbox? := rfl
      rw [e]; perm_count [ih]

/-- **The cut on the formulas of size at most `m`**, with the cut formula
at the head. -/
abbrev CutFor (m : Nat) : Type :=
  (A : Form) → (Γ Δ : List Form) → A.size ≤ m →
    Fam (Γ ⇒ A :: Δ) → Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ Δ)

/-- **The cut on the formulas of size at most `m + 1`, at the conclusions
of measure below `k`**: `U` holds every boxed subformula of the conclusion
`Γ ⇒ Δ`, and the measure of the conclusion relative to `U` is below `k`. -/
abbrev CutAt (m : Nat) (U : List Form) (k : Nat) : Type :=
  (A : Form) → (Γ Δ : List Form) → A.size ≤ m + 1 → Closed U (Γ ⇒ Δ) →
    weight U (Γ ⇒ Δ) < k → Fam (Γ ⇒ A :: Δ) → Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ Δ)

/-- **The cut on a boxed formula `□B`, principal in both premises, at a
conclusion `Γ ⇒ Δ` that is no axiom and has no implication at top level.**
The first premise ends with GLR on `□B`, from `d₀`.  The second can only
end with GLR, on some `□C` of `Δ`, from `e₀ : B, □B, xbox Γ, □C ⇒ C`.
Then: a cut on `B`, smaller, of `d₀` weakened with `e₀`; GLR on `□B` from
`d₀` weakened; a cut on `□B` at the premise `xbox Γ, □C ⇒ C` of GLR at the
conclusion, of smaller measure; and GLR on `□C`. -/
def cutBox {m : Nat} (ih : CutFor m) {U : List Form} {k : Nat} (rec : CutAt m U k)
    (B : Form) (Γ Δ : List Form) (hB : (□B).size ≤ m + 1) (hU : Closed U (Γ ⇒ Δ))
    (hw : weight U (Γ ⇒ Δ) < k + 1) (nP : ¬ (Γ ⇒ Δ).IsIdP) (nBot : ¬ (Γ ⇒ Δ).IsBotL)
    (nB : ¬ (Γ ⇒ Δ).IsIdB) (nR : ∀ A B, A ⟶ B ∉ Δ) (nL : ∀ A B, A ⟶ B ∉ Γ)
    (d₀ : Fam (xbox Γ ++ [□B] ⇒ [B])) (d₂ : Fam (□B :: Γ ⇒ Δ)) : Fam (Γ ⇒ Δ) :=
  match d₂ with
  | .idP p hΓ hΔ =>
      absurd ⟨p, mem_of_perm_cons_of_ne (.refl _) hΓ (fun h => by cases h), hΔ⟩ nP
  | .botL h => absurd (mem_of_perm_cons_of_ne (.refl _) h (fun h => by cases h)) nBot
  | .impR C D h _ => absurd h (nR C D)
  | .impL C D h _ _ =>
      absurd (mem_of_perm_cons_of_ne (.refl _) h (fun h => by cases h)) (nL C D)
  | .glr C hC e₀ =>
      have hs := (PSPrem.glr C nP nB nBot hC rfl :
        PSPrem (xbox Γ ++ [□C] ⇒ [C]) (Γ ⇒ Δ)).step hU
      -- the cut on `B`
      let d₀' : Fam (□B :: (xbox Γ ++ [□C]) ⇒ B :: [C]) :=
        (d₀.wk [□C] [C] _ _ (by perm_count []) (by perm_count [])).1
      let e₀' : Fam (B :: □B :: (xbox Γ ++ [□C]) ⇒ [C]) :=
        (e₀.le.ex (by perm_count []) (.refl _)).1
      let e₄ : Fam (□B :: (xbox Γ ++ [□C]) ⇒ [C]) :=
        ih B (□B :: (xbox Γ ++ [□C])) [C] (Nat.le_of_succ_le_succ hB) d₀' e₀'
      -- GLR on `□B`
      let e₅ : Fam (xbox Γ ++ [□C] ⇒ □B :: [C]) :=
        .glr B (List.mem_cons_self ..)
          (d₀.wk (xbox (Γ.filterMap Form.unbox?) ++ [C, □C]) [] _ _
            (by perm_count [xbox_xbox_perm Γ]) (by perm_count [])).1
      -- the cut on `□B` at the premise of GLR on `□C`, and GLR on `□C`
      .glr C hC
        (rec (□B) (xbox Γ ++ [□C]) [C] hB hs.1
          (Nat.lt_of_lt_of_le hs.2 (Nat.le_of_lt_succ hw)) e₅ e₄)

/-- **The cut at a conclusion `Γ ⇒ Δ` that is no axiom and has no
implication at top level**, by the last rule of the first premise.  IdP on
`p`: the cut formula is `p`, and it is contracted in the second premise.
BotL and ImpL: there is none.  ImpR on `C ⟶ D`: it is the cut formula; it
is inverted in the second premise, and the cut is two smaller cuts, on `C`
and on `D`.  GLR on `□B`: on the conclusion, if `□B` is in `Δ`; else `□B`
is the cut formula (`cutBox`). -/
def cutPrime {m : Nat} (ih : CutFor m) {U : List Form} {k : Nat} (rec : CutAt m U k)
    (A : Form) (Γ Δ : List Form) (hA : A.size ≤ m + 1) (hU : Closed U (Γ ⇒ Δ))
    (hw : weight U (Γ ⇒ Δ) < k + 1) (nP : ¬ (Γ ⇒ Δ).IsIdP) (nBot : ¬ (Γ ⇒ Δ).IsBotL)
    (nB : ¬ (Γ ⇒ Δ).IsIdB) (nR : ∀ A B, A ⟶ B ∉ Δ) (nL : ∀ A B, A ⟶ B ∉ Γ)
    (d₁ : Fam (Γ ⇒ A :: Δ)) (d₂ : Fam (A :: Γ ⇒ Δ)) : Fam (Γ ⇒ Δ) :=
  match d₁ with
  | .idP p hΓ hΔ =>
      have hA' : A ∈ Γ := by
        rcases List.mem_cons.1 hΔ with h | h
        · exact h ▸ hΓ
        · exact absurd ⟨p, hΓ, h⟩ nP
      ((d₂.ctrL A (Γ.erase A) (by perm_count [perm_cons_erase hA'])).ex
        (by perm_count [perm_cons_erase hA']) (.refl _)).1
  | .botL h => absurd h nBot
  | .impL C D h _ _ => absurd h (nL C D)
  | .impR C D h d =>
      have e : A = C ⟶ D := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h (nR C D)
      have hC : C.size ≤ m := by subst e; simp only [Form.size] at hA; omega
      have hD : D.size ≤ m := by subst e; simp only [Form.size] at hA; omega
      let r := d₂.invL C D Γ (by rw [e])
      let d' : Fam (C :: Γ ⇒ D :: Δ) :=
        (d.le.ex (.refl _) (by subst e; perm_count [perm_cons_erase h])).1
      -- the cut on `C`, then the cut on `D`
      ih D Γ Δ hD
        (ih C Γ (D :: Δ) hC (r.1.wk [] [D] (by perm_count []) (by perm_count [])).1 d')
        r.2.1
  | .glr B h d₀ =>
      if hB : □B ∈ Δ then .glr B hB d₀ else
        have e : A = □B := by
          rcases List.mem_cons.1 h with h | h
          · exact h.symm
          · exact absurd h hB
        cutBox ih rec B Γ Δ (e ▸ hA) hU hw nP nBot nB nR nL d₀
          (d₂.le.ex (by rw [e]) (.refl _)).1

/-- **The cut on the formulas of size at most `m + 1`**, from the cut on
those of size at most `m`, by recursion on a bound `k` on the measure of
the conclusion `Γ ⇒ Δ`.  The conclusion is looked at first: an axiom is
derived at once; an implication at top level is inverted in both premises,
the cut made at the premise or premises of its rule, of smaller measure,
and the rule applied; otherwise `cutPrime`. -/
def cutStep {m : Nat} (ih : CutFor m) (U : List Form) : (k : Nat) → CutAt m U k
  | 0, _, _, _, _, _, hw, _, _ => absurd hw (Nat.not_lt_zero _)
  | k + 1, A, Γ, Δ, hA, hU, hw, d₁, d₂ =>
    match classify (Γ ⇒ Δ) with
    | .idP p hΓ hΔ => .idP p hΓ hΔ
    | .botL h => .botL h
    | .idB B hΓ hΔ => Fam.id (□B) hΓ hΔ
    | .impR C D h =>
        have h : C ⟶ D ∈ Δ := h
        have hs := (PSPrem.impR C D h rfl :
          PSPrem (C :: Γ ⇒ D :: Δ.erase (C ⟶ D)) (Γ ⇒ Δ)).step hU
        .impR C D h
          (cutStep ih U k A (C :: Γ) (D :: Δ.erase (C ⟶ D)) hA hs.1
            (Nat.lt_of_lt_of_le hs.2 (Nat.le_of_lt_succ hw))
            ((d₁.invR C D (A :: Δ.erase (C ⟶ D)) (by perm_count [perm_cons_erase h])).ex
              (.refl _) (by perm_count [])).1
            ((d₂.invR C D (Δ.erase (C ⟶ D)) (perm_cons_erase h)).ex
              (by perm_count []) (.refl _)).1)
    | .impL C D h =>
        have h : C ⟶ D ∈ Γ := h
        have hs₁ := (PSPrem.impL₁ C D h rfl :
          PSPrem (Γ.erase (C ⟶ D) ⇒ C :: Δ) (Γ ⇒ Δ)).step hU
        have hs₂ := (PSPrem.impL₂ C D h rfl :
          PSPrem (D :: Γ.erase (C ⟶ D) ⇒ Δ) (Γ ⇒ Δ)).step hU
        let r₁ := d₁.invL C D (Γ.erase (C ⟶ D)) (perm_cons_erase h)
        let r₂ := d₂.invL C D (A :: Γ.erase (C ⟶ D)) (by perm_count [perm_cons_erase h])
        .impL C D h
          (cutStep ih U k A (Γ.erase (C ⟶ D)) (C :: Δ) hA hs₁.1
            (Nat.lt_of_lt_of_le hs₁.2 (Nat.le_of_lt_succ hw))
            (r₁.1.ex (.refl _) (by perm_count [])).1 r₂.1.1)
          (cutStep ih U k A (D :: Γ.erase (C ⟶ D)) Δ hA hs₂.1
            (Nat.lt_of_lt_of_le hs₂.2 (Nat.le_of_lt_succ hw))
            r₁.2.1 (r₂.2.ex (by perm_count []) (.refl _)).1)
    | .prime nP nBot nB nR nL =>
        cutPrime ih (cutStep ih U k) A Γ Δ hA hU hw nP nBot nB nR nL d₁ d₂

/-- **The cut on the formulas of size at most `m`**, by recursion on `m`:
at `m + 1`, `cutStep` at the boxed subformulas of the conclusion and one
more than its measure. -/
def cutFor : (m : Nat) → CutFor m
  | 0 => fun A _ _ hA _ _ => absurd hA (Nat.not_le_of_gt A.size_pos)
  | m + 1 => fun A Γ Δ hA d₁ d₂ =>
      cutStep (cutFor m) (Γ ⇒ Δ).boxSubs (weight (Γ ⇒ Δ).boxSubs (Γ ⇒ Δ) + 1) A Γ Δ hA
        (closed_self _) (Nat.lt_succ_self _) d₁ d₂

/-- **Goal 6, cut admissibility by the source's induction** (the source's
`GLS_cut_adm`): the additive cut, with the cut formula at any place.  Two
exchanges bring the cut formula to the head. -/
def cutBySource : CutAdmissible := fun A Γ0 Γ1 Δ0 Δ1 d₁ d₂ =>
  cutFor A.size A (Γ0 ++ Γ1) (Δ0 ++ Δ1) (Nat.le_refl _)
    (d₁.le.ex (.refl _) (by perm_count [])).1
    (d₂.le.ex (by perm_count []) (.refl _)).1

end GLS

#axioms_within_file [propext, Quot.sound]
