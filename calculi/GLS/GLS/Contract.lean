/-
Goal 4, third part: contraction on the left and on the right in GLS, with
heights.

Source: the Coq file `GL/GLS_ctr.v` (`GLS_hpadm_ctr_L`, `GLS_hpadm_ctr_R`)
of `ianshil/CE_GLS`.  The two are proved together, by recursion on a bound
on the height of the derivation: the recursive calls are on derivations
that the inversions return, which are no higher than a premise but are not
parts of it.  The sequent is given up to a permutation that brings the two
copies of the formula to the head.  Theory file: it ends with its bound on
axioms.
-/
import GLS.Invert

namespace GLS

theorem Fam.height_pos {s : Seq} (d : Fam s) : 0 < d.height := by
  cases d <;> exact Nat.succ_pos _

/-- A member of a permutation of `A :: A :: L₀` is in `A :: L₀`. -/
theorem mem_of_perm_dup {X A : Form} {L L₀ : List Form} (hp : L.Perm (A :: A :: L₀))
    (h : X ∈ L) : X ∈ A :: L₀ := by
  rcases List.mem_cons.1 (hp.mem_iff.1 h) with h | h
  · exact h ▸ List.mem_cons_self ..
  · exact h

/-- Contraction on the left, for the derivations of height at most `n`. -/
abbrev CtrL (n : Nat) : Type :=
  (Γ Δ : List Form) → (d : Fam (Γ ⇒ Δ)) → d.height ≤ n → (A : Form) → (Γ₀ : List Form) →
    Γ.Perm (A :: A :: Γ₀) → FamLe (A :: Γ₀ ⇒ Δ) d.height

/-- Contraction on the right, for the derivations of height at most `n`. -/
abbrev CtrR (n : Nat) : Type :=
  (Γ Δ : List Form) → (d : Fam (Γ ⇒ Δ)) → d.height ≤ n → (A : Form) → (Δ₀ : List Form) →
    Δ.Perm (A :: A :: Δ₀) → FamLe (Γ ⇒ A :: Δ₀) d.height

/-- Contraction on the left of a derivation with a bound on its height. -/
def CtrL.on {n : Nat} (ih : CtrL n) {Γ Δ : List Form} {m : Nat} (d : FamLe (Γ ⇒ Δ) m)
    (hm : m ≤ n) (A : Form) (Γ₀ : List Form) (hp : Γ.Perm (A :: A :: Γ₀)) :
    FamLe (A :: Γ₀ ⇒ Δ) m :=
  (ih _ _ d.1 (Nat.le_trans d.2 hm) A Γ₀ hp).mono d.2

/-- Contraction on the right of a derivation with a bound on its height. -/
def CtrR.on {n : Nat} (ih : CtrR n) {Γ Δ : List Form} {m : Nat} (d : FamLe (Γ ⇒ Δ) m)
    (hm : m ≤ n) (A : Form) (Δ₀ : List Form) (hp : Δ.Perm (A :: A :: Δ₀)) :
    FamLe (Γ ⇒ A :: Δ₀) m :=
  (ih _ _ d.1 (Nat.le_trans d.2 hm) A Δ₀ hp).mono d.2

/-- Contraction on the left of each formula of a list `L`: from `L, L, Γ₀`
to `L, Γ₀`. -/
def CtrL.list {n : Nat} (ih : CtrL n) : (L : List Form) → {Γ Δ : List Form} → {m : Nat} →
    (d : FamLe (Γ ⇒ Δ) m) → m ≤ n → (Γ₀ : List Form) → Γ.Perm (L ++ (L ++ Γ₀)) →
    FamLe (L ++ Γ₀ ⇒ Δ) m
  | [], _, _, _, d, _, _, hp => d.ex (by perm_count [hp]) (.refl _)
  | E :: L, _, _, _, d, hm, Γ₀, hp =>
      (CtrL.list ih L (ih.on d hm E (L ++ (L ++ Γ₀)) (by perm_count [hp])) hm (E :: Γ₀)
        (by perm_count [])).ex (by perm_count []) (.refl _)

/-- **Contraction on the left, one step of the bound.**  The cases of the
last rule: an axiom; a rule on another formula, where the premises are
contracted and the rule applied again; ImpL on the contracted formula
`C ⟶ D`, where the other copy is inverted in each premise, and `C` is
contracted on the right of the first and `D` on the left of the second;
GLR, where the premise has two copies of what the contracted formula gives
it. -/
def ctrLStep {n : Nat} (ihL : CtrL n) (ihR : CtrR n) : CtrL (n + 1)
  | _, _, .idP p hΓ hΔ, _, _, _, hp => ⟨.idP p (mem_of_perm_dup hp hΓ) hΔ, Nat.le_refl _⟩
  | _, _, .botL h, _, _, _, hp => ⟨.botL (mem_of_perm_dup hp h), Nat.le_refl _⟩
  | _, _, .impR C D h d, hd, A, Γ₀, hp =>
      .impR C D h
        ((ihL _ _ d (Nat.le_of_succ_le_succ hd) A (C :: Γ₀) (by perm_count [hp])).ex
          (by perm_count []) (.refl _))
  | _, _, .impL C D h d₁ d₂, hd, A, Γ₀, hp =>
      have hd₁ : d₁.height ≤ n :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ hd)
      have hd₂ : d₂.height ≤ n :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ hd)
      if e : C ⟶ D = A then
        -- the contracted formula is the principal one
        have hm : C ⟶ D ∈ A :: Γ₀ := e ▸ List.mem_cons_self ..
        let e₁ := (d₁.invL C D Γ₀ (by subst e; perm_count [hp, perm_cons_erase h])).1
        let e₂ := (d₂.invL C D (D :: Γ₀) (by subst e; perm_count [hp, perm_cons_erase h])).2
        .impL C D hm
          ((ihR.on e₁ hd₁ C _ (.refl _)).ex (by subst e; perm_count [perm_cons_erase hm])
            (.refl _))
          ((ihL.on e₂ hd₂ D Γ₀ (.refl _)).ex (by subst e; perm_count [perm_cons_erase hm])
            (.refl _))
      else
        have h₀ : C ⟶ D ∈ Γ₀ := by
          rcases List.mem_cons.1 (mem_of_perm_dup hp h) with h | h
          · exact absurd h e
          · exact h
        .impL C D (List.mem_cons_of_mem _ h₀)
          ((ihL _ _ d₁ hd₁ A (Γ₀.erase (C ⟶ D))
              (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])).ex
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem A h₀)])
            (.refl _))
          ((ihL _ _ d₂ hd₂ A (D :: Γ₀.erase (C ⟶ D))
              (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])).ex
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem A h₀)])
            (.refl _))
  | _, _, .glr C h d, hd, A, Γ₀, hp =>
      .glr C h
        ((ihL.list A.xb d.le (Nat.le_of_succ_le_succ hd) (xbox Γ₀ ++ [□C])
            (by perm_count [xbox_perm hp])).ex
          (by perm_count []) (.refl _))

/-- **Contraction on the right, one step of the bound.**  The cases of the
last rule: an axiom; a rule on another formula; ImpR on the contracted
formula `C ⟶ D`, where the other copy is inverted in the premise, and `C`
is contracted on the left and `D` on the right; GLR, whose premise is
unchanged. -/
def ctrRStep {n : Nat} (ihL : CtrL n) (ihR : CtrR n) : CtrR (n + 1)
  | _, _, .idP p hΓ hΔ, _, _, _, hp => ⟨.idP p hΓ (mem_of_perm_dup hp hΔ), Nat.le_refl _⟩
  | _, _, .botL h, _, _, _, _ => ⟨.botL h, Nat.le_refl _⟩
  | _, _, .impR C D h d, hd, A, Δ₀, hp =>
      have hd' : d.height ≤ n := Nat.le_of_succ_le_succ hd
      if e : C ⟶ D = A then
        -- the contracted formula is the principal one
        have hm : C ⟶ D ∈ A :: Δ₀ := e ▸ List.mem_cons_self ..
        let e₁ := d.invR C D (D :: Δ₀) (by subst e; perm_count [hp, perm_cons_erase h])
        let e₂ := ihL.on e₁ hd' C _ (.refl _)
        let e₃ := ihR.on e₂ hd' D Δ₀ (.refl _)
        .impR C D hm (e₃.ex (.refl _) (by subst e; perm_count [perm_cons_erase hm]))
      else
        have h₀ : C ⟶ D ∈ Δ₀ := by
          rcases List.mem_cons.1 (mem_of_perm_dup hp h) with h | h
          · exact absurd h e
          · exact h
        .impR C D (List.mem_cons_of_mem _ h₀)
          ((ihR _ _ d hd' A (D :: Δ₀.erase (C ⟶ D))
              (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])).ex
            (.refl _)
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem A h₀)]))
  | _, _, .impL C D h d₁ d₂, hd, A, Δ₀, hp =>
      have hd₁ : d₁.height ≤ n :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ hd)
      have hd₂ : d₂.height ≤ n :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ hd)
      .impL C D h
        ((ihR _ _ d₁ hd₁ A (C :: Δ₀) (by perm_count [hp])).ex (.refl _) (by perm_count []))
        (ihR _ _ d₂ hd₂ A Δ₀ hp)
  | _, _, .glr C h d, _, _, _, hp => ⟨.glr C (mem_of_perm_dup hp h) d, Nat.le_refl _⟩

/-- **Contraction on the left and on the right**, for the derivations of
height at most `n`. -/
def ctr : (n : Nat) → CtrL n × CtrR n
  | 0 =>
      (fun _ _ d hd _ _ _ => absurd hd (Nat.not_le_of_gt d.height_pos),
       fun _ _ d hd _ _ _ => absurd hd (Nat.not_le_of_gt d.height_pos))
  | n + 1 => (ctrLStep (ctr n).1 (ctr n).2, ctrRStep (ctr n).1 (ctr n).2)

/-- **Contraction on the left**, up to a permutation: a derivation of
`Γ ⇒ Δ`, where `Γ` is a permutation of `A :: A :: Γ₀`, gives one no higher
of `A :: Γ₀ ⇒ Δ`. -/
def Fam.ctrL {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) (A : Form) (Γ₀ : List Form)
    (hp : Γ.Perm (A :: A :: Γ₀)) : FamLe (A :: Γ₀ ⇒ Δ) d.height :=
  (ctr d.height).1 _ _ d (Nat.le_refl _) A Γ₀ hp

/-- **Contraction on the right**, up to a permutation: a derivation of
`Γ ⇒ Δ`, where `Δ` is a permutation of `A :: A :: Δ₀`, gives one no higher
of `Γ ⇒ A :: Δ₀`. -/
def Fam.ctrR {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) (A : Form) (Δ₀ : List Form)
    (hp : Δ.Perm (A :: A :: Δ₀)) : FamLe (Γ ⇒ A :: Δ₀) d.height :=
  (ctr d.height).2 _ _ d (Nat.le_refl _) A Δ₀ hp

/-! ## The statements -/

/-- **Goal 4, contraction on the left**, with heights. -/
def contractionL : ContractionL := fun A Γ0 Γ1 Γ2 _ d =>
  (d.ctrL A (Γ0 ++ Γ1 ++ Γ2) (by perm_count [])).ex (by perm_count []) (.refl _)

/-- **Goal 4, contraction on the right**, with heights. -/
def contractionR : ContractionR := fun A _ Δ0 Δ1 Δ2 d =>
  (d.ctrR A (Δ0 ++ Δ1 ++ Δ2) (by perm_count [])).ex (.refl _) (by perm_count [])

end GLS

#axioms_within_file [propext, Quot.sound]
