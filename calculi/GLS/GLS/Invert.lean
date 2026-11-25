/-
Goal 4, second part: the inversion of ImpR and of ImpL in GLS, with
heights.

Source: the Coq file `GL/GLS_inv_ImpR_ImpL.v` (`ImpR_ImpL_hpinv`) of
`ianshil/CE_GLS`.  Each inversion is a function on derivations, written by
matching on the derivation; the sequent is given up to a permutation that
brings the implication to the head.  Theory file: it ends with its bound
on axioms.
-/
import GLS.Structural

namespace GLS

/-- A member of a permutation of `X :: L₀` that is not `X` is in `L₀`. -/
theorem mem_of_perm_cons_of_ne {X Y : Form} {L L₀ : List Form} (hp : L.Perm (X :: L₀))
    (h : Y ∈ L) (hne : Y ≠ X) : Y ∈ L₀ := by
  rcases List.mem_cons.1 (hp.mem_iff.1 h) with h | h
  · exact absurd h hne
  · exact h

/-- The inversion of ImpR (`Fam.invR`), by matching on the derivation.  The
sequent is a variable `s`, so that the recursion is on a part of the
derivation.  Where the last rule is ImpR on the implication itself, the
premise is the answer; where it is a rule on another formula, its premises
are inverted and the rule applied again; at GLR the premise is weakened by
what `A` gives it. -/
def Fam.invRAux (A B : Form) : {s : Seq} → (d : Fam s) → (Δ₀ : List Form) →
    s.suc.Perm ((A ⟶ B) :: Δ₀) → FamLe (A :: s.ant ⇒ B :: Δ₀) d.height
  | _, .idP p hΓ hΔ, _, hp =>
      ⟨.idP p (List.mem_cons_of_mem _ hΓ)
        (List.mem_cons_of_mem _ (mem_of_perm_cons_of_ne hp hΔ (fun h => by cases h))),
        Nat.le_refl _⟩
  | _, .botL h, _, _ => ⟨.botL (List.mem_cons_of_mem _ h), Nat.le_refl _⟩
  | _, .impR C D h d, Δ₀, hp =>
      if e : C ⟶ D = A ⟶ B then
        -- the last rule is on the implication itself: its premise
        (d.le.ex (by rw [(Form.imp.inj e).1])
          (by
            have h' : A ⟶ B ∈ _ := e ▸ h
            rw [e, (Form.imp.inj e).2]
            perm_count [hp, perm_cons_erase h'])).mono (Nat.le_succ _)
      else
        have h₀ : C ⟶ D ∈ Δ₀ := mem_of_perm_cons_of_ne hp h e
        .impR C D (List.mem_cons_of_mem _ h₀)
          ((d.invRAux A B (D :: Δ₀.erase (C ⟶ D))
              (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])).ex
            (by perm_count [])
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem B h₀)]))
  | _, .impL C D h d₁ d₂, Δ₀, hp =>
      .impL C D (List.mem_cons_of_mem _ h)
        ((d₁.invRAux A B (C :: Δ₀) (by perm_count [hp])).ex
          (by perm_count [perm_cons_erase h, perm_cons_erase (List.mem_cons_of_mem A h)])
          (by perm_count []))
        ((d₂.invRAux A B Δ₀ hp).ex
          (by perm_count [perm_cons_erase h, perm_cons_erase (List.mem_cons_of_mem A h)])
          (.refl _))
  | _, .glr C h d, _, hp =>
      .glr C (List.mem_cons_of_mem _ (mem_of_perm_cons_of_ne hp h (fun h => by cases h)))
        (d.le.wk A.xb [] (by perm_count []) (by perm_count []))

/-- **The inversion of ImpR**, up to a permutation: a derivation of
`Γ ⇒ Δ`, where `Δ` is a permutation of `A ⟶ B :: Δ₀`, gives one no higher
of `A :: Γ ⇒ B :: Δ₀`. -/
def Fam.invR (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) (Δ₀ : List Form)
    (hp : Δ.Perm ((A ⟶ B) :: Δ₀)) : FamLe (A :: Γ ⇒ B :: Δ₀) d.height :=
  d.invRAux A B Δ₀ hp

/-- The inversion of ImpL (`Fam.invL`), by matching on the derivation.  The
sequent is a variable `s`, so that the recursion is on a part of the
derivation.  Where the last rule is ImpL on the implication itself, its
two premises are the answer; where it is a rule on another formula, its
premises are inverted and the rule applied again; at GLR the premise is
unchanged for the first answer, and weakened by what `B` gives it for the
second. -/
def Fam.invLAux (A B : Form) : {s : Seq} → (d : Fam s) → (Γ₀ : List Form) →
    s.ant.Perm ((A ⟶ B) :: Γ₀) →
    FamLe (Γ₀ ⇒ A :: s.suc) d.height × FamLe (B :: Γ₀ ⇒ s.suc) d.height
  | _, .idP p hΓ hΔ, _, hp =>
      have h₀ := mem_of_perm_cons_of_ne hp hΓ (fun h => by cases h)
      (⟨.idP p h₀ (List.mem_cons_of_mem _ hΔ), Nat.le_refl _⟩,
       ⟨.idP p (List.mem_cons_of_mem _ h₀) hΔ, Nat.le_refl _⟩)
  | _, .botL h, _, hp =>
      have h₀ := mem_of_perm_cons_of_ne hp h (fun h => by cases h)
      (⟨.botL h₀, Nat.le_refl _⟩, ⟨.botL (List.mem_cons_of_mem _ h₀), Nat.le_refl _⟩)
  | _, .impR C D h d, Γ₀, hp =>
      let r := d.invLAux A B (C :: Γ₀) (by perm_count [hp])
      (.impR C D (List.mem_cons_of_mem _ h)
          (r.1.ex (.refl _)
            (by perm_count [perm_cons_erase h, perm_cons_erase (List.mem_cons_of_mem A h)])),
       .impR C D h (r.2.ex (by perm_count []) (.refl _)))
  | _, .impL C D h d₁ d₂, Γ₀, hp =>
      if e : C ⟶ D = A ⟶ B then
        -- the last rule is on the implication itself: its two premises
        ((d₁.le.ex
            (by
              have h' : A ⟶ B ∈ _ := e ▸ h
              rw [e]
              perm_count [hp, perm_cons_erase h'])
            (by rw [(Form.imp.inj e).1])).mono (Nat.le_succ_of_le (Nat.le_max_left _ _)),
         (d₂.le.ex
            (by
              have h' : A ⟶ B ∈ _ := e ▸ h
              rw [e, (Form.imp.inj e).2]
              perm_count [hp, perm_cons_erase h'])
            (.refl _)).mono (Nat.le_succ_of_le (Nat.le_max_right _ _)))
      else
        have h₀ : C ⟶ D ∈ Γ₀ := mem_of_perm_cons_of_ne hp h e
        let r₁ := d₁.invLAux A B (Γ₀.erase (C ⟶ D))
          (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])
        let r₂ := d₂.invLAux A B (D :: Γ₀.erase (C ⟶ D))
          (by perm_count [hp, perm_cons_erase h, perm_cons_erase h₀])
        (.impL C D h₀ (r₁.1.ex (.refl _) (by perm_count [])) r₂.1,
         .impL C D (List.mem_cons_of_mem _ h₀)
          (r₁.2.ex
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem B h₀)])
            (.refl _))
          (r₂.2.ex
            (by perm_count [perm_cons_erase h₀, perm_cons_erase (List.mem_cons_of_mem B h₀)])
            (.refl _)))
  | _, .glr C h d, _, hp =>
      (.glr C (List.mem_cons_of_mem _ h) (d.le.ex (by perm_count [xbox_perm hp]) (.refl _)),
       .glr C h (d.le.wk B.xb [] (by perm_count [xbox_perm hp]) (by perm_count [])))

/-- **The inversion of ImpL**, up to a permutation: a derivation of
`Γ ⇒ Δ`, where `Γ` is a permutation of `A ⟶ B :: Γ₀`, gives one no higher
of `Γ₀ ⇒ A :: Δ` and one no higher of `B :: Γ₀ ⇒ Δ`. -/
def Fam.invL (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) (Γ₀ : List Form)
    (hp : Γ.Perm ((A ⟶ B) :: Γ₀)) :
    FamLe (Γ₀ ⇒ A :: Δ) d.height × FamLe (B :: Γ₀ ⇒ Δ) d.height :=
  d.invLAux A B Γ₀ hp

/-! ## The statements -/

/-- **Goal 4, the inversion of ImpR**, with heights. -/
def inversionImpR : InversionImpR := fun A B _ _ d h => d.invR A B _ (perm_cons_erase h)

/-- **Goal 4, the inversion of ImpL**, with heights. -/
def inversionImpL : InversionImpL := fun A B _ _ d h => d.invL A B _ (perm_cons_erase h)

end GLS

#axioms_within_file [propext, Quot.sound]
