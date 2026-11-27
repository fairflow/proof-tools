/-
Uniform interpolation for GL, the condition on variables.

`GLS/Interpolation.lean` proves that the interpolant has no `p`
(`uiSeq_free`).  The usual statement of uniform interpolation asks more:
every variable of `∃p.A` is a variable of `A`.  (On paper the two are
equivalent, by substituting `⊥` for the other variables; substitution is
not in this development.)  This file states the condition and proves it,
by the induction of `itpIn_free` carried for any variable `q` that occurs
nowhere in the sequent.

The statements are the two types below, written before their proofs.
Theory file: it ends with its bound on axioms.
-/
import GLS.Interpolation

namespace GLS

/-! ## The statements -/

/-- **The variables of the interpolant of a sequent are variables of the
sequent**: a variable `q` that occurs in no formula of `Γ ⇒ Δ` does not
occur in `uiSeq p Γ Δ`. -/
abbrev UiSeqVars : Prop :=
  ∀ (p q : Nat) (Γ Δ : List Form),
    (∀ A ∈ Γ ++ Δ, A.occ q = false) → (uiSeq p Γ Δ).occ q = false

/-- **Uniform interpolation for GL, with the condition on variables**: for
every `p` and `A`, the formulas `∃p.A` and `∀p.A` of `UIFor p A` (without
`p`, with their four derivations), and every variable of either is a
variable of `A`. -/
abbrev UniformInterpolationVars : Type :=
  (p : Nat) → (A : Form) →
    { u : UIFor p A //
      ∀ q, (u.ex.occ q = true → A.occ q = true) ∧ (u.all.occ q = true → A.occ q = true) }

/-! ## The proofs -/

theorem occ_nil {q : Nat} : ∀ A ∈ ([] : List Form), A.occ q = false := fun _ h => nomatch h

theorem occ_box_of {q : Nat} {A : Form} (h : (□A).occ q = false) : A.occ q = false := h

theorem occ_imp_of {q : Nat} {A B : Form} (h : (A ⟶ B).occ q = false) :
    A.occ q = false ∧ B.occ q = false := by
  simpa [Form.occ] using h

/-- The literals of a sequent have no variable the sequent has not. -/
theorem occ_lits_of {p q : Nat} {Γ Δ : List Form} (hΓ : ∀ A ∈ Γ, A.occ q = false)
    (hΔ : ∀ A ∈ Δ, A.occ q = false) : ∀ A ∈ lits p Γ Δ, A.occ q = false := by
  intro A hA
  unfold lits at hA
  rcases List.mem_append.1 hA with hA | hA
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hA
    exact hΓ _ (mem_vars.1 (List.mem_filter.1 hr).1)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hA
    exact occ_neg (hΔ _ (mem_vars.1 (List.mem_filter.1 hr).1))

theorem occ_xbox_of {q : Nat} {Γ : List Form} (hΓ : ∀ A ∈ Γ, A.occ q = false) :
    ∀ A ∈ xbox Γ, A.occ q = false := by
  intro A hA
  rcases mem_xbox.1 hA with h | ⟨h, _⟩
  · exact occ_box_of (hΓ _ h)
  · exact hΓ _ h

theorem occ_unboxes_of {q : Nat} {Γ : List Form} (hΓ : ∀ A ∈ Γ, A.occ q = false) :
    ∀ A ∈ Γ.filterMap Form.unbox?, A.occ q = false :=
  fun _ hA => occ_box_of (hΓ _ (mem_unboxes.1 hA))

theorem occ_map_box_of {q : Nat} {H : List Form} (hH : ∀ A ∈ H, A.occ q = false) :
    ∀ A ∈ H.map Form.box, A.occ q = false := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hA
  exact hH B hB

theorem occ_append_of {q : Nat} {X Y : List Form} (hX : ∀ A ∈ X, A.occ q = false)
    (hY : ∀ A ∈ Y, A.occ q = false) : ∀ A ∈ X ++ Y, A.occ q = false := by
  intro A hA
  rcases List.mem_append.1 hA with h | h
  · exact hX A h
  · exact hY A h

theorem occ_cons_of {q : Nat} {B : Form} {X : List Form} (hB : B.occ q = false)
    (hX : ∀ A ∈ X, A.occ q = false) : ∀ A ∈ B :: X, A.occ q = false := by
  intro A hA
  rcases List.mem_cons.1 hA with rfl | h
  · exact hB
  · exact hX A h

theorem occ_erase_of {q : Nat} {B : Form} {X : List Form}
    (hX : ∀ A ∈ X, A.occ q = false) : ∀ A ∈ X.erase B, A.occ q = false :=
  fun A hA => hX A (List.mem_of_mem_erase hA)

/-- The inner recursion: a variable in no formula of `Γ`, `Δ`, `H` is not
in the interpolant, if the box part adds none. -/
theorem itpIn_vars {p q : Nat} {sh : Bool} {bx : List Form → Form}
    (hbx : ∀ H', (∀ A ∈ H', A.occ q = false) → (bx H').occ q = false) :
    ∀ (n : Nat) (Γ Δ H : List Form), (∀ A ∈ Γ, A.occ q = false) →
      (∀ A ∈ Δ, A.occ q = false) → (∀ A ∈ H, A.occ q = false) →
      (itpIn p sh bx n Γ Δ H).occ q = false := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; rfl
  | succ n ih =>
    intro Γ Δ H hΓ hΔ hH
    simp only [itpIn]
    split
    · exact occ_mkAnd (occ_mkConj hΓ) (occ_mkNeg (occ_mkDisj hΔ))
    split
    · rfl
    · rfl
    · rfl
    · next A B h _ =>
      have hAB := occ_imp_of (hΔ _ h)
      exact ih _ _ _ (occ_cons_of hAB.1 hΓ) (occ_cons_of hAB.2 (occ_erase_of hΔ)) hH
    · next A B h _ =>
      have hAB := occ_imp_of (hΓ _ h)
      exact occ_orLazy (ih _ _ _ (occ_erase_of hΓ) (occ_cons_of hAB.1 hΔ) hH)
        (ih _ _ _ (occ_cons_of hAB.2 (occ_erase_of hΓ)) hΔ hH)
    · refine occ_andLazy (occ_andLazy (occ_mkConj (occ_lits_of hΓ hΔ)) ?_) (occ_conjLazy ?_)
      · split
        · rfl
        · exact occ_mkBox (hbx _ (occ_append_of hH (occ_unboxes_of hΓ)))
      · intro f hf
        obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hf
        have hC' : C.occ q = false := occ_unboxes_of hΔ C hC
        exact occ_mkDia (ih _ _ _
          (occ_append_of (occ_xbox_of hΓ) (occ_cons_of (B := □C) hC' occ_nil))
          (occ_cons_of hC' occ_nil) hH)

theorem itpK_vars (p q : Nat) (sh : Bool) (U : List Form) :
    ∀ (k : Nat) (Γ Δ H : List Form), (∀ A ∈ Γ, A.occ q = false) →
      (∀ A ∈ Δ, A.occ q = false) → (∀ A ∈ H, A.occ q = false) →
      (itpK p sh U k Γ Δ H).occ q = false := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; rfl
  | succ k ih =>
    intro Γ Δ H hΓ hΔ hH
    exact itpIn_vars
      (fun H' hH' => ih _ _ _ (occ_xbox_of (occ_map_box_of hH')) occ_nil hH')
      _ _ _ _ hΓ hΔ hH

/-- **The variables of the interpolant of a sequent are variables of the
sequent, PROVED.** -/
theorem uiSeq_vars : UiSeqVars := fun p q _ _ h =>
  itpK_vars p q true _ _ _ _ _ (fun A hA => h A (List.mem_append_left _ hA))
    (fun A hA => h A (List.mem_append_right _ hA)) occ_nil

/-- Every variable of `∃p.A` is a variable of `A`. -/
theorem uiExists_vars (p q : Nat) (A : Form) (h : (uiExists p A).occ q = true) :
    A.occ q = true := by
  cases hA : A.occ q with
  | true => rfl
  | false =>
    have := uiSeq_vars p q [A] [] (occ_cons_of hA occ_nil)
    unfold uiExists at h
    rw [this] at h; cases h

/-- Every variable of `∀p.A` is a variable of `A`. -/
theorem uiForall_vars (p q : Nat) (A : Form) (h : (uiForall p A).occ q = true) :
    A.occ q = true := by
  cases hA : A.occ q with
  | true => rfl
  | false =>
    have := occ_neg (uiSeq_vars p q [] [A] (occ_cons_of hA occ_nil))
    unfold uiForall at h
    rw [this] at h; cases h

/-- **Uniform interpolation for GL, with the condition on variables,
PROVED**: the interpolants are those of `uniformInterpolation`. -/
def uniformInterpolationVars : UniformInterpolationVars := fun p A =>
  ⟨uniformInterpolation p A, fun q => ⟨uiExists_vars p q A, uiForall_vars p q A⟩⟩

end GLS

#axioms_within_file [propext, Quot.sound]
