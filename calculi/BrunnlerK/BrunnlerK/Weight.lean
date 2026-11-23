/-
A weight on nested sequents that every upward step of the search lowers.

Source: none; the source's measure for its own search is Definition 2.21
(the size of a sequent), which is for set sequents.  Theory file: it ends
with its bound on axioms.
-/
import BrunnlerK.Context

namespace BrunnlerK

/-- The weight of a formula: its number of symbols, with `□` counted
twice.  (A step of the rule `□` takes `□A` away and adds a box `[A]`; the
box weighs one more than its formula, so `□` weighs two.) -/
def Form.weight : Form → Nat
  | .atom _ => 1
  | .natom _ => 1
  | .or A B => A.weight + B.weight + 1
  | .and A B => A.weight + B.weight + 1
  | .dia A => A.weight + 1
  | .box A => A.weight + 2

/-- The weight of a list of formulas: the sum of their weights. -/
def formsWeight : List Form → Nat
  | [] => 0
  | A :: fs => A.weight + formsWeight fs

/-- The weight of a sequent: the weights of all its formulas, and one for
each box. -/
def NSeq.weight : NSeq → Nat
  | .leaf fs => formsWeight fs
  | .cons Δ r => Δ.weight + r.weight + 1

theorem formsWeight_erase {fs : List Form} {A : Form} (h : A ∈ fs) :
    formsWeight (fs.erase A) + A.weight = formsWeight fs := by
  induction fs with
  | nil => cases h
  | cons B fs ih =>
    by_cases e : B = A
    · subst e
      simp [formsWeight, Nat.add_comm]
    · have h' : A ∈ fs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      have := ih h'
      simp only [List.erase_cons, beq_iff_eq, e, if_false, formsWeight]
      omega

namespace NSeq

theorem weight_add (Γ : NSeq) (A : Form) : (Γ.add A).weight = Γ.weight + A.weight := by
  induction Γ with
  | leaf fs => simp [add, weight, formsWeight, Nat.add_comm]
  | cons Δ r _ ih => simp only [add, weight, ih]; omega

theorem weight_erase {Γ : NSeq} {A : Form} (h : A ∈ Γ.forms) :
    (Γ.erase A).weight + A.weight = Γ.weight := by
  induction Γ with
  | leaf fs => exact formsWeight_erase h
  | cons Δ r _ ih =>
    have := ih (by simpa [forms] using h)
    simp only [erase, weight]
    omega

theorem weight_addBox (Γ Λ : NSeq) : (Γ.addBox Λ).weight = Γ.weight + Λ.weight + 1 := by
  induction Γ with
  | leaf fs => simp only [addBox, weight]; omega
  | cons Δ r _ ih => simp only [addBox, weight, ih]; omega

/-- A sequent weighs at least its own formulas and any one of its boxes,
and one more. -/
theorem weight_box_lt {Γ Δ : NSeq} (h : Δ ∈ Γ.boxes) :
    Δ.weight + formsWeight Γ.forms < Γ.weight := by
  induction Γ with
  | leaf fs => cases h
  | cons Δ' r _ ih =>
    have hr : formsWeight r.forms ≤ r.weight := by
      clear ih h
      induction r with
      | leaf fs => exact Nat.le_refl _
      | cons Δ'' r' _ ih' => simp only [forms, weight]; omega
    rcases List.mem_cons.mp h with h | h
    · subst h
      simp only [forms, weight]
      omega
    · have := ih h
      simp only [forms, weight]
      omega

theorem weight_foldl_add (Bs : List Form) (Δ : NSeq) :
    (Bs.foldl NSeq.add Δ).weight = Δ.weight + formsWeight Bs := by
  induction Bs generalizing Δ with
  | nil => rfl
  | cons B Bs ih =>
    simp only [List.foldl_cons, ih, weight_add, formsWeight]
    omega

end NSeq

/-! ## The formulas under a `◇` -/

/-- `A`, of the formula `◇A`. -/
def Form.undia : Form → Option Form
  | .dia A => some A
  | _ => none

/-- The formulas `B` with `◇B` in the list. -/
def dias (fs : List Form) : List Form := fs.filterMap Form.undia

theorem mem_dias {fs : List Form} {B : Form} : B ∈ dias fs ↔ ◇B ∈ fs := by
  simp only [dias, List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, e⟩
    cases A <;> simp [Form.undia] at e
    exact e ▸ hA
  · intro h
    exact ⟨_, h, rfl⟩

theorem formsWeight_dias (fs : List Form) : formsWeight (dias fs) ≤ formsWeight fs := by
  induction fs with
  | nil => exact Nat.le_refl _
  | cons A fs ih =>
    cases A <;> simp only [dias, List.filterMap_cons, Form.undia, formsWeight, Form.weight] <;>
      (simp only [dias] at ih; omega)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
