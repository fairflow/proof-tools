/-
The general axiom: system K proves `Γ{A, Ā}` for every formula `A`.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1.  Not stated
there as a result; used on p. 29, in the proof of Theorem 2.38.  The
axiom of Figure 2.3 is for propositions only.  Theory file: it ends with
its bound on axioms.
-/
import BrunnlerK.Soundness
import BrunnlerK.Ctx

namespace BrunnlerK

/-- The number of symbols of a formula. -/
def Form.size : Form → Nat
  | .atom _ => 1
  | .natom _ => 1
  | .or A B => A.size + B.size + 1
  | .and A B => A.size + B.size + 1
  | .dia A => A.size + 1
  | .box A => A.size + 1

theorem Form.size_dual (A : Form) : (∼A).size = A.size := by
  induction A with
  | atom _ => rfl
  | natom _ => rfl
  | or A B ihA ihB => simp [Form.dual, Form.size, ihA, ihB]
  | and A B ihA ihB => simp [Form.dual, Form.size, ihA, ihB]
  | dia A ih => simp [Form.dual, Form.size, ih]
  | box A ih => simp [Form.dual, Form.size, ih]

/-- A formula is not the conjunction or disjunction of something of its
own size with something else. -/
theorem Form.ne_of_size {A B : Form} (h : A.size < B.size) : A ≠ B :=
  fun e => Nat.lt_irrefl _ (e ▸ h)

theorem Form.ne_and_dual_left (B C : Form) : B ≠ ∼B ⋏ ∼C :=
  Form.ne_of_size (by simp only [Form.size, Form.size_dual]; omega)

theorem Form.ne_and_dual_right (B C : Form) : C ≠ ∼B ⋏ ∼C :=
  Form.ne_of_size (by simp only [Form.size, Form.size_dual]; omega)

theorem Form.dual_ne_and_left (B C : Form) : ∼B ≠ B ⋏ C :=
  Form.ne_of_size (by simp only [Form.size, Form.size_dual]; omega)

theorem Form.dual_ne_and_right (B C : Form) : ∼C ≠ B ⋏ C :=
  Form.ne_of_size (by simp only [Form.size, Form.size_dual]; omega)

open NSeq in
/-- **The general axiom**, by membership: if a node of `Γ` has a formula
`A` and its negation `Ā`, system K proves `Γ`.  By recursion on `A`: for
`B ∨ C` against `B̄ ∧ C̄`, the rules `∨` and `∧`; for `□B` against `◇B̄`,
the rule `□` and then `◇k_c` into the new box. -/
def Fam.gax {c : Bool} : (A : Form) → {Γ Θ : NSeq} → (a : Path) →
    Γ.node? a = some Θ → A ∈ Θ.forms → ∼A ∈ Θ.forms → Fam c Γ
  | .atom p, _, _, a, hΘ, hA, hN => .ax a p hΘ hA hN
  | .natom p, _, _, a, hΘ, hA, hN => .ax a p hΘ hN hA
  | .or B C, _, Θ, a, hΘ, hA, hN =>
    .or a B C hΘ hA <|
    .and a (∼B) (∼C) (node?_setNode _ hΘ)
      (by
        simp only [forms_add, forms_erase]
        exact .tail _ (.tail _ (mem_erase_of_ne (by intro h; cases h) hN)))
      (Fam.gax B a (node?_setNode _ (node?_setNode _ hΘ))
        (by
          simp only [forms_add, forms_erase]
          exact .tail _ (mem_erase_of_ne (Form.ne_and_dual_left B C) (.head _)))
        (by simp only [forms_add]; exact .head _))
      (Fam.gax C a (node?_setNode _ (node?_setNode _ hΘ))
        (by
          simp only [forms_add, forms_erase]
          exact .tail _ (mem_erase_of_ne (Form.ne_and_dual_right B C) (.tail _ (.head _))))
        (by simp only [forms_add]; exact .head _))
  | .and B C, _, Θ, a, hΘ, hA, hN =>
    .or a (∼B) (∼C) hΘ hN <|
    .and a B C (node?_setNode _ hΘ)
      (by
        simp only [forms_add, forms_erase]
        exact .tail _ (.tail _ (mem_erase_of_ne (by intro h; cases h) hA)))
      (Fam.gax B a (node?_setNode _ (node?_setNode _ hΘ))
        (by simp only [forms_add]; exact .head _)
        (by
          simp only [forms_add, forms_erase]
          exact .tail _ (mem_erase_of_ne (Form.dual_ne_and_left B C) (.head _))))
      (Fam.gax C a (node?_setNode _ (node?_setNode _ hΘ))
        (by simp only [forms_add]; exact .head _)
        (by
          simp only [forms_add, forms_erase]
          exact .tail _ (mem_erase_of_ne (Form.dual_ne_and_right B C) (.tail _ (.head _)))))
  | .box B, _, Θ, a, hΘ, hA, hN =>
    .box a B hΘ hA <|
    .dia a (Θ.erase (□B)).boxes.length (∼B) (node?_setNode _ hΘ)
      (by
        simp only [forms_addBox, forms_erase]
        exact mem_erase_of_ne (by intro h; cases h) hN)
      (box?_addBox _ _) <|
    Fam.gax B (Θ := (NSeq.leaf [B]).add ∼B) (a ++ [(Θ.erase (□B)).boxes.length])
      (by
        rw [node?_append _ (node?_setNode _ (node?_setNode _ hΘ))]
        have h := box?_setBox_self ((NSeq.leaf [B]).add ∼B)
          (box?_addBox (Θ.erase (□B)) (.leaf [B]))
        simp only [node?, h])
      (.tail _ (.head _)) (.head _)
  | .dia B, _, Θ, a, hΘ, hA, hN =>
    .box a (∼B) hΘ hN <|
    .dia a (Θ.erase (□∼B)).boxes.length B (node?_setNode _ hΘ)
      (by
        simp only [forms_addBox, forms_erase]
        exact mem_erase_of_ne (by intro h; cases h) hA)
      (box?_addBox _ _) <|
    Fam.gax B (Θ := (NSeq.leaf [∼B]).add B) (a ++ [(Θ.erase (□∼B)).boxes.length])
      (by
        rw [node?_append _ (node?_setNode _ (node?_setNode _ hΘ))]
        have h := box?_setBox_self ((NSeq.leaf [∼B]).add B)
          (box?_addBox (Θ.erase (□∼B)) (.leaf [∼B]))
        simp only [node?, h])
      (.head _) (.tail _ (.head _))

/-- **The general axiom**, as the source writes it: `Γ{A, Ā}`, for a
context `Γ{ }` and a formula `A`. -/
def Fam.gaxC {c : Bool} (C : Ctx) (A : Form) : Fam c (C.fill (.leaf [A, ∼A])) :=
  Fam.gax A C.path (C.node?_fill _) (by simp) (by simp)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
