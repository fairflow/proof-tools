/-
The connectives that GLS does not have, defined from `→` and `⊥`: `¬`,
`⊤`, `∧`, `∨`, `◇`, and the conjunction of a list; their truth at a tree.

The definitions are the classical ones (the tutorial, §1, has `¬`, `◇`
and `⊤`):

    ¬A := A → ⊥      ⊤ := ⊥ → ⊥      ◇A := ¬□¬A
    A ∧ B := ¬(A → ¬B)                A ∨ B := ¬A → B

The rules they obtain in GLS are in `GLS/ConnectiveRules.lean`.  Theory
file: it ends with its bound on axioms.
-/
import GLS.TreeModel

namespace GLS

/-- `¬A := A → ⊥`. -/
def Form.neg (A : Form) : Form := A ⟶ ⊥

/-- `⊤ := ⊥ → ⊥`. -/
def Form.top : Form := ⊥ ⟶ ⊥

/-- `A ∧ B := ¬(A → ¬B)`. -/
def Form.and (A B : Form) : Form := (A ⟶ (B ⟶ ⊥)) ⟶ ⊥

/-- `A ∨ B := ¬A → B`. -/
def Form.or (A B : Form) : Form := (A ⟶ ⊥) ⟶ B

/-- `◇A := ¬□¬A`. -/
def Form.dia (A : Form) : Form := (□(A ⟶ ⊥)) ⟶ ⊥

/-- The conjunction of a list: `⊤` for the empty list. -/
def conjL : List Form → Form
  | [] => Form.top
  | A :: As => Form.and A (conjL As)

/-- The disjunction of a list: `⊥` for the empty list. -/
def disjL : List Form → Form
  | [] => ⊥
  | A :: As => Form.or A (disjL As)

@[inherit_doc] scoped infixl:65 " ⋏ " => Form.and
@[inherit_doc] scoped infixl:64 " ⋎ " => Form.or

/-! ## Truth at a tree -/

@[simp] theorem holds_neg (A : Form) (t : Tree) : A.neg.holds t = !A.holds t := by
  simp [Form.neg, Form.holds]

@[simp] theorem holds_top (t : Tree) : Form.top.holds t = true := by
  simp [Form.top, Form.holds]

@[simp] theorem holds_and (A B : Form) (t : Tree) :
    (A ⋏ B).holds t = (A.holds t && B.holds t) := by
  simp only [Form.and, Form.holds]
  cases A.holds t <;> cases B.holds t <;> rfl

@[simp] theorem holds_or (A B : Form) (t : Tree) :
    (A ⋎ B).holds t = (A.holds t || B.holds t) := by
  simp only [Form.or, Form.holds]
  cases A.holds t <;> cases B.holds t <;> rfl

@[simp] theorem holds_box (A : Form) (t : Tree) :
    (□A).holds t = t.desc.all (fun u => A.holds u) := rfl

@[simp] theorem holds_var (p : Nat) (t : Tree) : (Form.var p).holds t = t.val.contains p := rfl

@[simp] theorem holds_bot (t : Tree) : (⊥ : Form).holds t = false := rfl

@[simp] theorem holds_imp (A B : Form) (t : Tree) :
    (A ⟶ B).holds t = (!A.holds t || B.holds t) := rfl

/-- A list on which `all` fails has a member that fails, without choice. -/
theorem exists_of_all_false {α : Type} {f : α → Bool} : ∀ {l : List α},
    l.all f = false → ∃ x ∈ l, f x = false
  | [], h => by cases h
  | a :: l, h => by
    cases ha : f a with
    | false => exact ⟨a, List.mem_cons_self .., ha⟩
    | true =>
      rw [List.all_cons, ha, Bool.true_and] at h
      obtain ⟨x, hx, hf⟩ := exists_of_all_false h
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

/-- `◇A` is true at a tree iff `A` is true at a proper descendant. -/
theorem holds_dia (A : Form) (t : Tree) :
    A.dia.holds t = true ↔ ∃ u ∈ t.desc, A.holds u = true := by
  show (!(t.desc.all fun u => !A.holds u || false) || false) = true ↔ _
  constructor
  · intro h
    cases ha : t.desc.all (fun u => !A.holds u || false) with
    | true => rw [ha] at h; cases h
    | false =>
      obtain ⟨u, hu, hf⟩ := exists_of_all_false ha
      refine ⟨u, hu, ?_⟩
      cases hA : A.holds u with
      | true => rfl
      | false => rw [hA] at hf; cases hf
  · rintro ⟨u, hu, h⟩
    cases ha : t.desc.all (fun u => !A.holds u || false) with
    | false => rfl
    | true =>
      have := List.all_eq_true.1 ha u hu
      rw [h] at this; cases this

theorem holds_conjL (As : List Form) (t : Tree) :
    (conjL As).holds t = true ↔ ∀ A ∈ As, A.holds t = true := by
  induction As with
  | nil => simp [conjL]
  | cons A As ih => simp [conjL, ih]

theorem holds_disjL (As : List Form) (t : Tree) :
    (disjL As).holds t = true ↔ ∃ A ∈ As, A.holds t = true := by
  induction As with
  | nil => simp [disjL]
  | cons A As ih => simp [disjL, ih]

end GLS

#axioms_within_file [propext, Quot.sound]
