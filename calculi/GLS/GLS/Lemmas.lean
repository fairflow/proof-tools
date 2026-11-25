/-
Lemmas about lists of formulas: membership in `xbox`, and `List.erase`
without `Classical.choice` (core Lean's `List.mem_erase_of_ne`,
`List.Perm.erase` and `List.perm_cons_erase` use it on Lean v4.31.0).
Theory file: it ends with its bound on axioms.
-/
import GLS.Semantics

namespace GLS

/-! ## `erase` -/

theorem mem_erase_of_ne {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (hne : a ≠ b) (h : a ∈ l) : a ∈ l.erase b := by
  induction l with
  | nil => cases h
  | cons c l ih =>
    rw [List.erase_cons]
    by_cases hc : c = b
    · subst hc
      simp only [beq_self_eq_true, if_true]
      rcases List.mem_cons.1 h with h | h
      · exact absurd h hne
      · exact h
    · have : (c == b) = false := by simpa using hc
      simp only [this]
      rcases List.mem_cons.1 h with h | h
      · exact List.mem_cons.2 (.inl h)
      · exact List.mem_cons.2 (.inr (ih h))

theorem mem_erase_iff_of_ne {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (hne : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
  ⟨List.mem_of_mem_erase, mem_erase_of_ne hne⟩

/-- A member of a list is the erased one, or a member of the rest. -/
theorem eq_or_mem_erase {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (h : a ∈ l) : a = b ∨ a ∈ l.erase b := by
  by_cases hab : a = b
  · exact .inl hab
  · exact .inr (mem_erase_of_ne hab h)

/-- A list that has `a` is a permutation of `a` and the rest. -/
theorem perm_cons_erase {α : Type} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : l.Perm (a :: l.erase a) := by
  induction l with
  | nil => cases h
  | cons c l ih =>
    rw [List.erase_cons]
    by_cases hc : c = a
    · subst hc
      simp only [beq_self_eq_true, if_true]
      exact List.Perm.refl _
    · have hb : (c == a) = false := by simpa using hc
      simp only [hb]
      rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hc
      · exact ((ih h).cons c).trans (List.Perm.swap a c _)

/-- `erase` respects permutations. -/
theorem Perm.erase' {α : Type} [DecidableEq α] (a : α) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (l₁.erase a).Perm (l₂.erase a) := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih =>
    rw [List.erase_cons, List.erase_cons]
    by_cases hx : x = a
    · subst hx; simpa using ‹List.Perm _ _›
    · have hb : (x == a) = false := by simpa using hx
      simp only [hb]
      exact ih.cons x
  | swap x y l =>
    rw [List.erase_cons, List.erase_cons, List.erase_cons, List.erase_cons]
    by_cases hx : x = a
    · subst hx
      by_cases hy : y = x
      · subst hy; simp
      · have hb : (y == x) = false := by simpa using hy
        simp [hb]
    · have hbx : (x == a) = false := by simpa using hx
      by_cases hy : y = a
      · subst hy; simp [hbx]
      · have hby : (y == a) = false := by simpa using hy
        simp only [hbx, hby]
        exact List.Perm.swap x y _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## `xbox` -/

theorem mem_xb {A C : Form} : C ∈ A.xb ↔ A = □C ∨ (C = A ∧ ∃ B, A = □B) := by
  cases A with
  | var p => simp [Form.xb]
  | bot => simp [Form.xb]
  | imp A₁ A₂ => simp [Form.xb]
  | box B =>
    simp only [Form.xb, List.mem_cons, List.mem_nil_iff, or_false, Form.box.injEq]
    constructor
    · rintro (h | h)
      · exact .inl h.symm
      · exact .inr ⟨h, B, rfl⟩
    · rintro (h | ⟨h, _⟩)
      · exact .inl h.symm
      · exact .inr h

/-- What `xbox Γ` holds: the body of each boxed formula of `Γ`, and each
boxed formula of `Γ`. -/
theorem mem_xbox {Γ : List Form} {C : Form} :
    C ∈ xbox Γ ↔ □C ∈ Γ ∨ (C ∈ Γ ∧ ∃ B, C = □B) := by
  unfold xbox
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨A, hA, hC⟩
    rcases mem_xb.1 hC with h | ⟨h, B, hB⟩
    · subst h; exact .inl hA
    · subst h; exact .inr ⟨hA, B, hB⟩
  · rintro (h | ⟨h, B, hB⟩)
    · exact ⟨□C, h, mem_xb.2 (.inl rfl)⟩
    · exact ⟨C, h, mem_xb.2 (.inr ⟨rfl, B, hB⟩)⟩

theorem body_mem_xbox {Γ : List Form} {B : Form} (h : □B ∈ Γ) : B ∈ xbox Γ :=
  mem_xbox.2 (.inl h)

theorem box_mem_xbox {Γ : List Form} {B : Form} (h : □B ∈ Γ) : □B ∈ xbox Γ :=
  mem_xbox.2 (.inr ⟨h, B, rfl⟩)

theorem xbox_append (Γ Γ' : List Form) : xbox (Γ ++ Γ') = xbox Γ ++ xbox Γ' := by
  simp [xbox, List.flatMap_append]

theorem xbox_cons_box (B : Form) (Γ : List Form) : xbox (□B :: Γ) = B :: □B :: xbox Γ := by
  simp [xbox, Form.xb]

theorem xbox_perm {Γ Γ' : List Form} (h : Γ.Perm Γ') : (xbox Γ).Perm (xbox Γ') :=
  List.Perm.flatMap_right _ h

/-! ## The size of a formula -/

theorem Form.size_pos (A : Form) : 0 < A.size := by
  cases A <;> simp [Form.size] <;> omega

theorem Form.ne_imp_left (A B : Form) : A ≠ A ⟶ B := by
  intro h
  have := congrArg Form.size h
  simp only [Form.size] at this
  omega

theorem Form.ne_imp_right (A B : Form) : B ≠ A ⟶ B := by
  intro h
  have := congrArg Form.size h
  simp only [Form.size] at this
  omega

theorem Form.ne_box (A : Form) : A ≠ □A := by
  intro h
  have := congrArg Form.size h
  simp only [Form.size] at this
  omega

end GLS

#axioms_within_file [propext, Quot.sound]
