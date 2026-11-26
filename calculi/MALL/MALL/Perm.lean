/-
Permutations of lists of formulas, by counting, without
`Classical.choice`.

Core Lean v4.31.0's `List.isPerm_iff` (and so its instance that decides
`List.Perm`), `List.perm_cons_erase`, `List.Perm.erase` and
`List.mem_erase_of_ne` use `Classical.choice`.  This file has the lemmas
the campaign needs, within its policy.  The lemmas on `erase` and the
tactic `perm_count` are those of `calculi/GLS/GLS/Lemmas.lean` and
`Structural.lean` of this repository, written again here because a
package under `calculi/` requires only the library.  Theory file: it
ends with its bound on axioms.
-/
import MALL.Form

namespace MALL

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

/-! ## Counting -/

/-- One if the two formulas are the same, zero if not. -/
def ind (b a : Form) : Nat := if b == a then 1 else 0

theorem ind_self (a : Form) : ind a a = 1 := by simp [ind]

theorem ind_ne {a b : Form} (h : b ≠ a) : ind b a = 0 := by simp [ind, h]

theorem count_cons' (a b : Form) (l : List Form) : (b :: l).count a = l.count a + ind b a :=
  List.count_cons

/-- Two lists in which every formula occurs the same number of times are
permutations of each other. -/
theorem perm_of_count {l₁ l₂ : List Form} (h : ∀ a, l₁.count a = l₂.count a) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.nil
    | cons b l₂ =>
      have := h b
      rw [count_cons', ind_self, List.count_nil] at this
      exact absurd this (Nat.succ_ne_zero _).symm
  | cons a l₁ ih =>
    have ha : a ∈ l₂ := by
      apply List.count_pos_iff.1
      have := h a
      rw [count_cons', ind_self] at this
      omega
    have hp := perm_cons_erase ha
    refine (List.Perm.cons a (ih fun b => ?_)).trans hp.symm
    have h1 := h b
    have h2 := hp.count_eq b
    rw [count_cons'] at h1 h2
    omega

open Lean in
/-- **A permutation, by counting.**  `perm_count [h₁, …, hₙ]` closes a goal
`l₁.Perm l₂` where the `hᵢ` are proofs of permutations: it counts the
occurrences of a formula `x` in every list, and leaves the arithmetic to
`omega`. -/
macro "perm_count" "[" hs:term,* "]" : tactic => do
  let x := mkIdent `x
  let mut tac ← `(tactic| ((try simp only [count_cons', List.count_append, List.count_nil] at *)
    <;> omega))
  for h in hs.getElems.reverse do
    tac ← `(tactic| (have := List.Perm.count_eq $h $x; $tac))
  `(tactic| (refine perm_of_count (fun $x => ?_); $tac))

/-! ## Deciding a permutation -/

/-- The two lists have every formula of either the same number of times. -/
def permB (l₁ l₂ : List Form) : Bool := (l₁ ++ l₂).all fun a => l₁.count a == l₂.count a

theorem permB_iff {l₁ l₂ : List Form} : permB l₁ l₂ = true ↔ l₁.Perm l₂ := by
  constructor
  · intro h
    refine perm_of_count fun a => ?_
    by_cases ha : a ∈ l₁ ++ l₂
    · have := List.all_eq_true.1 h a ha
      simpa using this
    · have h₁ : a ∉ l₁ := fun h' => ha (List.mem_append.2 (.inl h'))
      have h₂ : a ∉ l₂ := fun h' => ha (List.mem_append.2 (.inr h'))
      rw [List.count_eq_zero_of_not_mem h₁, List.count_eq_zero_of_not_mem h₂]
  · intro h
    refine List.all_eq_true.2 fun a _ => ?_
    simpa using h.count_eq a

/-- `List.Perm` on formulas is decided by counting.  Of higher priority
than core Lean's instance, whose proof uses `Classical.choice`. -/
instance (priority := high) decPerm (l₁ l₂ : List Form) : Decidable (l₁.Perm l₂) :=
  decidable_of_iff _ permB_iff

/-! ## What the rules need of a permutation -/

theorem perm_nil_eq {l : List Form} (h : l.Perm []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact absurd h.length_eq (by simp)

theorem perm_singleton_eq {l : List Form} {a : Form} (h : l.Perm [a]) : l = [a] := by
  match l, h with
  | [], h => exact absurd h.length_eq (fun e => by cases e)
  | [b], h =>
    have hb : b ∈ [a] := h.mem_iff.1 (List.mem_cons_self ..)
    rcases List.mem_cons.1 hb with e | e
    · rw [e]
    · cases e
  | _ :: _ :: l, h =>
    have e : l.length + 2 = 1 := h.length_eq
    omega

/-- A formula at the head of one list is the head of a permutation of it,
or is in its tail. -/
theorem perm_cons_cases {C A : Form} {Γ₁ Γ : List Form} (h : (C :: Γ₁).Perm (A :: Γ))
    (hne : C ≠ A) : Γ₁.Perm (A :: Γ₁.erase A) ∧ Γ.Perm (C :: Γ₁.erase A) := by
  have hA : A ∈ Γ₁ := by
    have : A ∈ C :: Γ₁ := h.mem_iff.2 (List.mem_cons_self ..)
    rcases List.mem_cons.1 this with e | e
    · exact absurd e.symm hne
    · exact e
  have hp := perm_cons_erase hA
  exact ⟨hp, by perm_count [h, hp]⟩

/-- What is left of `l` when one occurrence of each member of `Γ` is taken
out. -/
def sub (l Γ : List Form) : List Form := Γ.foldl List.erase l

theorem perm_erase_of_cons {a : Form} {l l' : List Form} (h : l.Perm (a :: l')) :
    (l.erase a).Perm l' := by
  have ha : a ∈ l := h.mem_iff.2 (List.mem_cons_self ..)
  have hp := perm_cons_erase ha
  perm_count [h, hp]

/-- Where `l` is `Γ` and `Δ` together, `sub l Γ` is `Δ`. -/
theorem sub_perm {l Γ Δ : List Form} (h : l.Perm (Γ ++ Δ)) : (sub l Γ).Perm Δ := by
  induction Γ generalizing l with
  | nil => exact h
  | cons a Γ ih => exact ih (perm_erase_of_cons h)

end MALL

#axioms_within_file [propext, Quot.sound]
