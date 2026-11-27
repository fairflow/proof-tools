/-
Permutations of lists of formulas, by counting, without
`Classical.choice`.

Core Lean v4.31.0's `List.isPerm_iff` (and so its instance that decides
`List.Perm`), `List.perm_cons_erase`, `List.Perm.erase` and
`List.mem_erase_of_ne` use `Classical.choice`.  This file has the lemmas
the campaign needs, within its policy.  It is `calculi/MALL/MALL/Perm.lean`
of this repository, copied with the namespace changed (and that file's
lemmas on `erase` and its tactic `perm_count` are those of `calculi/GLS/`),
because a package under `calculi/` requires only the library.  Theory file: it
ends with its bound on axioms.
-/
import DILL.Form

namespace DILL

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

/-! ## A part of a list, checked in one pass -/

/-- **`Γ` is a part of `l`**: each member of `Γ` in turn is in what is
left of `l`.  One pass over `Γ`, each step as long as the place of the
member in what is left; no formula is counted.  (The test it replaces,
`permB l (Γ ++ sub l Γ)`, counts every formula of `l` in both lists: the
square of the length of `l` whatever `Γ` is.  In the kernel that was the
cost of a tree of moves: `campaign/measurements.md`.) -/
def subAll : List Form → List Form → Bool
  | _, [] => true
  | l, a :: Γ => l.contains a && subAll (l.erase a) Γ

/-- The one pass decides what the rules ask: `l` is `Γ` and what `sub`
leaves, together. -/
theorem subAll_iff {l Γ : List Form} : subAll l Γ = true ↔ l.Perm (Γ ++ sub l Γ) := by
  induction Γ generalizing l with
  | nil => exact ⟨fun _ => .refl _, fun _ => rfl⟩
  | cons a Γ ih =>
    have hs : sub l (a :: Γ) = sub (l.erase a) Γ := rfl
    constructor
    · intro h
      have h' : (l.contains a && subAll (l.erase a) Γ) = true := h
      have h₁ := (Bool.and_eq_true_iff.1 h').1
      have h₂ := (Bool.and_eq_true_iff.1 h').2
      have ha : a ∈ l := List.contains_iff_mem.1 h₁
      rw [hs]
      exact (perm_cons_erase ha).trans ((ih.1 h₂).cons a)
    · intro h
      rw [hs] at h
      have h : l.Perm (a :: (Γ ++ sub (l.erase a) Γ)) := h
      have ha : a ∈ l := h.mem_iff.2 (List.mem_cons_self ..)
      have h₂ := ih.2 (perm_erase_of_cons h)
      show (l.contains a && subAll (l.erase a) Γ) = true
      exact Bool.and_eq_true_iff.2 ⟨List.contains_iff_mem.2 ha, h₂⟩

/-- **The one pass is the test it replaces.** -/
theorem subAll_eq_permB (l Γ : List Form) : subAll l Γ = permB l (Γ ++ sub l Γ) := by
  cases h : subAll l Γ with
  | true => exact (permB_iff.2 (subAll_iff.1 h)).symm
  | false =>
    cases h' : permB l (Γ ++ sub l Γ) with
    | false => rfl
    | true => rw [subAll_iff.2 (permB_iff.1 h')] at h; cases h

/-! ## Equality with a number compared first -/

/-- **A number for a formula**, computed by arithmetic.  Nothing rests on
it: two formulas with one number are compared as formulas.  It is there
for the kernel, which keeps the number of a formula it has met, and for
which an equality of two numbers is one step where the equality of two
formulas is a recursion over both. -/
def hashF : Form → Nat
  | .atom n => (n * 2654435761 + 97) % 4294967296
  | .one => 3
  | .top => 5
  | .zero => 7
  | .tensor A B => (hashF A * 1000003 + hashF B * 8191 + 11) % 4294967296
  | .lolli A B => (hashF A * 1000003 + hashF B * 8191 + 13) % 4294967296
  | .wth A B => (hashF A * 1000003 + hashF B * 8191 + 17) % 4294967296
  | .plus A B => (hashF A * 1000003 + hashF B * 8191 + 19) % 4294967296
  | .bang A => (hashF A * 1000003 + 23) % 4294967296

/-- Equality of two formulas, their numbers compared first. -/
def eqH (a b : Form) : Bool := Nat.beq (hashF a) (hashF b) && decide (a = b)

theorem eqH_eq (a b : Form) : eqH a b = decide (a = b) := by
  unfold eqH
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

/-- For compiled code `eqH` is the plain equality: compiled code keeps no
number of a formula, and would compute both numbers at every comparison
(the compiled check of the tree of `chain 64` took 2.6 ms with them and
1.3 ms without).  The kernel reduces the definition above. -/
def eqPlain (a b : Form) : Bool := decide (a = b)

@[csimp] theorem eqH_csimp : @eqH = @eqPlain := by
  funext a b
  exact eqH_eq a b

/-- Membership, by `eqH`. -/
def memH (x : Form) : List Form → Bool
  | [] => false
  | a :: l => eqH a x || memH x l

theorem memH_eq (x : Form) (l : List Form) : memH x l = decide (x ∈ l) := by
  induction l with
  | nil => simp [memH]
  | cons a l ih =>
    by_cases h : a = x
    · simp [memH, eqH_eq, h]
    · have h' : ¬ x = a := fun e => h e.symm
      simp [memH, eqH_eq, h, h', ih]

/-- `List.erase`, by `eqH`. -/
def eraseH (x : Form) : List Form → List Form
  | [] => []
  | a :: l => bif eqH a x then l else a :: eraseH x l

theorem eraseH_eq (x : Form) (l : List Form) : eraseH x l = l.erase x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = x
    · simp [eraseH, eqH_eq, h]
    · simp [eraseH, eqH_eq, h, ih]

/-- `sub`, by `eqH`. -/
def subH (l Γ : List Form) : List Form := Γ.foldl (fun l a => eraseH a l) l

theorem subH_eq (l Γ : List Form) : subH l Γ = sub l Γ := by
  induction Γ generalizing l with
  | nil => rfl
  | cons a Γ ih =>
    show subH (eraseH a l) Γ = sub (l.erase a) Γ
    rw [eraseH_eq]
    exact ih _

/-- `subAll`, by `eqH`. -/
def subAllH : List Form → List Form → Bool
  | _, [] => true
  | l, a :: Γ => memH a l && subAllH (eraseH a l) Γ

theorem subAllH_eq (l Γ : List Form) : subAllH l Γ = subAll l Γ := by
  induction Γ generalizing l with
  | nil => rfl
  | cons a Γ ih =>
    show (memH a l && subAllH (eraseH a l) Γ) = (l.contains a && subAll (l.erase a) Γ)
    rw [memH_eq, eraseH_eq, ih]
    simp

end DILL

#axioms_within_file [propext, Quot.sound]
