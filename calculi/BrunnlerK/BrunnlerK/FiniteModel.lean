/-
The finite model property: a sequent that is not valid is not true at
some state of a two-valued model with finitely many states.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Corollary
2.24 (finite model property), p. 19, at `X = ∅`: "if a formula is not
valid then there is a finite frame in which it is not valid".  Theory
file: it ends with its bound on axioms.

The search (`BrunnlerK/Search.lean`) refutes a sequent that is not valid
at a finite tree, a state of the model of all finite trees.  Here that
tree is made a model of its own: its states are the trees of its first
levels, down to the modal depth of the formula, each with the number of
its level.
-/
import BrunnlerK.Completeness

namespace BrunnlerK

/-- **A model with finitely many states**: some list has every state. -/
def Model.Finite (M : Model) : Prop := ∃ l : List M.W, ∀ s : M.W, s ∈ l

/-- The modal depth of a formula: the greatest number of `◇` and `□`
one inside the other. -/
def Form.md : Form → Nat
  | .atom _ => 0
  | .natom _ => 0
  | .or A B => max A.md B.md
  | .and A B => max A.md B.md
  | .dia A => A.md + 1
  | .box A => A.md + 1

/-- The trees at level `n` of a tree: itself at level 0, the children of
the trees of level `n` at level `n + 1`. -/
def Tree.level : Nat → Tree → List Tree
  | 0, t => [t]
  | n + 1, t => (t.level n).flatMap Tree.kids

/-- **The model of the levels `0` to `N` of a tree.**  A state is a level
and a tree of that level; `(i, u) → (i + 1, v)` if `v` is a child of the
root of `u`; a proposition is true at `(i, u)` if it is in the list at
the root of `u`. -/
def Tree.model (t : Tree) (N : Nat) : Model where
  W := {x : Nat × Tree // x.1 ≤ N ∧ x.2 ∈ t.level x.1}
  R x y := y.1.1 = x.1.1 + 1 ∧ y.1.2 ∈ x.1.2.kids
  V p x := p ∈ x.1.2.val

/-- Truth in the model of the levels is truth in the model of finite
trees, for a formula whose modal depth does not go below level `N`. -/
theorem Tree.sat_model (t : Tree) (N : Nat) : ∀ (A : Form) (x : (t.model N).W),
    A.md + x.1.1 ≤ N → ((t.model N).sat x A ↔ treeModel.sat x.1.2 A) := by
  intro A
  induction A with
  | atom p => intro x _; exact Iff.rfl
  | natom p => intro x _; exact Iff.rfl
  | or A B ihA ihB =>
    intro x hx
    simp only [Form.md] at hx
    exact or_congr (ihA x (by omega)) (ihB x (by omega))
  | and A B ihA ihB =>
    intro x hx
    simp only [Form.md] at hx
    exact and_congr (ihA x (by omega)) (ihB x (by omega))
  | dia A ih =>
    intro x hx
    simp only [Form.md] at hx
    constructor
    · rintro ⟨y, ⟨hy₁, hy₂⟩, hs⟩
      have hy₁' : y.1.1 = x.1.1 + 1 := hy₁
      exact ⟨y.1.2, hy₂, (ih y (by omega)).mp hs⟩
    · rintro ⟨v, hv, hs⟩
      have hv' : v ∈ x.1.2.kids := hv
      let y : (t.model N).W := ⟨(x.1.1 + 1, v), by omega,
        List.mem_flatMap.mpr ⟨x.1.2, x.2.2, hv'⟩⟩
      exact ⟨y, ⟨rfl, hv'⟩, (ih y (by show A.md + (x.1.1 + 1) ≤ N; omega)).mpr hs⟩
  | box A ih =>
    intro x hx
    simp only [Form.md] at hx
    constructor
    · intro h v hv
      have hv' : v ∈ x.1.2.kids := hv
      let y : (t.model N).W := ⟨(x.1.1 + 1, v), by omega,
        List.mem_flatMap.mpr ⟨x.1.2, x.2.2, hv'⟩⟩
      exact (ih y (by show A.md + (x.1.1 + 1) ≤ N; omega)).mp (h y ⟨rfl, hv'⟩)
    · intro h y hy
      have hy₁' : y.1.1 = x.1.1 + 1 := hy.1
      exact (ih y (by omega)).mpr (h y.1.2 hy.2)

/-- The model of the levels has finitely many states. -/
theorem Tree.model_finite (t : Tree) (N : Nat) : (t.model N).Finite := by
  let l : List (Nat × Tree) :=
    (List.range (N + 1)).flatMap fun i => (t.level i).map fun u => (i, u)
  have hl : ∀ x, x ∈ l → x.1 ≤ N ∧ x.2 ∈ t.level x.1 := by
    intro x hx
    rcases List.mem_flatMap.mp hx with ⟨i, hi, hx⟩
    rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
    exact ⟨by have := List.mem_range.mp hi; omega, hu⟩
  refine ⟨l.pmap Subtype.mk hl, fun s => ?_⟩
  refine List.mem_pmap.mpr ⟨s.1, ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨s.1.1, List.mem_range.mpr (by have := s.2.1; omega),
    List.mem_map.mpr ⟨s.1.2, s.2.2, rfl⟩⟩

/-- For the members of a list, each with the proof that it is one: all
have `P`, or not all. -/
theorem forall_mem_or_not {α : Type} : ∀ (l : List α) (P : (v : α) → v ∈ l → Prop),
    (∀ v h, P v h ∨ ¬ P v h) → (∀ v h, P v h) ∨ ¬ (∀ v h, P v h) := by
  intro l
  induction l with
  | nil => exact fun _ _ => .inl fun _ h => nomatch h
  | cons a l ih =>
    intro P hP
    rcases ih (fun v h => P v (.tail _ h)) (fun v h => hP v (.tail _ h)) with h | h
    · rcases hP a (.head _) with ha | ha
      · refine .inl fun v hv => ?_
        cases hv with
        | head => exact ha
        | tail _ hv => exact h v hv
      · exact .inr fun h' => ha (h' a (.head _))
    · exact .inr fun h' => h fun v hv => h' v (.tail _ hv)

/-- For the members of a list: one has `P`, or none. -/
theorem exists_mem_or_not {α : Type} : ∀ (l : List α) (P : (v : α) → v ∈ l → Prop),
    (∀ v h, P v h ∨ ¬ P v h) → (∃ v h, P v h) ∨ ¬ (∃ v h, P v h) := by
  intro l
  induction l with
  | nil => exact fun _ _ => .inr fun ⟨_, h, _⟩ => nomatch h
  | cons a l ih =>
    intro P hP
    rcases hP a (.head _) with ha | ha
    · exact .inl ⟨a, .head _, ha⟩
    · rcases ih (fun v h => P v (.tail _ h)) (fun v h => hP v (.tail _ h)) with ⟨v, hv, hp⟩ | h
      · exact .inl ⟨v, .tail _ hv, hp⟩
      · refine .inr ?_
        rintro ⟨v, hv, hp⟩
        cases hv with
        | head => exact ha hp
        | tail _ hv => exact h ⟨v, hv, hp⟩

/-- The state of a child, one level down. -/
def Tree.child (t : Tree) (N : Nat) (x : (t.model N).W) (hlt : x.1.1 + 1 ≤ N) (v : Tree)
    (hv : v ∈ x.1.2.kids) : (t.model N).W :=
  ⟨(x.1.1 + 1, v), hlt, List.mem_flatMap.mpr ⟨x.1.2, x.2.2, hv⟩⟩

/-- A state related to `x` is the state of a child of `x`. -/
theorem Tree.eq_child (t : Tree) (N : Nat) {x y : (t.model N).W} (h : (t.model N).R x y) :
    ∃ (hlt : x.1.1 + 1 ≤ N) (hv : y.1.2 ∈ x.1.2.kids), y = t.child N x hlt y.1.2 hv := by
  have h₁ : y.1.1 = x.1.1 + 1 := h.1
  have h₂ : y.1.2 ∈ x.1.2.kids := h.2
  have hy := y.2.1
  exact ⟨by omega, h₂, Subtype.ext (Prod.ext h₁ rfl)⟩

/-- The model of the levels is two-valued. -/
theorem Tree.model_twoValued (t : Tree) (N : Nat) : (t.model N).TwoValued := by
  intro A
  induction A with
  | atom p =>
    intro x
    exact Decidable.em (p ∈ x.1.2.val)
  | natom p =>
    intro x
    rcases Decidable.em (p ∈ x.1.2.val) with h | h
    · exact .inr fun h' => h' h
    · exact .inl h
  | or A B ihA ihB =>
    intro s
    rcases ihA s with h | h
    · exact .inl (.inl h)
    · rcases ihB s with h' | h'
      · exact .inl (.inr h')
      · exact .inr fun h'' => h''.elim h h'
  | and A B ihA ihB =>
    intro s
    rcases ihA s with h | h
    · rcases ihB s with h' | h'
      · exact .inl ⟨h, h'⟩
      · exact .inr fun h'' => h' h''.2
    · exact .inr fun h'' => h h''.1
  | dia A ih =>
    intro x
    by_cases hlt : x.1.1 + 1 ≤ N
    · rcases exists_mem_or_not x.1.2.kids
          (fun v hv => (t.model N).sat (t.child N x hlt v hv) A)
          (fun v hv => ih (t.child N x hlt v hv)) with ⟨v, hv, hs⟩ | h
      · exact .inl ⟨t.child N x hlt v hv, ⟨rfl, hv⟩, hs⟩
      · refine .inr ?_
        rintro ⟨y, hy, hs⟩
        rcases t.eq_child N hy with ⟨_, hv, e⟩
        exact h ⟨y.1.2, hv, e ▸ hs⟩
    · refine .inr ?_
      rintro ⟨y, hy, _⟩
      rcases t.eq_child N hy with ⟨hlt', _, _⟩
      exact hlt hlt'
  | box A ih =>
    intro x
    by_cases hlt : x.1.1 + 1 ≤ N
    · rcases forall_mem_or_not x.1.2.kids
          (fun v hv => (t.model N).sat (t.child N x hlt v hv) A)
          (fun v hv => ih (t.child N x hlt v hv)) with h | h
      · refine .inl fun y hy => ?_
        rcases t.eq_child N hy with ⟨_, hv, e⟩
        exact e ▸ h y.1.2 hv
      · exact .inr fun h' => h fun v hv => h' _ ⟨rfl, hv⟩
    · refine .inl fun y hy => ?_
      rcases t.eq_child N hy with ⟨hlt', _, _⟩
      exact absurd hlt' hlt

/-! ## The finite model property (Corollary 2.24) -/

/-- **The finite model property** (Corollary 2.24, at `X = ∅`): a sequent
that is not valid is not true at some state of a two-valued model with
finitely many states. -/
def FiniteModelProperty : Prop :=
  ∀ Γ : NSeq, ¬ Valid Γ →
    ∃ M : Model, M.TwoValued ∧ M.Finite ∧ ∃ s : M.W, ¬ M.sat s Γ.form

theorem finiteModelProperty : FiniteModelProperty := by
  intro Γ hΓ
  rcases search Γ with d | r
  · exact absurd (soundness Γ d) hΓ
  · let s : (r.tree.model Γ.form.md).W := ⟨(0, r.tree), Nat.zero_le _, .head _⟩
    refine ⟨r.tree.model Γ.form.md, r.tree.model_twoValued _, r.tree.model_finite _, s, ?_⟩
    exact fun h => r.refutes ((r.tree.sat_model _ Γ.form s (Nat.le_refl _)).mp h)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
