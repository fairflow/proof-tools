/-
The model of finite trees is a two-valued model of GL, truth in it is
what `Form.holds` computes, and the part of it below a tree is a finite
model with the same truth.  So a refuted sequent is not valid.  Theory
file: it ends with its bound on axioms.
-/
import GLS.Lemmas

namespace GLS

/-! ## Descendants -/

theorem Tree.desc_node (v : List Nat) (ks : List Tree) : (Tree.node v ks).desc = Tree.descL ks := by
  simp [Tree.desc]

theorem Tree.descL_cons (t : Tree) (ts : List Tree) :
    Tree.descL (t :: ts) = t :: (t.desc ++ Tree.descL ts) := by
  simp [Tree.descL]

/-- The trees of `descL ks`: each tree of `ks`, and its proper descendants. -/
theorem Tree.mem_descL {ks : List Tree} {u : Tree} :
    u ∈ Tree.descL ks ↔ ∃ k ∈ ks, u = k ∨ u ∈ k.desc := by
  induction ks with
  | nil => simp [Tree.descL]
  | cons t ts ih =>
    rw [Tree.descL_cons]
    simp only [List.mem_cons, List.mem_append, ih]
    constructor
    · rintro (h | h | ⟨k, hk, h⟩)
      · exact ⟨t, .inl rfl, .inl h⟩
      · exact ⟨t, .inl rfl, .inr h⟩
      · exact ⟨k, .inr hk, h⟩
    · rintro ⟨k, hk | hk, h⟩
      · subst hk
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr ⟨k, hk, h⟩)

/-- The proper descendants of a tree: each child, and its proper
descendants. -/
theorem Tree.mem_desc {t u : Tree} : u ∈ t.desc ↔ ∃ k ∈ t.kids, u = k ∨ u ∈ k.desc := by
  cases t with
  | node v ks => rw [Tree.desc_node, Tree.mem_descL]; rfl

mutual
  /-- The number of nodes of a tree. -/
  def Tree.size : Tree → Nat
    | .node _ ks => Tree.sizeL ks + 1
  /-- The number of nodes of the trees of a list. -/
  def Tree.sizeL : List Tree → Nat
    | [] => 0
    | t :: ts => t.size + Tree.sizeL ts
end

theorem Tree.size_le_sizeL {ks : List Tree} {k : Tree} (h : k ∈ ks) : k.size ≤ Tree.sizeL ks := by
  induction ks with
  | nil => cases h
  | cons t ts ih =>
    simp only [Tree.sizeL]
    rcases List.mem_cons.1 h with h | h
    · subst h; omega
    · have := ih h; omega

theorem Tree.size_kid {t k : Tree} (h : k ∈ t.kids) : k.size < t.size := by
  cases t with
  | node v ks =>
    have := Tree.size_le_sizeL (ks := ks) h
    simp only [Tree.size]
    omega

/-- A proper descendant is smaller. -/
theorem Tree.size_desc : ∀ (n : Nat) (t u : Tree), t.size ≤ n → u ∈ t.desc → u.size < t.size := by
  intro n
  induction n with
  | zero =>
    intro t u hn _
    cases t with
    | node v ks => simp [Tree.size] at hn
  | succ n ih =>
    intro t u hn hu
    obtain ⟨k, hk, h⟩ := Tree.mem_desc.1 hu
    have hlt := Tree.size_kid hk
    rcases h with h | h
    · subst h; exact hlt
    · have := ih k u (by omega) h
      omega

/-- The proper descendants of a proper descendant are proper descendants. -/
theorem Tree.desc_trans : ∀ (n : Nat) (t u v : Tree), t.size ≤ n →
    u ∈ t.desc → v ∈ u.desc → v ∈ t.desc := by
  intro n
  induction n with
  | zero =>
    intro t u v hn _ _
    cases t with
    | node w ks => simp [Tree.size] at hn
  | succ n ih =>
    intro t u v hn hu hv
    obtain ⟨k, hk, h⟩ := Tree.mem_desc.1 hu
    have hlt := Tree.size_kid hk
    rcases h with h | h
    · subst h
      exact Tree.mem_desc.2 ⟨u, hk, .inr hv⟩
    · exact Tree.mem_desc.2 ⟨k, hk, .inr (ih k u v (by omega) h hv)⟩

/-! ## The model of finite trees -/

/-- The model of finite trees is a model of GL. -/
theorem treeModel_GL : treeModel.GL where
  trans x y z hxy hyz := Tree.desc_trans x.size x y z (Nat.le_refl _) hxy hyz
  cwf := Subrelation.wf (r := InvImage (· < ·) Tree.size)
    (fun {x y} (h : x ∈ y.desc) => Tree.size_desc y.size y x (Nat.le_refl _) h)
    (InvImage.wf Tree.size Nat.lt_wfRel.wf)

/-- Truth at a tree is what `Form.holds` computes. -/
theorem holds_iff : ∀ (A : Form) (t : Tree), A.holds t = true ↔ treeModel.sat t A
  | .var p, t => by
    show t.val.contains p = true ↔ p ∈ t.val
    exact List.contains_iff_mem
  | ⊥, t => by simp [Form.holds, Model.sat]
  | A ⟶ B, t => by
    have ihA := holds_iff A t
    have ihB := holds_iff B t
    show (!A.holds t || B.holds t) = true ↔ (treeModel.sat t A → treeModel.sat t B)
    rw [← ihA, ← ihB]
    cases A.holds t <;> cases B.holds t <;> simp
  | □A, t => by
    show t.desc.all (fun u => A.holds u) = true ↔ ∀ v, v ∈ t.desc → treeModel.sat v A
    rw [List.all_eq_true]
    exact ⟨fun h v hv => (holds_iff A v).1 (h v hv), fun h v hv => (holds_iff A v).2 (h v hv)⟩

/-- The model of finite trees is two-valued. -/
theorem treeModel_twoValued : treeModel.TwoValued := by
  intro A t
  cases h : A.holds t with
  | true => exact .inl ((holds_iff A t).1 h)
  | false => exact .inr (fun hs => by rw [(holds_iff A t).2 hs] at h; cases h)

/-- A sequent that `refutedAt` finds false at a tree is not true there. -/
theorem not_satSeq_of_refutedAt {s : Seq} {t : Tree} (h : s.refutedAt t = true) :
    ¬ treeModel.satSeq t s := by
  intro hs
  simp only [Seq.refutedAt, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨B, hB, hsat⟩ := hs (fun A hA => (holds_iff A t).1 (h.1 A hA))
  have := h.2 B hB
  rw [(holds_iff B t).2 hsat] at this
  cases this

/-- A sequent that is not true at a tree is one `refutedAt` finds false
there. -/
theorem refutedAt_of_not_satSeq {s : Seq} {t : Tree} (h : ¬ treeModel.satSeq t s) :
    s.refutedAt t = true := by
  simp only [Seq.refutedAt, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro A hA
    cases hh : A.holds t with
    | true => rfl
    | false =>
      exfalso
      apply h
      intro hall
      have := (holds_iff A t).2 (hall A hA)
      rw [this] at hh
      cases hh
  · intro B hB
    cases hh : B.holds t with
    | false => rfl
    | true => exact absurd (fun _ => ⟨B, hB, (holds_iff B t).1 hh⟩) h

/-- What a tree refutes is not valid. -/
theorem Refutation.not_valid {s : Seq} (r : Refutation s) : ¬ Valid s :=
  fun h => r.refutes (h treeModel treeModel_GL treeModel_twoValued r.tree)

/-! ## The part below a tree: a finite model -/

/-- Truth in the part below a tree is truth in the model of finite
trees. -/
theorem subModel_sat (t : Tree) : ∀ (A : Form) (u : (subModel t).W),
    (subModel t).sat u A ↔ treeModel.sat u.1 A
  | .var _, _ => Iff.rfl
  | ⊥, _ => Iff.rfl
  | A ⟶ B, u => by
    show ((subModel t).sat u A → (subModel t).sat u B) ↔ (treeModel.sat u.1 A → treeModel.sat u.1 B)
    rw [subModel_sat t A u, subModel_sat t B u]
  | □A, u => by
    show (∀ v : (subModel t).W, v.1 ∈ u.1.desc → (subModel t).sat v A) ↔
      (∀ v : Tree, v ∈ u.1.desc → treeModel.sat v A)
    constructor
    · intro h v hv
      have hmem : v = t ∨ v ∈ t.desc := by
        rcases u.2 with hu | hu
        · exact .inr (hu ▸ hv)
        · exact .inr (Tree.desc_trans t.size t u.1 v (Nat.le_refl _) hu hv)
      exact (subModel_sat t A ⟨v, hmem⟩).1 (h ⟨v, hmem⟩ hv)
    · intro h v hv
      exact (subModel_sat t A v).2 (h v.1 hv)

theorem subModel_GL (t : Tree) : (subModel t).GL where
  trans x y z hxy hyz := Tree.desc_trans x.1.size x.1 y.1 z.1 (Nat.le_refl _) hxy hyz
  cwf := Subrelation.wf (r := InvImage (· < ·) (fun u : (subModel t).W => u.1.size))
    (fun {x y} (h : x.1 ∈ y.1.desc) => Tree.size_desc y.1.size y.1 x.1 (Nat.le_refl _) h)
    (InvImage.wf _ Nat.lt_wfRel.wf)

theorem subModel_twoValued (t : Tree) : (subModel t).TwoValued := by
  intro A u
  rcases treeModel_twoValued A u.1 with h | h
  · exact .inl ((subModel_sat t A u).2 h)
  · exact .inr (fun hs => h ((subModel_sat t A u).1 hs))

theorem subModel_finite (t : Tree) : (subModel t).Finite := by
  refine ⟨(t :: t.desc).attach.map (fun u => ⟨u.1, by
    rcases List.mem_cons.1 u.2 with h | h
    · exact .inl h
    · exact .inr h⟩), ?_⟩
  intro w
  rw [List.mem_map]
  refine ⟨⟨w.1, ?_⟩, List.mem_attach _ _, rfl⟩
  rcases w.2 with h | h
  · exact List.mem_cons.2 (.inl h)
  · exact List.mem_cons.2 (.inr h)

/-- The sequent of a refutation is false at a world of a finite two-valued
model of GL: the root of its tree, in the part below it. -/
theorem Refutation.finite {s : Seq} (r : Refutation s) :
    ∃ M : Model, M.GL ∧ M.TwoValued ∧ M.Finite ∧ ∃ w : M.W, ¬ M.satSeq w s := by
  refine ⟨subModel r.tree, subModel_GL _, subModel_twoValued _, subModel_finite _,
    ⟨r.tree, .inl rfl⟩, ?_⟩
  intro h
  apply r.refutes
  intro hant
  obtain ⟨B, hB, hsat⟩ := h (fun A hA => (subModel_sat r.tree A _).2 (hant A hA))
  exact ⟨B, hB, (subModel_sat r.tree B _).1 hsat⟩

end GLS

#axioms_within_file [propext, Quot.sound]
