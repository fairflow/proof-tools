/-
A search that gives, for every nested sequent, a proof in system K or a
finite tree that refutes it.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Theorem 2.23
(completeness), pp. 17–19, at `X = ∅`, for what is proved.  The search is
not the source's procedure `prove` (pp. 16–17), which applies the rules
of K° anywhere in the sequent and is shown to end by a bound on set
sequents.  This one works at the root of a sequent and then inside one
box at a time, and ends because a weight goes down
(`BrunnlerK/Weight.lean`):

1. if the root has `p` and `p̄`: the axiom;
2. if not, while the root has a formula `A ∧ B`, `A ∨ B` or `□A`: the
   rule for it, upwards, at the root, and from 1 again;
3. then the root has propositions, negated propositions and formulas
   `◇B` only: for each box `[Δ]` of the root, search `Δ, B₁, …, Bₖ`, where
   `◇B₁, …, ◇Bₖ` are the diamonds of the root.  A proof of one of these
   gives a proof of the whole (`◇k_c` `k` times, then `Fam.lift`).  If
   every one is refuted, the refuting trees are the children of a tree
   that refutes the whole.

Theory file: it ends with its bound on axioms.
-/
import BrunnlerK.Soundness
import BrunnlerK.Weight

namespace BrunnlerK

/-! ## The model of finite trees is two-valued -/

/-- Truth at a tree in the model of finite trees is what `Form.holds`
computes. -/
theorem holds_iff : ∀ (A : Form) (t : Tree), treeModel.sat t A ↔ A.holds t = true := by
  intro A
  induction A with
  | atom p => intro t; simp [Model.sat, Form.holds, treeModel]
  | natom p => intro t; simp [Model.sat, Form.holds, treeModel]
  | or A B ihA ihB => intro t; simp [Model.sat, Form.holds, ihA, ihB]
  | and A B ihA ihB => intro t; simp [Model.sat, Form.holds, ihA, ihB]
  | dia A ih =>
    intro t
    simp only [Model.sat, Form.holds, List.any_eq_true]
    exact exists_congr fun u => and_congr Iff.rfl (ih u)
  | box A ih =>
    intro t
    simp only [Model.sat, Form.holds, List.all_eq_true]
    exact forall_congr' fun u => imp_congr_right fun _ => ih u

/-- **The model of finite trees is two-valued.** -/
theorem treeModel_twoValued : TreeModelTwoValued := by
  intro A t
  rw [holds_iff]
  cases A.holds t
  · exact .inr (by simp)
  · exact .inl rfl

/-! ## What the search looks for at a root -/

/-- A formula that no rule of step 1 acts on: a proposition, a negated
proposition, or a formula `◇B`. -/
def Form.basic : Form → Bool
  | .atom _ => true
  | .natom _ => true
  | .dia _ => true
  | _ => false

/-- A proposition `p` of the second list whose negation `p̄` is in the
first: the first there is. -/
def findClash (fs : List Form) : List Form → Option Nat
  | [] => none
  | A :: gs =>
    match A with
    | .atom p => if Form.natom p ∈ fs then some p else findClash fs gs
    | _ => findClash fs gs

theorem findClash_some {fs gs : List Form} {p : Nat} (h : findClash fs gs = some p) :
    Form.atom p ∈ gs ∧ Form.natom p ∈ fs := by
  induction gs with
  | nil => cases h
  | cons A gs ih =>
    cases A with
    | atom q =>
      simp only [findClash] at h
      split at h
      · rename_i hq
        have : q = p := by simpa using h
        subst this
        exact ⟨List.mem_cons_self .., hq⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    | natom _ | or _ _ | and _ _ | dia _ | box _ =>
      simp only [findClash] at h
      exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem findClash_none {fs gs : List Form} (h : findClash fs gs = none) :
    ∀ p, Form.atom p ∈ gs → Form.natom p ∉ fs := by
  induction gs with
  | nil => intro p hp; cases hp
  | cons A gs ih =>
    intro p hp
    cases A with
    | atom q =>
      simp only [findClash] at h
      split at h
      · cases h
      · rename_i hq
        rcases List.mem_cons.mp hp with e | hp
        · have : p = q := by simpa using e
          exact this ▸ hq
        · exact ih h p hp
    | natom _ | or _ _ | and _ _ | dia _ | box _ =>
      simp only [findClash] at h
      rcases List.mem_cons.mp hp with e | hp
      · cases e
      · exact ih h p hp

/-- The proposition `p`, of the formula `p̄`. -/
def Form.unneg : Form → Option Nat
  | .natom p => some p
  | _ => none

/-- The propositions `p` with `p̄` in the list. -/
def negs (fs : List Form) : List Nat := fs.filterMap Form.unneg

theorem mem_negs {fs : List Form} {p : Nat} : p ∈ negs fs ↔ Form.natom p ∈ fs := by
  simp only [negs, List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, e⟩
    cases A <;> simp [Form.unneg] at e
    exact e ▸ hA
  · intro h
    exact ⟨_, h, rfl⟩

/-! ## The semantic side of the steps -/

namespace NSeq

variable {M : Model}

/-- If `Γ` is true, so is the left premise of `∧` at the root. -/
theorem sat_and_left {Γ : NSeq} (A B : Form) {s : M.W} (h : Γ.sat M s) :
    ((Γ.erase (A ⋏ B)).add A).sat M s := by
  rcases sat_erase_cases (A ⋏ B) h with h | h
  · exact sat_add.mpr (.inl h.1)
  · exact sat_add.mpr (.inr h)

/-- If `Γ` is true, so is the right premise of `∧` at the root. -/
theorem sat_and_right {Γ : NSeq} (A B : Form) {s : M.W} (h : Γ.sat M s) :
    ((Γ.erase (A ⋏ B)).add B).sat M s := by
  rcases sat_erase_cases (A ⋏ B) h with h | h
  · exact sat_add.mpr (.inl h.2)
  · exact sat_add.mpr (.inr h)

/-- If `Γ` is true, so is the premise of `∨` at the root. -/
theorem sat_or_prem {Γ : NSeq} (A B : Form) {s : M.W} (h : Γ.sat M s) :
    (((Γ.erase (A ⋎ B)).add B).add A).sat M s := by
  rcases sat_erase_cases (A ⋎ B) h with h | h
  · rcases h with h | h
    · exact sat_add.mpr (.inl h)
    · exact sat_add.mpr (.inr (sat_add.mpr (.inl h)))
  · exact sat_add.mpr (.inr (sat_add.mpr (.inr h)))

/-- If `Γ` is true, so is the premise of `□` at the root. -/
theorem sat_box_prem {Γ : NSeq} (A : Form) {s : M.W} (h : Γ.sat M s) :
    ((Γ.erase (□A)).addBox (.leaf [A])).sat M s := by
  rcases sat_erase_cases (□A) h with h | h
  · exact sat_addBox.mpr (.inr fun t ht => sat_single.mpr (h t ht))
  · exact sat_addBox.mpr (.inl h)

theorem sat_foldl_add {Bs : List Form} {Δ : NSeq} {s : M.W} :
    (Bs.foldl NSeq.add Δ).sat M s ↔ (∃ B, B ∈ Bs ∧ M.sat s B) ∨ Δ.sat M s := by
  induction Bs generalizing Δ with
  | nil => simp
  | cons B Bs ih =>
    rw [List.foldl_cons, ih, sat_add]
    constructor
    · rintro (⟨C, hC, h⟩ | h | h)
      · exact .inl ⟨C, List.mem_cons_of_mem _ hC, h⟩
      · exact .inl ⟨B, List.mem_cons_self .., h⟩
      · exact .inr h
    · rintro (⟨C, hC, h⟩ | h)
      · rcases List.mem_cons.mp hC with rfl | hC
        · exact .inr (.inl h)
        · exact .inl ⟨C, hC, h⟩
      · exact .inr (.inr h)

/-- **The countermodel at a root that the search cannot go on from.**
The root has propositions, negated propositions and diamonds only, and
no `p` with `p̄`.  Each box, with the formulas under the root's diamonds
added, is refuted by one of the trees `ts`, and each of `ts` refutes one
of them.  Then the tree with the propositions `p` for `p̄` in the root,
and `ts` as its children, refutes the sequent. -/
theorem not_sat_saturated {Γ : NSeq} {ts : List Tree}
    (hb : ∀ A, A ∈ Γ.forms → A.basic = true)
    (hc : ∀ p, Form.atom p ∈ Γ.forms → Form.natom p ∉ Γ.forms)
    (h₁ : ∀ Δ, Δ ∈ Γ.boxes →
      ∃ u, u ∈ ts ∧ ¬ ((dias Γ.forms).foldl NSeq.add Δ).sat treeModel u)
    (h₂ : ∀ u, u ∈ ts →
      ∃ Δ, Δ ∈ Γ.boxes ∧ ¬ ((dias Γ.forms).foldl NSeq.add Δ).sat treeModel u) :
    ¬ Γ.sat treeModel (.node (negs Γ.forms) ts) := by
  intro h
  rcases (sat_iff Γ _).mp h with ⟨A, hA, hs⟩ | ⟨Δ, hΔ, hs⟩
  · cases A with
    | atom p =>
      have hp : p ∈ negs Γ.forms := hs
      exact hc p hA (mem_negs.mp hp)
    | natom p =>
      have hp : ¬ p ∈ negs Γ.forms := hs
      exact hp (mem_negs.mpr hA)
    | dia B =>
      rcases hs with ⟨u, hu, hB⟩
      have hu' : u ∈ ts := hu
      rcases h₂ u hu' with ⟨Δ, _, hΔ⟩
      exact hΔ (sat_foldl_add.mpr (.inl ⟨B, mem_dias.mpr hA, hB⟩))
    | or A B => exact absurd (hb _ hA) (by simp [Form.basic])
    | and A B => exact absurd (hb _ hA) (by simp [Form.basic])
    | box A => exact absurd (hb _ hA) (by simp [Form.basic])
  · rcases h₁ Δ hΔ with ⟨u, hu, hn⟩
    exact hn (sat_foldl_add.mpr (.inr (hs u hu)))

end NSeq

/-! ## The search -/

/-- What the search gives for a sequent: a proof in system K, or a tree
at which the sequent is not true. -/
abbrev Found (Γ : NSeq) : Type := K Γ ⊕ {t : Tree // ¬ Γ.sat treeModel t}

/-- One of a list, with something for it. -/
structure Hit {α : Type} (P : α → Type) (l : List α) where
  /-- The one. -/
  x : α
  /-- It is of the list. -/
  mem : x ∈ l
  /-- What there is for it. -/
  val : P x

/-- Go through a list: the first member that has a `P`, with it; or, if
every member has a tree with `Q`, the list of those trees. -/
def sweep {α : Type} {P : α → Type} {Q : α → Tree → Prop} :
    (l : List α) → ((x : α) → x ∈ l → P x ⊕ {u : Tree // Q x u}) →
    Hit P l ⊕ {ts : List Tree //
      (∀ x, x ∈ l → ∃ u, u ∈ ts ∧ Q x u) ∧ (∀ u, u ∈ ts → ∃ x, x ∈ l ∧ Q x u)}
  | [], _ => .inr ⟨[], by constructor <;> (intro _ h; cases h)⟩
  | x :: l, f =>
    match f x (.head _) with
    | .inl d => .inl ⟨x, .head _, d⟩
    | .inr ⟨u, hu⟩ =>
      match sweep l (fun y hy => f y (.tail _ hy)) with
      | .inl ⟨y, hy, d⟩ => .inl ⟨y, .tail _ hy, d⟩
      | .inr ⟨ts, h₁, h₂⟩ =>
        .inr ⟨u :: ts,
          fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact ⟨u, .head _, hu⟩
            · rcases h₁ y hy with ⟨v, hv, hq⟩
              exact ⟨v, .tail _ hv, hq⟩,
          fun v hv => by
            rcases List.mem_cons.mp hv with rfl | hv
            · exact ⟨x, .head _, hu⟩
            · rcases h₂ v hv with ⟨y, hy, hq⟩
              exact ⟨y, .tail _ hy, hq⟩⟩

theorem lt_of_and {Γ : NSeq} {A B : Form} {n : Nat} (hm : A ⋏ B ∈ Γ.forms)
    (h : Γ.weight < n + 1) :
    ((Γ.erase (A ⋏ B)).add A).weight < n ∧ ((Γ.erase (A ⋏ B)).add B).weight < n := by
  have := NSeq.weight_erase hm
  simp only [NSeq.weight_add, Form.weight] at this ⊢
  constructor <;> omega

theorem lt_of_or {Γ : NSeq} {A B : Form} {n : Nat} (hm : A ⋎ B ∈ Γ.forms)
    (h : Γ.weight < n + 1) : (((Γ.erase (A ⋎ B)).add B).add A).weight < n := by
  have := NSeq.weight_erase hm
  simp only [NSeq.weight_add, Form.weight] at this ⊢
  omega

theorem lt_of_box {Γ : NSeq} {A : Form} {n : Nat} (hm : □A ∈ Γ.forms)
    (h : Γ.weight < n + 1) : ((Γ.erase (□A)).addBox (.leaf [A])).weight < n := by
  have := NSeq.weight_erase hm
  simp only [NSeq.weight_addBox, NSeq.weight, formsWeight, Form.weight] at this ⊢
  omega

theorem lt_of_kid {Γ Δ : NSeq} {n : Nat} (hΔ : Δ ∈ Γ.boxes) (h : Γ.weight < n + 1) :
    ((dias Γ.forms).foldl NSeq.add Δ).weight < n := by
  have h₁ := NSeq.weight_box_lt hΔ
  have h₂ := formsWeight_dias Γ.forms
  rw [NSeq.weight_foldl_add]
  omega

/-- The search, with a bound on the weight of the sequent.  The bound is
what the recursion is on. -/
def searchN : (n : Nat) → (Γ : NSeq) → Γ.weight < n → Found Γ
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, Γ, h =>
    match hc : findClash Γ.forms Γ.forms with
    | some p => .inl (.ax [] p rfl (findClash_some hc).1 (findClash_some hc).2)
    | none =>
    match hf : Γ.forms.find? (fun A => !A.basic) with
    | some (.and A B) =>
      have hm : A ⋏ B ∈ Γ.forms := List.mem_of_find?_eq_some hf
      match searchN n ((Γ.erase (A ⋏ B)).add A) (lt_of_and hm h).1 with
      | .inr ⟨t, ht⟩ => .inr ⟨t, fun hs => ht (NSeq.sat_and_left A B hs)⟩
      | .inl d₁ =>
        match searchN n ((Γ.erase (A ⋏ B)).add B) (lt_of_and hm h).2 with
        | .inr ⟨t, ht⟩ => .inr ⟨t, fun hs => ht (NSeq.sat_and_right A B hs)⟩
        | .inl d₂ => .inl (.and [] A B rfl hm d₁ d₂)
    | some (.or A B) =>
      have hm : A ⋎ B ∈ Γ.forms := List.mem_of_find?_eq_some hf
      match searchN n (((Γ.erase (A ⋎ B)).add B).add A) (lt_of_or hm h) with
      | .inr ⟨t, ht⟩ => .inr ⟨t, fun hs => ht (NSeq.sat_or_prem A B hs)⟩
      | .inl d => .inl (.or [] A B rfl hm d)
    | some (.box A) =>
      have hm : □A ∈ Γ.forms := List.mem_of_find?_eq_some hf
      match searchN n ((Γ.erase (□A)).addBox (.leaf [A])) (lt_of_box hm h) with
      | .inr ⟨t, ht⟩ => .inr ⟨t, fun hs => ht (NSeq.sat_box_prem A hs)⟩
      | .inl d => .inl (.box [] A rfl hm d)
    | some (.atom _) => absurd (List.find?_some hf) (by simp [Form.basic])
    | some (.natom _) => absurd (List.find?_some hf) (by simp [Form.basic])
    | some (.dia _) => absurd (List.find?_some hf) (by simp [Form.basic])
    | none =>
        match sweep (P := fun Δ => K ((dias Γ.forms).foldl NSeq.add Δ))
            (Q := fun Δ u => ¬ ((dias Γ.forms).foldl NSeq.add Δ).sat treeModel u)
            Γ.boxes (fun Δ hΔ => searchN n _ (lt_of_kid hΔ h)) with
        | .inl ⟨Δ, hΔ, d⟩ =>
          .inl (Fam.diaAll (dias Γ.forms) (Γ.boxIdx Δ)
            (fun _ hB => mem_dias.mp hB) (NSeq.box?_boxIdx hΔ)
            (d.lift [Γ.boxIdx Δ]
              (by simp [NSeq.node?, NSeq.box?_setBox_self _ (NSeq.box?_boxIdx hΔ)])))
        | .inr ⟨ts, h₁, h₂⟩ =>
          .inr ⟨.node (negs Γ.forms) ts,
            NSeq.not_sat_saturated
              (fun A hA => by
                have := List.find?_eq_none.mp hf A hA
                simpa using this)
              (findClash_none hc) h₁ h₂⟩

/-- **The search**: for a sequent, a proof in system K or a refutation. -/
def search (Γ : NSeq) : K Γ ⊕ Refutation Γ :=
  match searchN (Γ.weight + 1) Γ (Nat.lt_succ_self _) with
  | .inl d => .inl d
  | .inr ⟨t, ht⟩ => .inr ⟨t, fun h => ht ((treeModel.sat_form Γ t).mp h)⟩

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
