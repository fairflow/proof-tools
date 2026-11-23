/-
Soundness of system K, and of K with cut, for truth in two-valued models.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Lemma 2.8
(`l:deepsound`, deep inference is sound) and Theorem 2.9 (soundness),
p. 13.  The source's proof goes through a Hilbert system; this one is
direct, on the models.  Theory file: it ends with its bound on axioms.
-/
import BrunnlerK.Semantics
import BrunnlerK.Context

namespace BrunnlerK

/-! ## Truth of a sequent, stated on the sequent -/

/-- Truth of a sequent at a state, by the sequent's own structure: some
formula of it is true there, or for some box `[Δ]` of it, `Δ` is true at
every successor.  `sat_form` below: this is truth of the corresponding
formula. -/
def NSeq.sat (M : Model) : NSeq → M.W → Prop
  | .leaf fs, s => ∃ A, A ∈ fs ∧ M.sat s A
  | .cons Δ r, s => (∀ t, M.R s t → Δ.sat M t) ∨ r.sat M s

namespace Model

variable (M : Model)

theorem not_sat_bot (s : M.W) : ¬ M.sat s Form.bot := fun h => h.2 h.1

theorem sat_foldl_or (s : M.W) (As : List Form) (A : Form) :
    M.sat s (As.foldl (· ⋎ ·) A) ↔ M.sat s A ∨ ∃ B, B ∈ As ∧ M.sat s B := by
  induction As generalizing A with
  | nil => simp
  | cons B As ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro (h | ⟨C, hC, h⟩)
      · rcases h with h | h
        · exact .inl h
        · exact .inr ⟨B, List.mem_cons_self .., h⟩
      · exact .inr ⟨C, List.mem_cons_of_mem _ hC, h⟩
    · rintro (h | ⟨C, hC, h⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.mp hC with rfl | hC
        · exact .inl (.inr h)
        · exact .inr ⟨C, hC, h⟩

/-- A disjunction of a list is true where one of the list is. -/
theorem sat_disj (s : M.W) (As : List Form) :
    M.sat s (Form.disj As) ↔ ∃ A, A ∈ As ∧ M.sat s A := by
  cases As with
  | nil => simp [Form.disj, not_sat_bot]
  | cons A As =>
    rw [Form.disj, sat_foldl_or]
    constructor
    · rintro (h | ⟨B, hB, h⟩)
      · exact ⟨A, List.mem_cons_self .., h⟩
      · exact ⟨B, List.mem_cons_of_mem _ hB, h⟩
    · rintro ⟨B, hB, h⟩
      rcases List.mem_cons.mp hB with rfl | hB
      · exact .inl h
      · exact .inr ⟨B, hB, h⟩

/-- **Truth of the corresponding formula is truth of the sequent.** -/
theorem sat_form : ∀ (Γ : NSeq) (s : M.W), M.sat s Γ.form ↔ Γ.sat M s := by
  intro Γ
  induction Γ with
  | leaf fs =>
    intro s
    simp [NSeq.form, NSeq.forms, NSeq.boxForms, sat_disj, NSeq.sat]
  | cons Δ r ihΔ ihr =>
    intro s
    have hΔ : M.sat s (□Δ.form) ↔ ∀ t, M.R s t → Δ.sat M t := by
      simp only [Model.sat]
      exact forall_congr' fun t => imp_congr_right fun _ => ihΔ t
    simp only [NSeq.sat]
    rw [← ihr s, ← hΔ]
    simp only [NSeq.form, NSeq.forms, NSeq.boxForms, sat_disj, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨A, (h | rfl | h), hA⟩
      · exact .inr ⟨A, .inl h, hA⟩
      · exact .inl hA
      · exact .inr ⟨A, .inr h, hA⟩
    · rintro (h | ⟨A, (h | h), hA⟩)
      · exact ⟨_, .inr (.inl rfl), h⟩
      · exact ⟨A, .inl h, hA⟩
      · exact ⟨A, .inr (.inr h), hA⟩

/-- A formula and its negation are not both true at a state.  No
hypothesis on the model. -/
theorem not_sat_dual : ∀ (A : Form) (s : M.W), M.sat s (∼A) → M.sat s A → False := by
  intro A
  induction A with
  | atom p => intro s h h'; exact h h'
  | natom p => intro s h h'; exact h' h
  | or A B ihA ihB =>
    intro s h h'
    rcases h' with h' | h'
    · exact ihA s h.1 h'
    · exact ihB s h.2 h'
  | and A B ihA ihB =>
    intro s h h'
    rcases h with h | h
    · exact ihA s h h'.1
    · exact ihB s h h'.2
  | dia A ih =>
    intro s h h'
    rcases h' with ⟨t, ht, h'⟩
    exact ih t (h t ht) h'
  | box A ih =>
    intro s h h'
    rcases h with ⟨t, ht, h⟩
    exact ih t h (h' t ht)

end Model

/-- A sequent is valid if it is true, as a sequent, at every state of
every two-valued model. -/
theorem valid_iff {Γ : NSeq} :
    Valid Γ ↔ ∀ M : Model, M.TwoValued → ∀ s : M.W, Γ.sat M s :=
  forall_congr' fun M => imp_congr_right fun _ => forall_congr' fun s => M.sat_form Γ s

namespace NSeq

variable {M : Model}

/-- Truth of a sequent, by its formulas and its boxes. -/
theorem sat_iff (Γ : NSeq) (s : M.W) :
    Γ.sat M s ↔ (∃ A, A ∈ Γ.forms ∧ M.sat s A)
      ∨ ∃ Δ, Δ ∈ Γ.boxes ∧ ∀ t, M.R s t → Δ.sat M t := by
  induction Γ with
  | leaf fs => simp [sat, forms, boxes]
  | cons Δ r _ ih =>
    simp only [sat, forms, boxes, ih, List.mem_cons]
    constructor
    · rintro (h | h | ⟨Δ', hΔ', h⟩)
      · exact .inr ⟨Δ, .inl rfl, h⟩
      · exact .inl h
      · exact .inr ⟨Δ', .inr hΔ', h⟩
    · rintro (h | ⟨Δ', (rfl | hΔ'), h⟩)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr ⟨Δ', hΔ', h⟩)

theorem sat_of_form {Γ : NSeq} {s : M.W} {A : Form} (h : A ∈ Γ.forms) (hA : M.sat s A) :
    Γ.sat M s :=
  (sat_iff Γ s).mpr (.inl ⟨A, h, hA⟩)

theorem sat_of_box {Γ Δ : NSeq} {s : M.W} (h : Δ ∈ Γ.boxes)
    (hΔ : ∀ t, M.R s t → Δ.sat M t) : Γ.sat M s :=
  (sat_iff Γ s).mpr (.inr ⟨Δ, h, hΔ⟩)

theorem sat_add {Γ : NSeq} {A : Form} {s : M.W} :
    (Γ.add A).sat M s ↔ M.sat s A ∨ Γ.sat M s := by
  rw [sat_iff (Γ.add A) s, sat_iff Γ s]
  simp only [forms_add, boxes_add, List.mem_cons]
  constructor
  · rintro (⟨B, (rfl | hB), h⟩ | h)
    · exact .inl h
    · exact .inr (.inl ⟨B, hB, h⟩)
    · exact .inr (.inr h)
  · rintro (h | ⟨B, hB, h⟩ | h)
    · exact .inl ⟨A, .inl rfl, h⟩
    · exact .inl ⟨B, .inr hB, h⟩
    · exact .inr h

theorem sat_erase {Γ : NSeq} {A : Form} {s : M.W} (h : (Γ.erase A).sat M s) : Γ.sat M s := by
  rw [sat_iff (Γ.erase A) s] at h
  rw [sat_iff Γ s]
  simp only [forms_erase, boxes_erase] at h
  rcases h with ⟨B, hB, h⟩ | h
  · exact .inl ⟨B, List.mem_of_mem_erase hB, h⟩
  · exact .inr h

/-- A formula other than `A` stays when one `A` is taken out. -/
theorem mem_erase_of_ne {fs : List Form} {A B : Form} (e : B ≠ A) (h : B ∈ fs) :
    B ∈ fs.erase A := by
  induction fs with
  | nil => cases h
  | cons C fs ih =>
    by_cases eC : C = A
    · subst eC
      rcases List.mem_cons.mp h with h | h
      · exact absurd h e
      · simpa using h
    · simp only [List.erase_cons, beq_iff_eq, eC, if_false]
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- If a sequent is true, then the formula `A` is, or the sequent without
one `A` is. -/
theorem sat_erase_cases {Γ : NSeq} (A : Form) {s : M.W} (h : Γ.sat M s) :
    M.sat s A ∨ (Γ.erase A).sat M s := by
  rw [sat_iff Γ s] at h
  rw [sat_iff (Γ.erase A) s]
  simp only [forms_erase, boxes_erase]
  rcases h with ⟨B, hB, h⟩ | h
  · by_cases e : B = A
    · exact .inl (e ▸ h)
    · exact .inr (.inl ⟨B, mem_erase_of_ne e hB, h⟩)
  · exact .inr (.inr h)

theorem sat_addBox {Γ Λ : NSeq} {s : M.W} :
    (Γ.addBox Λ).sat M s ↔ Γ.sat M s ∨ ∀ t, M.R s t → Λ.sat M t := by
  rw [sat_iff (Γ.addBox Λ) s, sat_iff Γ s]
  simp only [forms_addBox, boxes_addBox, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | ⟨Δ, (hΔ | rfl), h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨Δ, hΔ, h⟩)
    · exact .inr h
  · rintro ((h | ⟨Δ, hΔ, h⟩) | h)
    · exact .inl h
    · exact .inr ⟨Δ, .inl hΔ, h⟩
    · exact .inr ⟨Λ, .inr rfl, h⟩

theorem sat_single {A : Form} {s : M.W} : (leaf [A]).sat M s ↔ M.sat s A := by
  simp [sat]

/-- A sequent with one box replaced is true where the new box is, or
where the sequent was already. -/
theorem sat_setBox {Γ Δ : NSeq} {i : Nat} (Λ : NSeq) {s : M.W} (h : Γ.box? i = some Δ)
    (hs : (Γ.setBox i Λ).sat M s) : (∀ t, M.R s t → Λ.sat M t) ∨ Γ.sat M s := by
  induction Γ generalizing i with
  | leaf fs => cases h
  | cons Δ' r _ ih =>
    cases i with
    | zero =>
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr hs)
    | succ i =>
      rcases hs with hs | hs
      · exact .inr (.inl hs)
      · rcases ih (by simpa [box?] using h) hs with h' | h'
        · exact .inl h'
        · exact .inr (.inr h')

theorem sat_of_box? {Γ Δ : NSeq} {i : Nat} {s : M.W} (h : Γ.box? i = some Δ)
    (hΔ : ∀ t, M.R s t → Δ.sat M t) : Γ.sat M s :=
  sat_of_box (mem_boxes_of_box? h) hΔ

/-! ## Deep inference is sound (Lemma 2.8) -/

/-- What is true at every state as a node is true at every state in any
context. -/
theorem deep₀ {Θ : NSeq} (h : ∀ t, Θ.sat M t) :
    ∀ (a : Path) (Γ : NSeq), Γ.node? a = some Θ → ∀ s, Γ.sat M s := by
  intro a
  induction a with
  | nil =>
    intro Γ hΘ s
    have : Γ = Θ := by simpa [node?] using hΘ
    exact this ▸ h s
  | cons i a ih =>
    intro Γ hΘ s
    simp only [node?] at hΘ
    cases hb : Γ.box? i with
    | none => simp [hb] at hΘ
    | some Δ =>
      simp only [hb] at hΘ
      exact sat_of_box? hb fun t _ => ih Δ hΘ t

/-- A rule with two premises that is sound at a node is sound in any
context: if `Θ` is true wherever `Θ₁` and `Θ₂` are, then `Γ{Θ}` is true
wherever `Γ{Θ₁}` and `Γ{Θ₂}` are. -/
theorem deep₂ {Θ Θ₁ Θ₂ : NSeq} (h : ∀ t, Θ₁.sat M t → Θ₂.sat M t → Θ.sat M t) :
    ∀ (a : Path) (Γ : NSeq), Γ.node? a = some Θ →
      ∀ s, (Γ.setNode a Θ₁).sat M s → (Γ.setNode a Θ₂).sat M s → Γ.sat M s := by
  intro a
  induction a with
  | nil =>
    intro Γ hΘ s h₁ h₂
    have : Γ = Θ := by simpa [node?] using hΘ
    exact this ▸ h s h₁ h₂
  | cons i a ih =>
    intro Γ hΘ s h₁ h₂
    simp only [node?] at hΘ
    cases hb : Γ.box? i with
    | none => simp [hb] at hΘ
    | some Δ =>
      simp only [hb] at hΘ
      simp only [setNode, hb] at h₁ h₂
      rcases sat_setBox _ hb h₁ with h₁ | h₁
      · rcases sat_setBox _ hb h₂ with h₂ | h₂
        · exact sat_of_box? hb fun t ht => ih Δ hΘ t (h₁ t ht) (h₂ t ht)
        · exact h₂
      · exact h₁

/-- The same for a rule with one premise. -/
theorem deep₁ {Θ Θ₁ : NSeq} (h : ∀ t, Θ₁.sat M t → Θ.sat M t)
    (a : Path) (Γ : NSeq) (hΘ : Γ.node? a = some Θ) (s : M.W)
    (h₁ : (Γ.setNode a Θ₁).sat M s) : Γ.sat M s :=
  deep₂ (fun t h₁ _ => h t h₁) a Γ hΘ s h₁ h₁

end NSeq

/-! ## Soundness (Theorem 2.9) -/

/-- A proof in K, or in K with cut, ends in a sequent that is true at
every state of every two-valued model.  The model's two values are used
for the axiom and for `◇k_c`; `cut` does not need them. -/
theorem Fam.sound {c : Bool} {Γ : NSeq} (d : Fam c Γ) (M : Model) (tv : M.TwoValued) :
    ∀ s : M.W, Γ.sat M s := by
  induction d with
  | @ax Γ Θ a p hΘ hp hn =>
    refine NSeq.deep₀ (fun t => ?_) a Γ hΘ
    rcases tv (.atom p) t with h | h
    · exact NSeq.sat_of_form hp h
    · exact NSeq.sat_of_form hn h
  | @and Γ Θ a A B hΘ hA _ _ ih₁ ih₂ =>
    intro s
    refine NSeq.deep₂ (fun t h₁ h₂ => ?_) a Γ hΘ s (ih₁ s) (ih₂ s)
    rcases NSeq.sat_add.mp h₁ with h₁ | h₁
    · rcases NSeq.sat_add.mp h₂ with h₂ | h₂
      · exact NSeq.sat_of_form hA ⟨h₁, h₂⟩
      · exact NSeq.sat_erase h₂
    · exact NSeq.sat_erase h₁
  | @or Γ Θ a A B hΘ hA _ ih =>
    intro s
    refine NSeq.deep₁ (fun t h => ?_) a Γ hΘ s (ih s)
    rcases NSeq.sat_add.mp h with h | h
    · exact NSeq.sat_of_form hA (.inl h)
    · rcases NSeq.sat_add.mp h with h | h
      · exact NSeq.sat_of_form hA (.inr h)
      · exact NSeq.sat_erase h
  | @box Γ Θ a A hΘ hA _ ih =>
    intro s
    refine NSeq.deep₁ (fun t h => ?_) a Γ hΘ s (ih s)
    rcases NSeq.sat_addBox.mp h with h | h
    · exact NSeq.sat_erase h
    · exact NSeq.sat_of_form hA fun u hu => NSeq.sat_single.mp (h u hu)
  | @dia Γ Θ Δ a i A hΘ hA hΔ _ ih =>
    intro s
    refine NSeq.deep₁ (fun t h => ?_) a Γ hΘ s (ih s)
    rcases NSeq.sat_setBox _ hΔ h with h | h
    · rcases tv (◇A) t with hd | hd
      · exact NSeq.sat_of_form hA hd
      · refine NSeq.sat_of_box? hΔ fun u hu => ?_
        rcases NSeq.sat_add.mp (h u hu) with h' | h'
        · exact absurd ⟨u, hu, h'⟩ hd
        · exact h'
    · exact h
  | @cut Γ Θ a A hc hΘ _ _ ih₁ ih₂ =>
    intro s
    refine NSeq.deep₂ (fun t h₁ h₂ => ?_) a Γ hΘ s (ih₁ s) (ih₂ s)
    rcases NSeq.sat_add.mp h₁ with h₁ | h₁
    · rcases NSeq.sat_add.mp h₂ with h₂ | h₂
      · exact (M.not_sat_dual A t h₂ h₁).elim
      · exact h₂
    · exact h₁

/-- **Soundness of K with cut**: `K + cut ⊢ Γ → Valid Γ`. -/
theorem soundnessCut : SoundnessCut :=
  fun _ d => valid_iff.mpr fun M tv s => d.sound M tv s

/-- **Soundness** (Theorem 2.9 (i), (iii), at `X = ∅`):
`K ⊢ Γ → Valid Γ`. -/
theorem soundness : Soundness :=
  fun _ d => valid_iff.mpr fun M tv s => d.sound M tv s

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
