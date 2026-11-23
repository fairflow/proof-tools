/-
The depth of a proof; necessitation, weakening and exchange, each
admissible with a proof of at most the same depth.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Lemma 2.4 (i)
(`l:stradm`), pp. 10–11, for `nec` and `wk`; Figure 2.4
(`fig:admissible`).  Exchange is not in the source, whose sequents are
multisets.  The depth of a derivation is used by the source (p. 8) and
not defined there (`campaign/rule-table.md`, D13).  Theory file: it ends
with its bound on axioms.

One theorem does the work, `Fam.sub`: if `Γ` embeds in `Γ'` (each node's
formulas are among those of its image, counted with multiplicity, and
distinct boxes of a node go to distinct boxes of its image), a proof of
`Γ` gives a proof of `Γ'` of at most the same depth.  Weakening and
exchange are instances.
-/
import BrunnlerK.Ctx

namespace BrunnlerK

/-! ## The depth of a proof -/

/-- **The depth of a proof**: the number of rule instances on its longest
branch.  An instance of the axiom is a leaf, at depth 0. -/
def Fam.depth {c : Bool} : {Γ : NSeq} → Fam c Γ → Nat
  | _, .ax .. => 0
  | _, .and _ _ _ _ _ d₁ d₂ => max d₁.depth d₂.depth + 1
  | _, .or _ _ _ _ _ d => d.depth + 1
  | _, .box _ _ _ _ d => d.depth + 1
  | _, .dia _ _ _ _ _ _ d => d.depth + 1
  | _, .cut _ _ _ _ d₁ d₂ => max d₁.depth d₂.depth + 1

/-- Carrying a proof into a context does not change its depth. -/
theorem Fam.depth_lift {c : Bool} {Θ : NSeq} (d : Fam c Θ) :
    ∀ {Γ : NSeq} (a : Path) (h : Γ.node? a = some Θ), (d.lift a h).depth = d.depth := by
  induction d with
  | ax => intros; rfl
  | and _ _ _ _ _ _ _ ih₁ ih₂ => intro Γ a h; simp [Fam.lift, Fam.depth, ih₁, ih₂]
  | or _ _ _ _ _ _ ih => intro Γ a h; simp [Fam.lift, Fam.depth, ih]
  | box _ _ _ _ _ ih => intro Γ a h; simp [Fam.lift, Fam.depth, ih]
  | dia _ _ _ _ _ _ _ ih => intro Γ a h; simp [Fam.lift, Fam.depth, ih]
  | cut _ _ _ _ _ _ ih₁ ih₂ => intro Γ a h; simp [Fam.lift, Fam.depth, ih₁, ih₂]

namespace NSeq

/-! ## Two more functions on sequents -/

/-- `Γ.removeBox i` is `Γ` without its box at position `i`. -/
def removeBox : NSeq → Nat → NSeq
  | leaf fs, _ => leaf fs
  | cons _ r, 0 => r
  | cons Δ r, i + 1 => cons Δ (r.removeBox i)

/-- `Γ.withForms fs` is `Γ` with its formulas replaced by `fs`. -/
def withForms : NSeq → List Form → NSeq
  | leaf _, fs => leaf fs
  | cons Δ r, fs => cons Δ (r.withForms fs)

/-- The position in `Γ` of the box that is at position `k` of
`Γ.removeBox i`. -/
def skip (i k : Nat) : Nat := if k < i then k else k + 1

theorem skip_zero (k : Nat) : skip 0 k = k + 1 := by simp [skip]

theorem skip_succ_zero (i : Nat) : skip (i + 1) 0 = 0 := by simp [skip]

theorem skip_succ_succ (i k : Nat) : skip (i + 1) (k + 1) = skip i k + 1 := by
  simp only [skip, Nat.add_lt_add_iff_right]
  split <;> rfl

theorem skip_ne (i k : Nat) : skip i k ≠ i := by
  simp only [skip]
  split <;> omega

@[simp] theorem forms_removeBox (Γ : NSeq) (i : Nat) : (Γ.removeBox i).forms = Γ.forms := by
  induction Γ generalizing i with
  | leaf fs => rfl
  | cons Δ r _ ih => cases i with
    | zero => rfl
    | succ i => simpa [removeBox, forms] using ih i

@[simp] theorem forms_withForms (Γ : NSeq) (fs : List Form) : (Γ.withForms fs).forms = fs := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simpa [withForms, forms] using ih

@[simp] theorem box?_withForms (Γ : NSeq) (fs : List Form) (i : Nat) :
    (Γ.withForms fs).box? i = Γ.box? i := by
  induction Γ generalizing i with
  | leaf gs => rfl
  | cons Δ r _ ih => cases i with
    | zero => rfl
    | succ i => simpa [withForms, box?] using ih i

theorem removeBox_withForms (Γ : NSeq) (fs : List Form) (i : Nat) :
    (Γ.withForms fs).removeBox i = (Γ.removeBox i).withForms fs := by
  induction Γ generalizing i with
  | leaf gs => rfl
  | cons Δ r _ ih => cases i with
    | zero => rfl
    | succ i => simp [withForms, removeBox, ih]

theorem add_eq_withForms (Γ : NSeq) (A : Form) : Γ.add A = Γ.withForms (A :: Γ.forms) := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simp [add, withForms, forms, ih]

theorem erase_eq_withForms (Γ : NSeq) (A : Form) :
    Γ.erase A = Γ.withForms (Γ.forms.erase A) := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simp [erase, withForms, forms, ih]

theorem withForms_forms (Γ : NSeq) : Γ.withForms Γ.forms = Γ := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simp [withForms, forms, ih]

theorem box?_removeBox (Γ : NSeq) (i k : Nat) :
    (Γ.removeBox i).box? k = Γ.box? (skip i k) := by
  induction Γ generalizing i k with
  | leaf fs => rfl
  | cons Δ r _ ih =>
    cases i with
    | zero => simp [removeBox, skip_zero, box?]
    | succ i =>
      cases k with
      | zero => simp [removeBox, skip_succ_zero, box?]
      | succ k => simp [removeBox, skip_succ_succ, box?, ih]

theorem removeBox_setBox (Γ : NSeq) (i : Nat) (X : NSeq) :
    (Γ.setBox i X).removeBox i = Γ.removeBox i := by
  induction Γ generalizing i with
  | leaf fs => rfl
  | cons Δ r _ ih => cases i with
    | zero => rfl
    | succ i => simp [setBox, removeBox, ih]

theorem removeBox_setBox_skip (Γ : NSeq) (i k : Nat) (X : NSeq) :
    (Γ.setBox (skip i k) X).removeBox i = (Γ.removeBox i).setBox k X := by
  induction Γ generalizing i k with
  | leaf fs => rfl
  | cons Δ r _ ih =>
    cases i with
    | zero => simp [removeBox, skip_zero, setBox]
    | succ i =>
      cases k with
      | zero => simp [removeBox, skip_succ_zero, setBox]
      | succ k => simp [removeBox, skip_succ_succ, setBox, ih]

theorem box?_setBox_ne (Γ : NSeq) {i k : Nat} (X : NSeq) (h : k ≠ i) :
    (Γ.setBox k X).box? i = Γ.box? i := by
  induction Γ generalizing i k with
  | leaf fs => rfl
  | cons Δ r _ ih =>
    cases k with
    | zero =>
      cases i with
      | zero => exact absurd rfl h
      | succ i => rfl
    | succ k =>
      cases i with
      | zero => rfl
      | succ i => simpa [setBox, box?] using ih (i := i) (k := k) (by omega)

theorem box?_addBox_of_some {Γ Δ : NSeq} {i : Nat} (Λ : NSeq) (h : Γ.box? i = some Δ) :
    (Γ.addBox Λ).box? i = some Δ := by
  induction Γ generalizing i with
  | leaf fs => cases h
  | cons Δ' r _ ih => cases i with
    | zero => simpa [addBox, box?] using h
    | succ i => simpa [addBox, box?] using ih (by simpa [box?] using h)

theorem removeBox_addBox_of_some {Γ Δ : NSeq} {i : Nat} (Λ : NSeq) (h : Γ.box? i = some Δ) :
    (Γ.addBox Λ).removeBox i = (Γ.removeBox i).addBox Λ := by
  induction Γ generalizing i with
  | leaf fs => cases h
  | cons Δ' r _ ih => cases i with
    | zero => rfl
    | succ i => simp [addBox, removeBox, ih (by simpa [box?] using h)]

theorem removeBox_addBox (Γ Λ : NSeq) : (Γ.addBox Λ).removeBox Γ.boxes.length = Γ := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simp [addBox, boxes, removeBox, ih]

/-! ## Embedding -/

/-- **`Γ` embeds in `Γ'`**: the formulas of `Γ` are among those of `Γ'`,
each as many times at least; and the boxes of `Γ`, one after the other,
embed in boxes of `Γ'` at different positions.  By recursion on `Γ`: a
box `[Δ]` of `Γ` embeds in a box at some position `i` of `Γ'`, and the
rest of `Γ` embeds in `Γ'` without that box. -/
def Sub : NSeq → NSeq → Prop
  | leaf fs, Γ' => ∀ A, fs.count A ≤ Γ'.forms.count A
  | cons Δ r, Γ' => ∃ i Δ', Γ'.box? i = some Δ' ∧ Sub Δ Δ' ∧ Sub r (Γ'.removeBox i)

theorem Sub.refl : ∀ Γ : NSeq, Sub Γ Γ := by
  intro Γ
  induction Γ with
  | leaf fs => exact fun _ => Nat.le_refl _
  | cons Δ r ihΔ ihr => exact ⟨0, Δ, rfl, ihΔ, ihr⟩

theorem Sub.forms {Γ Γ' : NSeq} (h : Sub Γ Γ') (A : Form) :
    Γ.forms.count A ≤ Γ'.forms.count A := by
  induction Γ generalizing Γ' with
  | leaf fs => exact h A
  | cons Δ r _ ih =>
    rcases h with ⟨i, Δ', _, _, hr⟩
    simpa [NSeq.forms] using ih hr

theorem Sub.mem {Γ Γ' : NSeq} (h : Sub Γ Γ') {A : Form} (hA : A ∈ Γ.forms) :
    A ∈ Γ'.forms :=
  List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr hA) (h.forms A))

theorem Sub.withForms {Γ Γ' : NSeq} (h : Sub Γ Γ') {fs fs' : List Form}
    (hf : ∀ A, fs.count A ≤ fs'.count A) : Sub (Γ.withForms fs) (Γ'.withForms fs') := by
  induction Γ generalizing Γ' with
  | leaf gs => intro A; simpa [NSeq.withForms] using hf A
  | cons Δ r _ ih =>
    rcases h with ⟨i, Δ', hb, hΔ, hr⟩
    refine ⟨i, Δ', by simpa using hb, hΔ, ?_⟩
    rw [removeBox_withForms]
    exact ih hr

theorem Sub.add {Γ Γ' : NSeq} (h : Sub Γ Γ') (A : Form) : Sub (Γ.add A) (Γ'.add A) := by
  rw [add_eq_withForms, add_eq_withForms]
  refine h.withForms fun B => ?_
  simp only [List.count_cons]
  exact Nat.add_le_add_right (h.forms B) _

theorem count_erase_ne {fs : List Form} {X B : Form} (h : B ≠ X) :
    (fs.erase X).count B = fs.count B := by
  induction fs with
  | nil => rfl
  | cons C fs ih =>
    by_cases e : C = X
    · subst e
      have : ¬ C = B := fun e' => h e'.symm
      simp [this]
    · simp only [List.erase_cons, beq_iff_eq, e, if_false, List.count_cons, ih]

theorem count_erase_self {fs : List Form} {X : Form} (h : X ∈ fs) :
    (fs.erase X).count X + 1 = fs.count X := by
  induction fs with
  | nil => cases h
  | cons C fs ih =>
    by_cases e : C = X
    · subst e
      simp
    · have h' : X ∈ fs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      simp only [List.erase_cons, beq_iff_eq, e, if_false, List.count_cons]
      have := ih h'
      omega

theorem erase_of_not_mem {fs : List Form} {X : Form} (h : X ∉ fs) : fs.erase X = fs := by
  induction fs with
  | nil => rfl
  | cons C fs ih =>
    have e : ¬ C = X := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [List.erase_cons, beq_iff_eq, e, if_false]
    rw [ih fun h' => h (List.mem_cons_of_mem _ h')]

/-- Taking one `X` out of both keeps "each formula as many times at
least". -/
theorem count_erase_le {fs fs' : List Form} (h : ∀ A, fs.count A ≤ fs'.count A)
    (X B : Form) : (fs.erase X).count B ≤ (fs'.erase X).count B := by
  by_cases e : B = X
  · subst e
    by_cases hm : B ∈ fs
    · have hm' : B ∈ fs' :=
        List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr hm) (h B))
      have h₁ := count_erase_self hm
      have h₂ := count_erase_self hm'
      have := h B
      omega
    · rw [erase_of_not_mem hm]
      have h₀ : fs.count B = 0 := by
        cases hc : fs.count B with
        | zero => rfl
        | succ n => exact absurd (List.count_pos_iff.mp (by omega)) hm
      omega
  · rw [count_erase_ne e, count_erase_ne e]
    exact h B

theorem Sub.erase {Γ Γ' : NSeq} (h : Sub Γ Γ') (X : Form) : Sub (Γ.erase X) (Γ'.erase X) := by
  rw [erase_eq_withForms, erase_eq_withForms]
  exact h.withForms (count_erase_le h.forms X)

theorem Sub.addBox {Γ Γ' Λ Λ' : NSeq} (h : Sub Γ Γ') (hΛ : Sub Λ Λ') :
    Sub (Γ.addBox Λ) (Γ'.addBox Λ') := by
  induction Γ generalizing Γ' with
  | leaf fs =>
    refine ⟨Γ'.boxes.length, Λ', box?_addBox Γ' Λ', hΛ, ?_⟩
    rw [removeBox_addBox]
    exact h
  | cons Δ r _ ih =>
    rcases h with ⟨i, Δ', hb, hΔ, hr⟩
    refine ⟨i, Δ', box?_addBox_of_some Λ' hb, hΔ, ?_⟩
    rw [removeBox_addBox_of_some Λ' hb]
    exact ih hr

/-- A box of `Γ` embeds in a box of `Γ'`, and replacing both keeps the
embedding. -/
theorem Sub.box {Γ Γ' Δ : NSeq} {j : Nat} (h : Sub Γ Γ') (hj : Γ.box? j = some Δ) :
    ∃ j' Δ', Γ'.box? j' = some Δ' ∧ Sub Δ Δ' ∧
      ∀ X X', Sub X X' → Sub (Γ.setBox j X) (Γ'.setBox j' X') := by
  induction Γ generalizing Γ' j with
  | leaf fs => cases hj
  | cons Δ₀ r _ ih =>
    rcases h with ⟨i, Δ₀', hb, hΔ₀, hr⟩
    cases j with
    | zero =>
      have e : Δ₀ = Δ := by simpa [NSeq.box?] using hj
      subst e
      refine ⟨i, Δ₀', hb, hΔ₀, fun X X' hX => ?_⟩
      refine ⟨i, X', box?_setBox_self X' hb, hX, ?_⟩
      rw [removeBox_setBox]
      exact hr
    | succ j =>
      rcases ih hr (by simpa [NSeq.box?] using hj) with ⟨k, Δ', hk, hΔ, hset⟩
      refine ⟨skip i k, Δ', by rw [← box?_removeBox]; exact hk, hΔ, fun X X' hX => ?_⟩
      refine ⟨i, Δ₀', by rw [box?_setBox_ne _ _ (skip_ne i k)]; exact hb, hΔ₀, ?_⟩
      rw [removeBox_setBox_skip]
      exact hset X X' hX

/-- The node at a path of `Γ` embeds in a node of `Γ'`, and replacing
both keeps the embedding. -/
theorem Sub.node {Γ Γ' Θ : NSeq} {a : Path} (h : Sub Γ Γ') (ha : Γ.node? a = some Θ) :
    ∃ a' Θ', Γ'.node? a' = some Θ' ∧ Sub Θ Θ' ∧
      ∀ X X', Sub X X' → Sub (Γ.setNode a X) (Γ'.setNode a' X') := by
  induction a generalizing Γ Γ' with
  | nil =>
    have e : Γ = Θ := by simpa [NSeq.node?] using ha
    subst e
    exact ⟨[], Γ', rfl, h, fun X X' hX => hX⟩
  | cons j a ih =>
    simp only [NSeq.node?] at ha
    cases hb : Γ.box? j with
    | none => simp [hb] at ha
    | some Δ =>
      simp only [hb] at ha
      rcases h.box hb with ⟨j', Δ', hb', hΔ, hset⟩
      rcases ih hΔ ha with ⟨a', Θ', hn, hΘ, hset'⟩
      refine ⟨j' :: a', Θ', by simp [NSeq.node?, hb', hn], hΘ, fun X X' hX => ?_⟩
      simp only [NSeq.setNode, hb, hb']
      exact hset _ _ (hset' X X' hX)

/-- A box replaced by one it embeds in. -/
theorem Sub.setBox_right {Γ Δ Δ' : NSeq} {i : Nat} (hb : Γ.box? i = some Δ) (h : Sub Δ Δ') :
    Sub Γ (Γ.setBox i Δ') := by
  induction Γ generalizing i with
  | leaf fs => cases hb
  | cons Δ₀ r _ ih =>
    cases i with
    | zero =>
      have e : Δ₀ = Δ := by simpa [NSeq.box?] using hb
      subst e
      exact ⟨0, Δ', rfl, h, Sub.refl r⟩
    | succ i => exact ⟨0, Δ₀, rfl, Sub.refl Δ₀, ih (by simpa [NSeq.box?] using hb)⟩

/-- A node replaced by one it embeds in. -/
theorem Sub.setNode_right {Γ Θ Θ' : NSeq} {a : Path} (ha : Γ.node? a = some Θ)
    (h : Sub Θ Θ') : Sub Γ (Γ.setNode a Θ') := by
  induction a generalizing Γ with
  | nil =>
    have e : Γ = Θ := by simpa [NSeq.node?] using ha
    subst e
    exact h
  | cons j a ih =>
    simp only [NSeq.node?] at ha
    cases hb : Γ.box? j with
    | none => simp [hb] at ha
    | some Δ =>
      simp only [hb] at ha
      simp only [NSeq.setNode, hb]
      exact Sub.setBox_right hb (ih ha)

/-- `Θ` embeds in `Θ, Δ`. -/
theorem Sub.comma (Θ Δ : NSeq) : Sub Θ (Θ.comma Δ) := by
  induction Θ with
  | leaf fs =>
    intro A
    simp only [NSeq.comma, forms_appendForms, List.count_append]
    omega
  | cons Λ r _ ih => exact ⟨0, Λ, rfl, Sub.refl Λ, ih⟩

end NSeq

/-! ## Embedding is admissible, with the depth -/

open NSeq in
/-- **If `Γ` embeds in `Γ'`, a proof of `Γ` gives a proof of `Γ'` of at
most the same depth.**  In K, and in K with cut. -/
theorem Fam.sub {c : Bool} {Γ : NSeq} (d : Fam c Γ) :
    ∀ {Γ' : NSeq}, Sub Γ Γ' → ∃ d' : Fam c Γ', d'.depth ≤ d.depth := by
  induction d with
  | @ax Γ Θ a p hΘ hp hn =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, _⟩
    exact ⟨.ax a' p hΘ' (hs.mem hp) (hs.mem hn), Nat.le_refl _⟩
  | @and Γ Θ a A B hΘ hA d₁ d₂ ih₁ ih₂ =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases ih₁ (hset _ _ ((hs.erase (A ⋏ B)).add A)) with ⟨e₁, h₁⟩
    rcases ih₂ (hset _ _ ((hs.erase (A ⋏ B)).add B)) with ⟨e₂, h₂⟩
    refine ⟨.and a' A B hΘ' (hs.mem hA) e₁ e₂, ?_⟩
    simp only [Fam.depth]
    omega
  | @or Γ Θ a A B hΘ hA d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases ih (hset _ _ (((hs.erase (A ⋎ B)).add B).add A)) with ⟨e, he⟩
    exact ⟨.or a' A B hΘ' (hs.mem hA) e, Nat.succ_le_succ he⟩
  | @box Γ Θ a A hΘ hA d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases ih (hset _ _ ((hs.erase (□A)).addBox (Sub.refl (.leaf [A])))) with ⟨e, he⟩
    exact ⟨.box a' A hΘ' (hs.mem hA) e, Nat.succ_le_succ he⟩
  | @dia Γ Θ Δ a i A hΘ hA hΔ d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases hs.box hΔ with ⟨i', Δ', hΔ', hsΔ, hsetΔ⟩
    rcases ih (hset _ _ (hsetΔ _ _ (hsΔ.add A))) with ⟨e, he⟩
    exact ⟨.dia a' i' A hΘ' (hs.mem hA) hΔ' e, Nat.succ_le_succ he⟩
  | @cut Γ Θ a A hc hΘ d₁ d₂ ih₁ ih₂ =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases ih₁ (hset _ _ (hs.add A)) with ⟨e₁, h₁⟩
    rcases ih₂ (hset _ _ (hs.add ∼A)) with ⟨e₂, h₂⟩
    refine ⟨.cut a' A hc hΘ' e₁ e₂, ?_⟩
    simp only [Fam.depth]
    omega

/-! ## Necessitation and weakening (Lemma 2.4 (i), Figure 2.4) -/

/-- **`nec` is admissible, with the depth**: from a proof of `Γ`, a proof
of `[Γ]` of the same depth. -/
theorem nec {c : Bool} {Γ : NSeq} (d : Fam c Γ) :
    ∃ d' : Fam c (.cons Γ (.leaf [])), d'.depth ≤ d.depth :=
  ⟨d.lift [0] rfl, Nat.le_of_eq (d.depth_lift [0] rfl)⟩

/-- **`wk` is admissible, with the depth**: from a proof of `Γ{∅}`, a
proof of `Γ{Δ}` of at most the same depth. -/
theorem wk {c : Bool} (C : Ctx) (Δ : NSeq) (d : Fam c (C.fill (.leaf []))) :
    ∃ d' : Fam c (C.fill Δ), d'.depth ≤ d.depth := by
  refine d.sub ?_
  rw [Ctx.fill_empty]
  exact NSeq.Sub.setNode_right C.at_path (NSeq.Sub.comma C.side Δ)

/-! ## Exchange -/

/-- `Γ.swap i` is `Γ` with its boxes at positions `i` and `i + 1`
exchanged.  Where there are no two such boxes, it is `Γ`. -/
def NSeq.swap : NSeq → Nat → NSeq
  | .leaf fs, _ => .leaf fs
  | .cons Δ r, i + 1 => .cons Δ (r.swap i)
  | .cons Δ (.leaf fs), 0 => .cons Δ (.leaf fs)
  | .cons Δ₁ (.cons Δ₂ r), 0 => .cons Δ₂ (.cons Δ₁ r)

/-- **Exchange**: `Exch Γ Γ'` if `Γ'` is `Γ` with the formulas of its
nodes permuted and the boxes of its nodes permuted.  Generated by: the
formulas of one node permuted; two neighbouring boxes of one node
exchanged; and doing one after another. -/
inductive Exch : NSeq → NSeq → Prop where
  | refl (Γ : NSeq) : Exch Γ Γ
  /-- The formulas of the node at the path `a` permuted. -/
  | forms {Γ Θ : NSeq} (a : Path) (fs : List Form) (hΘ : Γ.node? a = some Θ)
      (hp : Θ.forms.Perm fs) : Exch Γ (Γ.setNode a (Θ.withForms fs))
  /-- The boxes at positions `i` and `i + 1` of the node at the path `a`
  exchanged. -/
  | boxes {Γ Θ : NSeq} (a : Path) (i : Nat) (hΘ : Γ.node? a = some Θ) :
      Exch Γ (Γ.setNode a (Θ.swap i))
  | trans {Γ₁ Γ₂ Γ₃ : NSeq} (h₁ : Exch Γ₁ Γ₂) (h₂ : Exch Γ₂ Γ₃) : Exch Γ₁ Γ₃

theorem NSeq.Sub.swap (Θ : NSeq) (i : Nat) : NSeq.Sub Θ (Θ.swap i) := by
  induction Θ generalizing i with
  | leaf fs => exact Sub.refl _
  | cons Δ r _ ih =>
    cases i with
    | succ i => exact ⟨0, Δ, rfl, Sub.refl Δ, ih i⟩
    | zero =>
      cases r with
      | leaf fs => exact Sub.refl _
      | cons Δ₂ r' => exact ⟨1, Δ, rfl, Sub.refl Δ, Sub.refl _⟩

/-- **Exchange is admissible, with the depth**: if `Γ'` is `Γ` with
formulas and boxes permuted inside its nodes, a proof of `Γ` gives a
proof of `Γ'` of at most the same depth. -/
theorem exchange {c : Bool} {Γ Γ' : NSeq} (h : Exch Γ Γ') :
    ∀ d : Fam c Γ, ∃ d' : Fam c Γ', d'.depth ≤ d.depth := by
  induction h with
  | refl Γ => exact fun d => ⟨d, Nat.le_refl _⟩
  | @forms Γ Θ a fs hΘ hp =>
    intro d
    refine d.sub (NSeq.Sub.setNode_right hΘ ?_)
    have := (NSeq.Sub.refl Θ).withForms (fs := Θ.forms) (fs' := fs)
      (fun A => Nat.le_of_eq (hp.count_eq A))
    rwa [NSeq.withForms_forms] at this
  | @boxes Γ Θ a i hΘ =>
    exact fun d => d.sub (NSeq.Sub.setNode_right hΘ (NSeq.Sub.swap Θ i))
  | trans _ _ ih₁ ih₂ =>
    intro d
    rcases ih₁ d with ⟨d₁, h₁⟩
    rcases ih₂ d₁ with ⟨d₂, h₂⟩
    exact ⟨d₂, Nat.le_trans h₂ h₁⟩

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
