/-
Invertibility of the rules `∧`, `∨` and `□`, with the depth.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Lemma 2.4 (ii)
(`l:stradm`), pp. 10–11: "All its rules are depth-preserving invertible."
The source's proof is "a routine induction on the depth of the proof".
Theory file: it ends with its bound on axioms.

The induction needs a statement about several occurrences at once.  For a
formula `X` that a rule acts on and the formulas `As` (and, for `□`, the
box) that the rule puts in its place: if `Γ'` is `Γ` with some
occurrences of `X` so replaced, at any nodes, and with anything added,
then a proof of `Γ` gives a proof of `Γ'` of at most the same depth
(`Fam.invert`).  The inverse rules are instances.
-/
import BrunnlerK.Structural
import BrunnlerK.Identity

namespace BrunnlerK

namespace NSeq

/-! ## Embedding, with any relation at the nodes -/

/-- `Γ.graft T` is `Γ` with `T` in place of its formulas: the boxes of
`Γ`, then `T`. -/
def graft : NSeq → NSeq → NSeq
  | leaf _, T => T
  | cons Δ r, T => cons Δ (r.graft T)

theorem withForms_eq_graft (Γ : NSeq) (fs : List Form) : Γ.withForms fs = Γ.graft (leaf fs) := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simp [withForms, graft, ih]

theorem addBox_eq_graft (Γ Λ : NSeq) : Γ.addBox Λ = Γ.graft (cons Λ (leaf Γ.forms)) := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simp [addBox, graft, forms, ih]

theorem graft_graft (Γ : NSeq) (fs : List Form) (T : NSeq) :
    (Γ.graft (leaf fs)).graft T = Γ.graft T := by
  induction Γ with
  | leaf _ => rfl
  | cons Δ r _ ih => simp [graft, ih]

theorem withForms_withForms (Γ : NSeq) (fs gs : List Form) :
    (Γ.withForms fs).withForms gs = Γ.withForms gs := by
  induction Γ with
  | leaf _ => rfl
  | cons Δ r _ ih => simp [withForms, ih]

@[simp] theorem boxes_withForms (Γ : NSeq) (fs : List Form) :
    (Γ.withForms fs).boxes = Γ.boxes := by
  induction Γ with
  | leaf _ => rfl
  | cons Δ r _ ih => simp [withForms, boxes, ih]

/-- **Embedding with a relation `R` at the nodes.**  As `Sub`: the boxes
of `Γ`, one after the other, embed in boxes of `Γ'` at different
positions.  What is asked of the formulas is `R`, of the formulas of `Γ`
and of what is left of `Γ'` when the boxes used are taken away. -/
def SubR (R : List Form → NSeq → Prop) : NSeq → NSeq → Prop
  | leaf fs, Γ' => R fs Γ'
  | cons Δ r, Γ' => ∃ i Δ', Γ'.box? i = some Δ' ∧ SubR R Δ Δ' ∧ SubR R r (Γ'.removeBox i)

variable {R : List Form → NSeq → Prop}

theorem SubR.refl (hR : ∀ fs, R fs (leaf fs)) : ∀ Γ : NSeq, SubR R Γ Γ := by
  intro Γ
  induction Γ with
  | leaf fs => exact hR fs
  | cons Δ r ihΔ ihr => exact ⟨0, Δ, rfl, ihΔ, ihr⟩

/-- What is left of `Γ'`, with the relation at the root. -/
theorem SubR.leaf {Γ Γ' : NSeq} (h : SubR R Γ Γ') :
    ∃ Λ, R Γ.forms Λ ∧ Λ.forms = Γ'.forms := by
  induction Γ generalizing Γ' with
  | leaf fs => exact ⟨Γ', h, rfl⟩
  | cons Δ r _ ih =>
    rcases h with ⟨i, Δ', _, _, hr⟩
    rcases ih hr with ⟨Λ, hΛ, hf⟩
    exact ⟨Λ, hΛ, by simpa using hf⟩

theorem SubR.box {Γ Γ' Δ : NSeq} {j : Nat} (h : SubR R Γ Γ') (hj : Γ.box? j = some Δ) :
    ∃ j' Δ', Γ'.box? j' = some Δ' ∧ SubR R Δ Δ' ∧
      ∀ X X', SubR R X X' → SubR R (Γ.setBox j X) (Γ'.setBox j' X') := by
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

theorem SubR.node {Γ Γ' Θ : NSeq} {a : Path} (h : SubR R Γ Γ') (ha : Γ.node? a = some Θ) :
    ∃ a' Θ', Γ'.node? a' = some Θ' ∧ SubR R Θ Θ' ∧
      ∀ X X', SubR R X X' → SubR R (Γ.setNode a X) (Γ'.setNode a' X') := by
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

theorem SubR.setBox_right (hR : ∀ fs, R fs (NSeq.leaf fs)) {Γ Δ Δ' : NSeq} {i : Nat}
    (hb : Γ.box? i = some Δ) (h : SubR R Δ Δ') : SubR R Γ (Γ.setBox i Δ') := by
  induction Γ generalizing i with
  | leaf fs => cases hb
  | cons Δ₀ r _ ih =>
    cases i with
    | zero =>
      have e : Δ₀ = Δ := by simpa [NSeq.box?] using hb
      subst e
      exact ⟨0, Δ', rfl, h, SubR.refl hR r⟩
    | succ i => exact ⟨0, Δ₀, rfl, SubR.refl hR Δ₀, ih (by simpa [NSeq.box?] using hb)⟩

theorem SubR.setNode_right (hR : ∀ fs, R fs (NSeq.leaf fs)) {Γ Θ Θ' : NSeq} {a : Path}
    (ha : Γ.node? a = some Θ) (h : SubR R Θ Θ') : SubR R Γ (Γ.setNode a Θ') := by
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
      exact SubR.setBox_right hR hb (ih ha)

/-- A change of a sequent that leaves its boxes where they are, and is
the same change when a box is taken away first. -/
structure Stable (F : NSeq → NSeq) : Prop where
  box : ∀ (Λ : NSeq) (i : Nat) (Δ : NSeq), Λ.box? i = some Δ → (F Λ).box? i = some Δ
  rem : ∀ (Λ : NSeq) (i : Nat) (Δ : NSeq), Λ.box? i = some Δ →
    (F Λ).removeBox i = F (Λ.removeBox i)

theorem Stable.id : Stable (fun Λ => Λ) := ⟨fun _ _ _ h => h, fun _ _ _ _ => rfl⟩

/-- New formulas, computed from the old ones. -/
theorem Stable.withForms (g : List Form → List Form) :
    Stable (fun Λ => Λ.withForms (g Λ.forms)) :=
  ⟨fun Λ i Δ h => by simpa using h,
   fun Λ i Δ _ => by simp [removeBox_withForms]⟩

/-- A stable change, and then a new box. -/
theorem Stable.addBox {F : NSeq → NSeq} (hF : Stable F) (Λ₀ : NSeq) :
    Stable (fun Λ => (F Λ).addBox Λ₀) :=
  ⟨fun Λ i Δ h => box?_addBox_of_some Λ₀ (hF.box Λ i Δ h),
   fun Λ i Δ h => by
    show ((F Λ).addBox Λ₀).removeBox i = (F (Λ.removeBox i)).addBox Λ₀
    rw [removeBox_addBox_of_some Λ₀ (hF.box Λ i Δ h), hF.rem Λ i Δ h]⟩

/-- Change the formulas of `Γ` to `T` and `Γ'` by a stable change: the
embedding stays, if the relation at the root does. -/
theorem SubR.graft_map {F : NSeq → NSeq} (hF : Stable F) {Γ Γ' T : NSeq}
    (h : SubR R Γ Γ')
    (hT : ∀ Λ, R Γ.forms Λ → Λ.forms = Γ'.forms → SubR R T (F Λ)) :
    SubR R (Γ.graft T) (F Γ') := by
  induction Γ generalizing Γ' with
  | leaf fs => exact hT Γ' h rfl
  | cons Δ r _ ih =>
    rcases h with ⟨i, Δ', hb, hΔ, hr⟩
    refine ⟨i, Δ', hF.box _ _ _ hb, hΔ, ?_⟩
    rw [hF.rem _ _ _ hb]
    exact ih hr fun Λ hΛ hf => hT Λ hΛ (by simpa using hf)

/-- `Γ` embeds in a stable change of itself, if the relation holds at
each root. -/
theorem SubR.diag (hR : ∀ fs, R fs (NSeq.leaf fs)) {F : NSeq → NSeq} (hF : Stable F)
    (Γ : NSeq) (h : R Γ.forms (F (NSeq.leaf Γ.forms))) : SubR R Γ (F Γ) := by
  induction Γ with
  | leaf fs => exact h
  | cons Δ r _ ih =>
    refine ⟨0, Δ, hF.box _ 0 Δ rfl, SubR.refl hR Δ, ?_⟩
    rw [hF.rem _ 0 Δ rfl]
    exact ih h

/-- The number of boxes of a sequent that have the formula `A`. -/
def boxCount (A : Form) : NSeq → Nat
  | leaf _ => 0
  | cons Δ r => (if A ∈ Δ.forms then 1 else 0) + r.boxCount A

theorem boxCount_withForms (A : Form) (Γ : NSeq) (fs : List Form) :
    (Γ.withForms fs).boxCount A = Γ.boxCount A := by
  induction Γ with
  | leaf _ => rfl
  | cons Δ r _ ih => simp [withForms, boxCount, ih]

/-- Where there are `k + 1` boxes with `A`, one can be taken away and `k`
are left. -/
theorem exists_box_of_boxCount {A : Form} {k : Nat} {Γ : NSeq} (h : k + 1 ≤ Γ.boxCount A) :
    ∃ i Δ, Γ.box? i = some Δ ∧ A ∈ Δ.forms ∧ k ≤ (Γ.removeBox i).boxCount A := by
  induction Γ with
  | leaf fs => simp [boxCount] at h
  | cons Δ r _ ih =>
    by_cases hA : A ∈ Δ.forms
    · refine ⟨0, Δ, rfl, hA, ?_⟩
      simp only [boxCount, hA, if_true] at h
      simp only [removeBox]
      omega
    · simp only [boxCount, hA, if_false] at h
      rcases ih (by omega) with ⟨i, Δ', hb, hA', hk⟩
      refine ⟨i + 1, Δ', by simpa [box?] using hb, hA', ?_⟩
      simp only [removeBox, boxCount, hA, if_false]
      omega

end NSeq

/-! ## Counting formulas -/

theorem count_cons_self' (A : Form) (l : List Form) : (A :: l).count A = l.count A + 1 := by
  simp

theorem count_cons_ne' {A B : Form} (h : A ≠ B) (l : List Form) :
    (A :: l).count B = l.count B := by
  simp [h]

theorem count_pos_of_mem {A : Form} {l : List Form} (h : A ∈ l) : 1 ≤ l.count A :=
  List.count_pos_iff.mpr h

theorem mem_of_count_pos {A : Form} {l : List Form} (h : 1 ≤ l.count A) : A ∈ l :=
  List.count_pos_iff.mp h

theorem count_eq_zero_of_not_mem' {A : Form} {l : List Form} (h : A ∉ l) : l.count A = 0 := by
  cases hc : l.count A with
  | zero => rfl
  | succ n => exact absurd (mem_of_count_pos (by omega)) h

/-- **`k` occurrences of `X` replaced by `As`.**  `Cnt X As k fs gs`: the
list `gs` has all the formulas of `fs`, counted, where `k` of the
occurrences of `X` in `fs` have each been replaced by the formulas `As`;
and `gs` may have more. -/
def Cnt (X : Form) (As : List Form) (k : Nat) (fs gs : List Form) : Prop :=
  k ≤ fs.count X ∧ fs.count X ≤ gs.count X + k ∧
    ∀ B, B ≠ X → fs.count B + k * As.count B ≤ gs.count B

namespace Cnt

variable {X : Form} {As : List Form} {k : Nat} {fs gs : List Form}

theorem refl (X : Form) (As : List Form) (fs : List Form) : Cnt X As 0 fs fs :=
  ⟨Nat.zero_le _, Nat.le_refl _, fun B _ => by simp⟩

theorem mem (h : Cnt X As k fs gs) {Y : Form} (hY : Y ∈ fs) (hne : Y ≠ X) : Y ∈ gs := by
  have h₁ := h.2.2 Y hne
  have h₂ := count_pos_of_mem hY
  exact mem_of_count_pos (by omega)

theorem cons (h : Cnt X As k fs gs) (C : Form) : Cnt X As k (C :: fs) (C :: gs) := by
  rcases h with ⟨h₁, h₂, h₃⟩
  refine ⟨?_, ?_, fun B hB => ?_⟩
  · by_cases e : C = X
    · rw [e, count_cons_self']; omega
    · rw [count_cons_ne' e]; exact h₁
  · by_cases e : C = X
    · rw [e, count_cons_self', count_cons_self']; omega
    · rw [count_cons_ne' e, count_cons_ne' e]; exact h₂
  · have := h₃ B hB
    by_cases e : C = B
    · rw [e, count_cons_self', count_cons_self']; omega
    · rw [count_cons_ne' e, count_cons_ne' e]; exact this

/-- One `Y` taken out of both, where both have it. -/
theorem erase (h : Cnt X As k fs gs) {Y : Form} (hf : Y ∈ fs) (hg : Y ∈ gs) :
    ∃ k', k' ≤ k ∧ Cnt X As k' (fs.erase Y) (gs.erase Y) := by
  rcases h with ⟨h₁, h₂, h₃⟩
  have hf₁ := NSeq.count_erase_self hf
  have hg₁ := NSeq.count_erase_self hg
  by_cases e : Y = X
  · subst e
    by_cases hlt : k < fs.count Y
    · refine ⟨k, Nat.le_refl _, by omega, by omega, fun B hB => ?_⟩
      rw [NSeq.count_erase_ne hB, NSeq.count_erase_ne hB]
      exact h₃ B hB
    · have hg₂ := count_pos_of_mem hg
      have hf₂ := count_pos_of_mem hf
      refine ⟨k - 1, Nat.sub_le _ _, by omega, by omega, fun B hB => ?_⟩
      rw [NSeq.count_erase_ne hB, NSeq.count_erase_ne hB]
      have := h₃ B hB
      have hm : (k - 1) * As.count B ≤ k * As.count B :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
  · have eX : X ≠ Y := fun e' => e e'.symm
    refine ⟨k, Nat.le_refl _, ?_, ?_, fun B hB => ?_⟩
    · rw [NSeq.count_erase_ne eX]; exact h₁
    · rw [NSeq.count_erase_ne eX, NSeq.count_erase_ne eX]; exact h₂
    · by_cases eB : B = Y
      · subst eB
        have := h₃ B hB
        omega
      · rw [NSeq.count_erase_ne eB, NSeq.count_erase_ne eB]
        exact h₃ B hB

/-- Where `gs` has no `X` left, all the occurrences of `X` in `fs` are
replaced; and then `fs` with one `X` replaced by `As` is `gs` with one
replacement less. -/
theorem prem (h : Cnt X As k fs gs) (hf : X ∈ fs) (hg : X ∉ gs) (hX : X ∉ As) :
    ∃ k', k' + 1 = k ∧ Cnt X As k' (As ++ fs.erase X) gs := by
  rcases h with ⟨h₁, h₂, h₃⟩
  have hg₀ := count_eq_zero_of_not_mem' hg
  have hA₀ := count_eq_zero_of_not_mem' hX
  have hf₁ := NSeq.count_erase_self hf
  have hf₂ := count_pos_of_mem hf
  refine ⟨k - 1, by omega, ?_, ?_, fun B hB => ?_⟩
  · rw [List.count_append, hA₀]; omega
  · rw [List.count_append, hA₀]; omega
  · rw [List.count_append, NSeq.count_erase_ne hB]
    have := h₃ B hB
    have hm : (k - 1) * As.count B + As.count B = k * As.count B := by
      have hk : k = (k - 1) + 1 := by omega
      conv => rhs; rw [hk, Nat.succ_mul]
    omega

/-- One `X` replaced. -/
theorem one (hf : X ∈ fs) (hX : X ∉ As) : Cnt X As 1 fs (As ++ fs.erase X) := by
  have hA₀ := count_eq_zero_of_not_mem' hX
  have hf₁ := NSeq.count_erase_self hf
  refine ⟨count_pos_of_mem hf, ?_, fun B hB => ?_⟩
  · rw [List.count_append, hA₀]; omega
  · rw [List.count_append, NSeq.count_erase_ne hB, Nat.one_mul]; omega

end Cnt

/-! ## The inversions -/

/-- **An inversion**: a rule of system K that takes its formula away, and
which premise. -/
inductive Inv where
  /-- `Γ{A ∧ B}` to `Γ{A}`. -/
  | andL (A B : Form)
  /-- `Γ{A ∧ B}` to `Γ{B}`. -/
  | andR (A B : Form)
  /-- `Γ{A ∨ B}` to `Γ{A, B}`. -/
  | or (A B : Form)
  /-- `Γ{□A}` to `Γ{[A]}`. -/
  | box (A : Form)

namespace Inv

/-- The formula the rule acts on. -/
def X : Inv → Form
  | andL A B => A ⋏ B
  | andR A B => A ⋏ B
  | or A B => A ⋎ B
  | box A => □A

/-- The formulas the premise has in its place. -/
def As : Inv → List Form
  | andL A _ => [A]
  | andR _ B => [B]
  | or A B => [A, B]
  | box _ => []

/-- For `□`: `Λ` has `k` boxes with `A`.  For the others, nothing. -/
def Extra : Inv → Nat → NSeq → Prop
  | box A, k, Λ => k ≤ Λ.boxCount A
  | _, _, _ => True

/-- The relation at a node: some number `k` of the occurrences of `X`
replaced; `Λ` is what is left of the node of `Γ'` when the boxes that
boxes of `Γ` embed in are taken away. -/
def R (v : Inv) (fs : List Form) (Λ : NSeq) : Prop :=
  ∃ k, Cnt v.X v.As k fs Λ.forms ∧ v.Extra k Λ

/-- What the premise has at the root, for the formulas `fs`: the formulas
`As` with one `X` out, and for `□` the new box. -/
def prem : Inv → List Form → NSeq
  | box A, fs => .cons (.leaf [A]) (.leaf (fs.erase (□A)))
  | v, fs => .leaf (v.As ++ fs.erase v.X)

theorem X_not_mem_As (v : Inv) : v.X ∉ v.As := by
  cases v with
  | andL A B =>
    simp only [X, As, List.mem_singleton]
    exact fun e => Form.ne_of_size (A := A) (B := A ⋏ B) (by simp only [Form.size]; omega) e.symm
  | andR A B =>
    simp only [X, As, List.mem_singleton]
    exact fun e => Form.ne_of_size (A := B) (B := A ⋏ B) (by simp only [Form.size]; omega) e.symm
  | or A B =>
    simp only [X, As, List.mem_cons, List.not_mem_nil, or_false]
    rintro (e | e)
    · exact Form.ne_of_size (A := A) (B := A ⋎ B) (by simp only [Form.size]; omega) e.symm
    · exact Form.ne_of_size (A := B) (B := A ⋎ B) (by simp only [Form.size]; omega) e.symm
  | box A => simp [As]

theorem Extra.mono {v : Inv} {k k' : Nat} {Λ : NSeq} (h : v.Extra k Λ) (hk : k' ≤ k) :
    v.Extra k' Λ := by
  cases v <;> simp only [Extra] at h ⊢
  exact Nat.le_trans hk h

theorem Extra.zero (v : Inv) (Λ : NSeq) : v.Extra 0 Λ := by
  cases v <;> simp [Extra]

theorem Extra.withForms {v : Inv} {k : Nat} {Λ : NSeq} (h : v.Extra k Λ) (fs : List Form) :
    v.Extra k (Λ.withForms fs) := by
  cases v <;> simp only [Extra] at h ⊢
  rw [NSeq.boxCount_withForms]
  exact h

theorem R.refl (v : Inv) (fs : List Form) : v.R fs (.leaf fs) :=
  ⟨0, Cnt.refl _ _ _, Extra.zero _ _⟩

/-- A formula added to both. -/
theorem R.cons {v : Inv} {fs : List Form} {Λ : NSeq} (h : v.R fs Λ) (C : Form) :
    v.R (C :: fs) (Λ.withForms (C :: Λ.forms)) := by
  rcases h with ⟨k, hc, he⟩
  exact ⟨k, by simpa using hc.cons C, he.withForms _⟩

/-- One `Y` taken out of both, where both have it. -/
theorem R.erase {v : Inv} {fs : List Form} {Λ : NSeq} (h : v.R fs Λ) {Y : Form}
    (hf : Y ∈ fs) (hg : Y ∈ Λ.forms) : v.R (fs.erase Y) (Λ.withForms (Λ.forms.erase Y)) := by
  rcases h with ⟨k, hc, he⟩
  rcases hc.erase hf hg with ⟨k', hk', hc'⟩
  exact ⟨k', by simpa using hc', (he.mono hk').withForms _⟩

/-- Where the node of `Γ'` has no `X`: the premise of the rule on `X`
embeds in it. -/
theorem R.prem {v : Inv} {fs : List Form} {Λ : NSeq} (h : v.R fs Λ)
    (hf : v.X ∈ fs) (hg : v.X ∉ Λ.forms) : NSeq.SubR v.R (v.prem fs) Λ := by
  rcases h with ⟨k, hc, he⟩
  rcases hc.prem hf hg v.X_not_mem_As with ⟨k', hk', hc'⟩
  cases v with
  | andL A B => exact ⟨k', hc', trivial⟩
  | andR A B => exact ⟨k', hc', trivial⟩
  | or A B => exact ⟨k', hc', trivial⟩
  | box A =>
    simp only [Extra] at he
    rcases NSeq.exists_box_of_boxCount (A := A) (Γ := Λ) (k := k') (by omega) with ⟨i, Δ, hb, hA, hk⟩
    refine ⟨i, Δ, hb, ?_, ?_⟩
    · have hne : A ≠ □A := Form.ne_of_size (by simp only [Form.size]; omega)
      have h₀ : ([A] : List Form).count (□A) = 0 := by rw [count_cons_ne' hne]; rfl
      refine ⟨0, ⟨Nat.zero_le _, by simp only [X]; omega, fun B hB => ?_⟩, Nat.zero_le _⟩
      by_cases e : A = B
      · subst e
        have := count_pos_of_mem hA
        simp
        omega
      · simp [e]
    · exact ⟨k', by simpa [As, X] using hc', hk⟩

end Inv

/-! ## The theorem -/

section

open NSeq

variable {c : Bool}

theorem src_add_erase (Θ : NSeq) (Y C : Form) :
    (Θ.erase Y).add C = Θ.graft (.leaf (C :: Θ.forms.erase Y)) := by
  rw [add_eq_withForms, erase_eq_withForms, forms_withForms, withForms_withForms,
    withForms_eq_graft]

theorem src_add_add_erase (Θ : NSeq) (Y A B : Form) :
    ((Θ.erase Y).add B).add A = Θ.graft (.leaf (A :: B :: Θ.forms.erase Y)) := by
  rw [add_eq_withForms ((Θ.erase Y).add B), add_eq_withForms (Θ.erase Y), erase_eq_withForms]
  simp only [forms_withForms, withForms_withForms]
  exact withForms_eq_graft _ _

theorem src_addBox_erase (Θ : NSeq) (Y : Form) (Λ : NSeq) :
    (Θ.erase Y).addBox Λ = Θ.graft (.cons Λ (.leaf (Θ.forms.erase Y))) := by
  rw [addBox_eq_graft, erase_eq_withForms, forms_withForms, withForms_eq_graft, graft_graft]

/-- The premise of a rule with one new formula embeds in the same of the
target, where the target has the rule's formula. -/
theorem Inv.step₁ (v : Inv) {Θ Θ' : NSeq} (hs : SubR v.R Θ Θ') {Y : Form}
    (hf : Y ∈ Θ.forms) (hg : Y ∈ Θ'.forms) (C : Form) :
    SubR v.R ((Θ.erase Y).add C) ((Θ'.erase Y).add C) := by
  rw [src_add_erase, add_eq_withForms, erase_eq_withForms, forms_withForms, withForms_withForms]
  refine hs.graft_map (Stable.withForms fun gs => C :: gs.erase Y) fun Λ hΛ hf' => ?_
  have h₁ := (hΛ.erase hf (hf' ▸ hg)).cons C
  rw [withForms_withForms, forms_withForms] at h₁
  exact h₁

/-- A formula added to both. -/
theorem Inv.stepAdd (v : Inv) {Θ Θ' : NSeq} (hs : SubR v.R Θ Θ') (C : Form) :
    SubR v.R (Θ.add C) (Θ'.add C) := by
  rw [add_eq_withForms, add_eq_withForms, withForms_eq_graft]
  exact hs.graft_map (Stable.withForms fun gs => C :: gs) fun Λ hΛ _ => hΛ.cons C

/-- The premise of `□` embeds in the same of the target. -/
theorem Inv.stepBox (v : Inv) {Θ Θ' : NSeq} (hs : SubR v.R Θ Θ') {Y : Form}
    (hf : Y ∈ Θ.forms) (hg : Y ∈ Θ'.forms) (C : Form) :
    SubR v.R ((Θ.erase Y).addBox (.leaf [C])) ((Θ'.erase Y).addBox (.leaf [C])) := by
  rw [src_addBox_erase, erase_eq_withForms]
  refine hs.graft_map ((Stable.withForms fun gs => gs.erase Y).addBox (.leaf [C]))
    fun Λ hΛ hf' => ?_
  refine ⟨(Λ.withForms (Λ.forms.erase Y)).boxes.length, .leaf [C], box?_addBox _ _,
    Inv.R.refl v [C], ?_⟩
  rw [removeBox_addBox]
  exact hΛ.erase hf (hf' ▸ hg)

/-- Where the target has no `X`, the premise of the rule on `X` embeds in
the target as it is. -/
theorem Inv.stepPrem (v : Inv) {Θ Θ' : NSeq} (hs : SubR v.R Θ Θ')
    (hf : v.X ∈ Θ.forms) (hg : v.X ∉ Θ'.forms) : SubR v.R (Θ.graft (v.prem Θ.forms)) Θ' :=
  hs.graft_map Stable.id fun _ hΛ hf' => hΛ.prem hf (hf' ▸ hg)

/-- A formula of the node other than `X` is in the node of the target. -/
theorem Inv.mem (v : Inv) {Θ Θ' : NSeq} (hs : SubR v.R Θ Θ') {Y : Form}
    (hf : Y ∈ Θ.forms) (hne : Y ≠ v.X) : Y ∈ Θ'.forms := by
  rcases hs.leaf with ⟨Λ, ⟨k, hc, _⟩, hf'⟩
  exact hf' ▸ hc.mem hf hne

/-- **Inversion, for several occurrences at once.**  If `Γ` embeds in
`Γ'` with some occurrences of `X` replaced by what the rule's premise has
for it, a proof of `Γ` gives a proof of `Γ'` of at most the same depth. -/
theorem Fam.invert (v : Inv) {Γ : NSeq} (d : Fam c Γ) :
    ∀ {Γ' : NSeq}, SubR v.R Γ Γ' → ∃ d' : Fam c Γ', d'.depth ≤ d.depth := by
  induction d with
  | @ax Γ Θ a p hΘ hp hn =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, _⟩
    exact ⟨.ax a' p hΘ' (v.mem hs hp (by cases v <;> simp [Inv.X]))
      (v.mem hs hn (by cases v <;> simp [Inv.X])), Nat.le_refl _⟩
  | @and Γ Θ a A B hΘ hA d₁ d₂ ih₁ ih₂ =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    by_cases hY : A ⋏ B ∈ Θ'.forms
    · rcases ih₁ (hset _ _ (v.step₁ hs hA hY A)) with ⟨e₁, h₁⟩
      rcases ih₂ (hset _ _ (v.step₁ hs hA hY B)) with ⟨e₂, h₂⟩
      refine ⟨.and a' A B hΘ' hY e₁ e₂, ?_⟩
      simp only [Fam.depth]
      omega
    · have hX : A ⋏ B = v.X := Decidable.byContradiction fun hne => hY (v.mem hs hA hne)
      cases v with
      | andL A' B' =>
        have eA : A = A' := by simp only [Inv.X] at hX; injection hX
        have eB : B = B' := by simp only [Inv.X] at hX; injection hX
        subst eA; subst eB
        have hp := (Inv.andL A B).stepPrem hs hA hY
        rw [show Θ.graft ((Inv.andL A B).prem Θ.forms) = (Θ.erase (A ⋏ B)).add A from
          (src_add_erase Θ (A ⋏ B) A).symm] at hp
        have hq := hset _ _ hp
        rw [setNode_self hΘ'] at hq
        rcases ih₁ hq with ⟨e, he⟩
        exact ⟨e, by simp only [Fam.depth]; omega⟩
      | andR A' B' =>
        have eA : A = A' := by simp only [Inv.X] at hX; injection hX
        have eB : B = B' := by simp only [Inv.X] at hX; injection hX
        subst eA; subst eB
        have hp := (Inv.andR A B).stepPrem hs hA hY
        rw [show Θ.graft ((Inv.andR A B).prem Θ.forms) = (Θ.erase (A ⋏ B)).add B from
          (src_add_erase Θ (A ⋏ B) B).symm] at hp
        have hq := hset _ _ hp
        rw [setNode_self hΘ'] at hq
        rcases ih₂ hq with ⟨e, he⟩
        exact ⟨e, by simp only [Fam.depth]; omega⟩
      | or A' B' => simp [Inv.X] at hX
      | box A' => simp [Inv.X] at hX
  | @or Γ Θ a A B hΘ hA d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    by_cases hY : A ⋎ B ∈ Θ'.forms
    · rcases ih (hset _ _ (v.stepAdd (v.step₁ hs hA hY B) A)) with ⟨e, he⟩
      exact ⟨.or a' A B hΘ' hY e, Nat.succ_le_succ he⟩
    · have hX : A ⋎ B = v.X := Decidable.byContradiction fun hne => hY (v.mem hs hA hne)
      cases v with
      | or A' B' =>
        have eA : A = A' := by simp only [Inv.X] at hX; injection hX
        have eB : B = B' := by simp only [Inv.X] at hX; injection hX
        subst eA; subst eB
        have hp := (Inv.or A B).stepPrem hs hA hY
        rw [show Θ.graft ((Inv.or A B).prem Θ.forms) = ((Θ.erase (A ⋎ B)).add B).add A from
          (src_add_add_erase Θ (A ⋎ B) A B).symm] at hp
        have hq := hset _ _ hp
        rw [setNode_self hΘ'] at hq
        rcases ih hq with ⟨e, he⟩
        exact ⟨e, by simp only [Fam.depth]; omega⟩
      | andL A' B' => simp [Inv.X] at hX
      | andR A' B' => simp [Inv.X] at hX
      | box A' => simp [Inv.X] at hX
  | @box Γ Θ a A hΘ hA d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    by_cases hY : □A ∈ Θ'.forms
    · rcases ih (hset _ _ (v.stepBox hs hA hY A)) with ⟨e, he⟩
      exact ⟨.box a' A hΘ' hY e, Nat.succ_le_succ he⟩
    · have hX : □A = v.X := Decidable.byContradiction fun hne => hY (v.mem hs hA hne)
      cases v with
      | box A' =>
        have eA : A = A' := by simp only [Inv.X] at hX; injection hX
        subst eA
        have hp := (Inv.box A).stepPrem hs hA hY
        rw [show Θ.graft ((Inv.box A).prem Θ.forms) = (Θ.erase (□A)).addBox (.leaf [A]) from
          (src_addBox_erase Θ (□A) (.leaf [A])).symm] at hp
        have hq := hset _ _ hp
        rw [setNode_self hΘ'] at hq
        rcases ih hq with ⟨e, he⟩
        exact ⟨e, by simp only [Fam.depth]; omega⟩
      | andL A' B' => simp [Inv.X] at hX
      | andR A' B' => simp [Inv.X] at hX
      | or A' B' => simp [Inv.X] at hX
  | @dia Γ Θ Δ a i A hΘ hA hΔ d ih =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases hs.box hΔ with ⟨i', Δ', hΔ', hsΔ, hsetΔ⟩
    rcases ih (hset _ _ (hsetΔ _ _ (v.stepAdd hsΔ A))) with ⟨e, he⟩
    have hm : ◇A ∈ Θ'.forms := v.mem hs hA (by cases v <;> simp [Inv.X])
    exact ⟨.dia a' i' A hΘ' hm hΔ' e, Nat.succ_le_succ he⟩
  | @cut Γ Θ a A hc hΘ d₁ d₂ ih₁ ih₂ =>
    intro Γ' h
    rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
    rcases ih₁ (hset _ _ (v.stepAdd hs A)) with ⟨e₁, h₁⟩
    rcases ih₂ (hset _ _ (v.stepAdd hs ∼A)) with ⟨e₂, h₂⟩
    refine ⟨.cut a' A hc hΘ' e₁ e₂, ?_⟩
    simp only [Fam.depth]
    omega

/-! ## The inverse rules (Lemma 2.4 (ii)) -/

/-- **`∧` is invertible, with the depth, on the left**: from a proof of
`Γ` with `A ∧ B` in the node at `a`, a proof of the left premise of the
rule `∧` there, of at most the same depth. -/
theorem inv_andL {Γ Θ : NSeq} {a : Path} {A B : Form} (hΘ : Γ.node? a = some Θ)
    (hA : A ⋏ B ∈ Θ.forms) (d : Fam c Γ) :
    ∃ d' : Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add A)), d'.depth ≤ d.depth := by
  refine d.invert (.andL A B) (SubR.setNode_right (Inv.R.refl _) hΘ ?_)
  rw [add_eq_withForms, erase_eq_withForms, forms_withForms, withForms_withForms]
  exact SubR.diag (Inv.R.refl _) (Stable.withForms fun gs => A :: gs.erase (A ⋏ B)) Θ
    ⟨1, Cnt.one hA (Inv.andL A B).X_not_mem_As, trivial⟩

/-- **`∧` is invertible, with the depth, on the right.** -/
theorem inv_andR {Γ Θ : NSeq} {a : Path} {A B : Form} (hΘ : Γ.node? a = some Θ)
    (hA : A ⋏ B ∈ Θ.forms) (d : Fam c Γ) :
    ∃ d' : Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add B)), d'.depth ≤ d.depth := by
  refine d.invert (.andR A B) (SubR.setNode_right (Inv.R.refl _) hΘ ?_)
  rw [add_eq_withForms, erase_eq_withForms, forms_withForms, withForms_withForms]
  exact SubR.diag (Inv.R.refl _) (Stable.withForms fun gs => B :: gs.erase (A ⋏ B)) Θ
    ⟨1, Cnt.one hA (Inv.andR A B).X_not_mem_As, trivial⟩

/-- **`∨` is invertible, with the depth.** -/
theorem inv_or {Γ Θ : NSeq} {a : Path} {A B : Form} (hΘ : Γ.node? a = some Θ)
    (hA : A ⋎ B ∈ Θ.forms) (d : Fam c Γ) :
    ∃ d' : Fam c (Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A)), d'.depth ≤ d.depth := by
  refine d.invert (.or A B) (SubR.setNode_right (Inv.R.refl _) hΘ ?_)
  rw [add_eq_withForms ((Θ.erase (A ⋎ B)).add B), add_eq_withForms (Θ.erase (A ⋎ B)),
    erase_eq_withForms]
  simp only [forms_withForms, withForms_withForms]
  exact SubR.diag (Inv.R.refl _) (Stable.withForms fun gs => A :: B :: gs.erase (A ⋎ B)) Θ
    ⟨1, Cnt.one hA (Inv.or A B).X_not_mem_As, trivial⟩

/-- **`□` is invertible, with the depth.** -/
theorem inv_box {Γ Θ : NSeq} {a : Path} {A : Form} (hΘ : Γ.node? a = some Θ)
    (hA : □A ∈ Θ.forms) (d : Fam c Γ) :
    ∃ d' : Fam c (Γ.setNode a ((Θ.erase (□A)).addBox (.leaf [A]))), d'.depth ≤ d.depth := by
  refine d.invert (.box A) (SubR.setNode_right (Inv.R.refl _) hΘ ?_)
  rw [erase_eq_withForms]
  exact SubR.diag (Inv.R.refl _)
    ((Stable.withForms fun gs => gs.erase (□A)).addBox (.leaf [A])) Θ
    ⟨1, Cnt.one hA (Inv.box A).X_not_mem_As, by simp [Inv.Extra, boxCount, addBox, withForms, forms]⟩

/-! ### The same, as the source writes them: for a context `Γ{ }` -/

/-- From `Γ{A ∧ B}`, `Γ{A}`. -/
theorem inv_andL_C (C : Ctx) (A B : Form) (d : Fam c (C.fill (.leaf [A ⋏ B]))) :
    ∃ d' : Fam c (C.fill (.leaf [A])), d'.depth ≤ d.depth := by
  have h := inv_andL (A := A) (B := B) (C.node?_fill _) (by simp) d
  have e : (C.fill (.leaf [A ⋏ B])).setNode C.path
      (((C.side.comma (.leaf [A ⋏ B])).erase (A ⋏ B)).add A) = C.fill (.leaf [A]) := by
    rw [Ctx.setNode_fill]; simp [Ctx.fill]
  rw [e] at h
  exact h

/-- From `Γ{A ∧ B}`, `Γ{B}`. -/
theorem inv_andR_C (C : Ctx) (A B : Form) (d : Fam c (C.fill (.leaf [A ⋏ B]))) :
    ∃ d' : Fam c (C.fill (.leaf [B])), d'.depth ≤ d.depth := by
  have h := inv_andR (A := A) (B := B) (C.node?_fill _) (by simp) d
  have e : (C.fill (.leaf [A ⋏ B])).setNode C.path
      (((C.side.comma (.leaf [A ⋏ B])).erase (A ⋏ B)).add B) = C.fill (.leaf [B]) := by
    rw [Ctx.setNode_fill]; simp [Ctx.fill]
  rw [e] at h
  exact h

/-- From `Γ{A ∨ B}`, `Γ{A, B}`. -/
theorem inv_or_C (C : Ctx) (A B : Form) (d : Fam c (C.fill (.leaf [A ⋎ B]))) :
    ∃ d' : Fam c (C.fill (.leaf [A, B])), d'.depth ≤ d.depth := by
  have h := inv_or (A := A) (B := B) (C.node?_fill _) (by simp) d
  have e : (C.fill (.leaf [A ⋎ B])).setNode C.path
      ((((C.side.comma (.leaf [A ⋎ B])).erase (A ⋎ B)).add B).add A) = C.fill (.leaf [A, B]) := by
    rw [Ctx.setNode_fill]; simp [Ctx.fill]
  rw [e] at h
  exact h

/-- From `Γ{□A}`, `Γ{[A]}`. -/
theorem inv_box_C (C : Ctx) (A : Form) (d : Fam c (C.fill (.leaf [□A]))) :
    ∃ d' : Fam c (C.fill (.cons (.leaf [A]) (.leaf []))), d'.depth ≤ d.depth := by
  have h := inv_box (A := A) (C.node?_fill _) (by simp) d
  have e : (C.fill (.leaf [□A])).setNode C.path
      (((C.side.comma (.leaf [□A])).erase (□A)).addBox (.leaf [A]))
        = C.fill (.cons (.leaf [A]) (.leaf [])) := by
    rw [Ctx.setNode_fill]; simp [Ctx.fill]
  rw [e] at h
  exact h

end

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
