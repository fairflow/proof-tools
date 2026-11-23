/-
Contraction is admissible, with the depth.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Lemma 2.4 (i)
(`l:stradm`), pp. 10–11; the rule `ctr` of Figure 2.4 (`fig:admissible`):
from `Γ{Δ, Δ}`, `Γ{Δ}`.  The source: "by induction on the depth of the
proof tree, using depth-preserving invertibility of the rules", with a
case analysis on where the contracted sequent lies.  Theory file: it ends
with its bound on axioms.

Here the induction is on a stronger statement, `Fam.hom`: if `Γ` maps
into `Γ'` (each formula of a node is in the node's image, and each box
of a node goes to some box of the image, two boxes possibly to the same
one), a proof of `Γ` gives a proof of `Γ'` of at most the same depth.
The case analysis of the source is then not needed.  For a rule on a
formula `X` at a node: the induction hypothesis gives the premise with
`X` kept; inverting that `X` and the hypothesis once more give the
premise the rule needs.
-/
import BrunnlerK.Invert

namespace BrunnlerK

namespace NSeq

/-! ## Mapping one sequent into another -/

/-- **`Γ` maps into `Γ'`**: every formula of `Γ` is a formula of `Γ'`, and
every box of `Γ` maps into some box of `Γ'`.  Two boxes may map into the
same one, and a formula that is in `Γ` twice need be in `Γ'` once only. -/
def Hom : NSeq → NSeq → Prop
  | leaf fs, Γ' => ∀ A, A ∈ fs → A ∈ Γ'.forms
  | cons Δ r, Γ' => (∃ Δ', Δ' ∈ Γ'.boxes ∧ Hom Δ Δ') ∧ Hom r Γ'

theorem hom_iff (Γ Γ' : NSeq) :
    Hom Γ Γ' ↔ (∀ A, A ∈ Γ.forms → A ∈ Γ'.forms)
      ∧ ∀ Δ, Δ ∈ Γ.boxes → ∃ Δ', Δ' ∈ Γ'.boxes ∧ Hom Δ Δ' := by
  induction Γ with
  | leaf fs =>
    simp only [Hom, forms, boxes]
    exact ⟨fun h => ⟨h, fun _ h' => nomatch h'⟩, fun h => h.1⟩
  | cons Δ r _ ih =>
    simp only [Hom, forms, boxes, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨hΔ, hf, hb⟩
      refine ⟨hf, fun Λ hΛ => ?_⟩
      rcases hΛ with rfl | hΛ
      · exact hΔ
      · exact hb Λ hΛ
    · rintro ⟨hf, hb⟩
      exact ⟨hb Δ (.inl rfl), hf, fun Λ hΛ => hb Λ (.inr hΛ)⟩

theorem Hom.forms {Γ Γ' : NSeq} (h : Hom Γ Γ') {A : Form} (hA : A ∈ Γ.forms) :
    A ∈ Γ'.forms :=
  ((hom_iff Γ Γ').mp h).1 A hA

theorem Hom.boxes {Γ Γ' : NSeq} (h : Hom Γ Γ') {Δ : NSeq} (hΔ : Δ ∈ Γ.boxes) :
    ∃ Δ', Δ' ∈ Γ'.boxes ∧ Hom Δ Δ' :=
  ((hom_iff Γ Γ').mp h).2 Δ hΔ

theorem Hom.trans : ∀ {Γ₁ Γ₂ Γ₃ : NSeq}, Hom Γ₁ Γ₂ → Hom Γ₂ Γ₃ → Hom Γ₁ Γ₃ := by
  intro Γ₁
  induction Γ₁ with
  | leaf fs => exact fun h₁ h₂ A hA => h₂.forms (h₁ A hA)
  | cons Δ r ihΔ ihr =>
    rintro Γ₂ Γ₃ ⟨⟨Δ', hΔ', hΔ⟩, hr⟩ h₂
    rcases h₂.boxes hΔ' with ⟨Δ'', hΔ'', h'⟩
    exact ⟨⟨Δ'', hΔ'', ihΔ hΔ h'⟩, ihr hr h₂⟩

/-- The target may grow. -/
theorem Hom.weaken : ∀ {Γ Γ' Γ'' : NSeq}, Hom Γ Γ' →
    (∀ A, A ∈ Γ'.forms → A ∈ Γ''.forms) → (∀ Δ, Δ ∈ Γ'.boxes → Δ ∈ Γ''.boxes) →
    Hom Γ Γ'' := by
  intro Γ
  induction Γ with
  | leaf fs => exact fun h hf _ A hA => hf A (h A hA)
  | cons Δ r _ ihr =>
    rintro Γ' Γ'' ⟨⟨Δ', hΔ', hΔ⟩, hr⟩ hf hb
    exact ⟨⟨Δ', hb Δ' hΔ', hΔ⟩, ihr hr hf hb⟩

theorem Hom.refl : ∀ Γ : NSeq, Hom Γ Γ := by
  intro Γ
  induction Γ with
  | leaf fs => exact fun _ h => h
  | cons Δ r ihΔ ihr =>
    exact ⟨⟨Δ, .head _, ihΔ⟩, ihr.weaken (fun _ h => h) (fun _ h => .tail _ h)⟩

/-- A sequent maps into one that has its formulas and its boxes. -/
theorem Hom.of_subset {P Q : NSeq} (hf : ∀ A, A ∈ P.forms → A ∈ Q.forms)
    (hb : ∀ Δ, Δ ∈ P.boxes → Δ ∈ Q.boxes) : Hom P Q :=
  (Hom.refl P).weaken hf hb

/-- From `Θ` into `Θ'`, to `P` into `Q`: the formulas of `P` are in `Q`;
each box of `P` is a box of `Θ` or of `Q`; the boxes of `Θ'` are in `Q`. -/
theorem Hom.of_parts {Θ Θ' P Q : NSeq} (hs : Hom Θ Θ')
    (hf : ∀ A, A ∈ P.forms → A ∈ Q.forms)
    (hb : ∀ Λ, Λ ∈ P.boxes → Λ ∈ Θ.boxes ∨ Λ ∈ Q.boxes)
    (hq : ∀ Λ, Λ ∈ Θ'.boxes → Λ ∈ Q.boxes) : Hom P Q := by
  refine (hom_iff P Q).mpr ⟨hf, fun Λ hΛ => ?_⟩
  rcases hb Λ hΛ with h | h
  · rcases hs.boxes h with ⟨Λ', hΛ', hh⟩
    exact ⟨Λ', hq Λ' hΛ', hh⟩
  · exact ⟨Λ, h, Hom.refl Λ⟩

/-! ## Boxes that are replaced -/

theorem mem_setBox_cases {Γ Y Λ : NSeq} {j : Nat} (h : Λ ∈ (Γ.setBox j Y).boxes) :
    Λ = Y ∨ Λ ∈ Γ.boxes := by
  induction Γ generalizing j with
  | leaf fs => cases h
  | cons Δ r _ ih =>
    cases j with
    | zero =>
      rcases List.mem_cons.mp h with h | h
      · exact .inl h
      · exact .inr (.tail _ h)
    | succ j =>
      rcases List.mem_cons.mp h with h | h
      · exact .inr (h ▸ .head _)
      · rcases ih h with h | h
        · exact .inl h
        · exact .inr (.tail _ h)

theorem mem_setBox_or {Γ Δ Λ : NSeq} {j : Nat} (Y : NSeq) (h : Λ ∈ Γ.boxes)
    (hb : Γ.box? j = some Δ) : Λ ∈ (Γ.setBox j Y).boxes ∨ Λ = Δ := by
  induction Γ generalizing j with
  | leaf fs => cases h
  | cons Δ₀ r _ ih =>
    cases j with
    | zero =>
      have e : Δ₀ = Δ := by simpa [box?] using hb
      rcases List.mem_cons.mp h with h | h
      · exact .inr (h.trans e)
      · exact .inl (.tail _ h)
    | succ j =>
      rcases List.mem_cons.mp h with h | h
      · exact .inl (h ▸ .head _)
      · rcases ih h (by simpa [box?] using hb) with h | h
        · exact .inl (.tail _ h)
        · exact .inr h

theorem mem_setBox_congr {Γ Y Λ : NSeq} {j : Nat} (Y' : NSeq)
    (h : Λ ∈ (Γ.setBox j Y).boxes) :
    (Λ = Y ∧ Y' ∈ (Γ.setBox j Y').boxes) ∨ Λ ∈ (Γ.setBox j Y').boxes := by
  induction Γ generalizing j with
  | leaf fs => cases h
  | cons Δ r _ ih =>
    cases j with
    | zero =>
      rcases List.mem_cons.mp h with h | h
      · exact .inl ⟨h, .head _⟩
      · exact .inr (.tail _ h)
    | succ j =>
      rcases List.mem_cons.mp h with h | h
      · exact .inr (h ▸ .head _)
      · rcases ih h with ⟨h₁, h₂⟩ | h
        · exact .inl ⟨h₁, .tail _ h₂⟩
        · exact .inr (.tail _ h)

/-- A box replaced by one it maps into. -/
theorem Hom.setBox_ext {Γ Δ Y : NSeq} {j : Nat} (hb : Γ.box? j = some Δ) (h : Hom Δ Y) :
    Hom Γ (Γ.setBox j Y) := by
  refine (hom_iff _ _).mpr ⟨fun A hA => by simpa using hA, fun Λ hΛ => ?_⟩
  rcases mem_setBox_or Y hΛ hb with h' | h'
  · exact ⟨Λ, h', Hom.refl Λ⟩
  · exact ⟨Y, mem_boxes_of_box? (box?_setBox_self Y hb), h' ▸ h⟩

/-- A node replaced by one it maps into. -/
theorem Hom.setNode_ext {Γ Θ X : NSeq} {a : Path} (ha : Γ.node? a = some Θ) (h : Hom Θ X) :
    Hom Γ (Γ.setNode a X) := by
  induction a generalizing Γ with
  | nil =>
    have e : Γ = Θ := by simpa [node?] using ha
    subst e
    exact h
  | cons j a ih =>
    simp only [node?] at ha
    cases hb : Γ.box? j with
    | none => simp [hb] at ha
    | some Δ =>
      simp only [hb] at ha
      simp only [setNode, hb]
      exact Hom.setBox_ext hb (ih ha)

theorem Hom.setBox_congr (Γ : NSeq) (j : Nat) {Y Y' : NSeq} (h : Hom Y Y') :
    Hom (Γ.setBox j Y) (Γ.setBox j Y') := by
  refine (hom_iff _ _).mpr ⟨fun A hA => by simpa using hA, fun Λ hΛ => ?_⟩
  rcases mem_setBox_congr Y' hΛ with ⟨h₁, h₂⟩ | h'
  · exact ⟨Y', h₂, h₁ ▸ h⟩
  · exact ⟨Λ, h', Hom.refl Λ⟩

/-- The node at a path replaced, in the same sequent, by `X` and by `X'`. -/
theorem Hom.setNode_congr (Γ : NSeq) (a : Path) {X X' : NSeq} (h : Hom X X') :
    Hom (Γ.setNode a X) (Γ.setNode a X') := by
  induction a generalizing Γ with
  | nil => exact h
  | cons j a ih =>
    simp only [setNode]
    cases hb : Γ.box? j with
    | none => exact Hom.refl Γ
    | some Δ => exact Hom.setBox_congr Γ j (ih Δ)

/-- A box of `Γ` maps into a box of `Γ'`; and both may be replaced, the
second by one it maps into. -/
theorem Hom.box {Γ Γ' Δ : NSeq} {j : Nat} (h : Hom Γ Γ') (hj : Γ.box? j = some Δ) :
    ∃ j' Δ', Γ'.box? j' = some Δ' ∧ Hom Δ Δ' ∧
      ∀ Y Y', Hom Y Y' → Hom Δ' Y' → Hom (Γ.setBox j Y) (Γ'.setBox j' Y') := by
  rcases h.boxes (mem_boxes_of_box? hj) with ⟨Δ', hΔ', hΔ⟩
  have hb' := box?_boxIdx hΔ'
  refine ⟨Γ'.boxIdx Δ', Δ', hb', hΔ, fun Y Y' hY hext => ?_⟩
  refine (hom_iff _ _).mpr ⟨fun A hA => ?_, fun Λ hΛ => ?_⟩
  · rw [forms_setBox] at hA ⊢
    exact h.forms hA
  · have hY' : Y' ∈ (Γ'.setBox (Γ'.boxIdx Δ') Y').boxes :=
      mem_boxes_of_box? (box?_setBox_self Y' hb')
    rcases mem_setBox_cases hΛ with e | hΛ
    · exact ⟨Y', hY', e ▸ hY⟩
    · rcases h.boxes hΛ with ⟨Λ', hΛ', hh⟩
      rcases mem_setBox_or Y' hΛ' hb' with h' | h'
      · exact ⟨Λ', h', hh⟩
      · exact ⟨Y', hY', hh.trans (h' ▸ hext)⟩

/-- The node at a path of `Γ` maps into a node of `Γ'`; and both may be
replaced, the second by one it maps into. -/
theorem Hom.node {Γ Γ' Θ : NSeq} {a : Path} (h : Hom Γ Γ') (ha : Γ.node? a = some Θ) :
    ∃ a' Θ', Γ'.node? a' = some Θ' ∧ Hom Θ Θ' ∧
      ∀ X X', Hom X X' → Hom Θ' X' → Hom (Γ.setNode a X) (Γ'.setNode a' X') := by
  induction a generalizing Γ Γ' with
  | nil =>
    have e : Γ = Θ := by simpa [node?] using ha
    subst e
    exact ⟨[], Γ', rfl, h, fun X X' hX _ => hX⟩
  | cons j a ih =>
    simp only [node?] at ha
    cases hb : Γ.box? j with
    | none => simp [hb] at ha
    | some Δ =>
      simp only [hb] at ha
      rcases h.box hb with ⟨j', Δ', hb', hΔ, hset⟩
      rcases ih hΔ ha with ⟨a', Θ', hn, hΘ, hset'⟩
      refine ⟨j' :: a', Θ', by simp [node?, hb', hn], hΘ, fun X X' hX hext => ?_⟩
      simp only [setNode, hb, hb']
      exact hset _ _ (hset' X X' hX hext) (Hom.setNode_ext hn hext)

theorem mem_erase_cons {A B X : Form} {l : List Form} (h : B ∈ (A :: l).erase X) :
    B = A ∨ B ∈ l.erase X := by
  by_cases e : A = X
  · subst e
    rw [List.erase_cons_head] at h
    by_cases e' : B = A
    · exact .inl e'
    · exact .inr (mem_erase_of_ne e' h)
  · simp only [List.erase_cons, beq_iff_eq, e, if_false] at h
    rcases List.mem_cons.mp h with h | h
    · exact .inl h
    · exact .inr h

end NSeq

/-! ## The theorem -/

open NSeq in
/-- **If `Γ` maps into `Γ'`, a proof of `Γ` gives a proof of `Γ'` of at
most the same depth.**  By induction on a bound of the depth. -/
theorem Fam.hom_aux {c : Bool} : ∀ (n : Nat) {Γ : NSeq} (d : Fam c Γ), d.depth < n →
    ∀ {Γ' : NSeq}, Hom Γ Γ' → ∃ d' : Fam c Γ', d'.depth ≤ d.depth := by
  intro n
  induction n with
  | zero => exact fun d hd => absurd hd (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ d hd Γ' h
    cases d with
    | @ax _ Θ a p hΘ hp hn =>
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, _⟩
      exact ⟨.ax a' p hΘ' (hs.forms hp) (hs.forms hn), Nat.le_refl _⟩
    | @and _ Θ a A B hΘ hA d₁ d₂ =>
      simp only [Fam.depth] at hd
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
      have hX : A ⋏ B ∈ Θ'.forms := hs.forms hA
      -- the premises, with `A ∧ B` kept
      have key : ∀ C, Hom ((Θ.erase (A ⋏ B)).add C) (Θ'.add C) := fun C =>
        Hom.of_parts hs
          (fun D hD => by
            simp only [forms_add, forms_erase, List.mem_cons] at hD ⊢
            rcases hD with hD | hD
            · exact .inl hD
            · exact .inr (hs.forms (List.mem_of_mem_erase hD)))
          (fun Λ hΛ => .inl (by simpa using hΛ)) (fun Λ hΛ => by simpa using hΛ)
      have ext : ∀ C, Hom Θ' (Θ'.add C) := fun C =>
        Hom.of_subset (fun D hD => by simp [hD]) (fun Λ hΛ => by simpa using hΛ)
      -- then `A ∧ B` inverted, and the two copies of the premise's formula made one
      have con : ∀ C, Hom (((Θ'.add C).erase (A ⋏ B)).add C) ((Θ'.erase (A ⋏ B)).add C) :=
        fun C => Hom.of_subset
          (fun D hD => by
            simp only [forms_add, forms_erase, List.mem_cons] at hD ⊢
            rcases hD with hD | hD
            · exact .inl hD
            · exact mem_erase_cons hD)
          (fun Λ hΛ => by simpa using hΛ)
      rcases ih d₁ (by omega) (hset _ _ (key A) (ext A)) with ⟨e₁, he₁⟩
      have i₁ := inv_andL (A := A) (B := B) (node?_setNode _ hΘ') (by simp [hX]) e₁
      rw [setNode_setNode _ _ hΘ'] at i₁
      rcases i₁ with ⟨f₁, hf₁⟩
      rcases ih f₁ (by omega) (Hom.setNode_congr Γ' a' (con A)) with ⟨g₁, hg₁⟩
      rcases ih d₂ (by omega) (hset _ _ (key B) (ext B)) with ⟨e₂, he₂⟩
      have i₂ := inv_andR (A := A) (B := B) (node?_setNode _ hΘ') (by simp [hX]) e₂
      rw [setNode_setNode _ _ hΘ'] at i₂
      rcases i₂ with ⟨f₂, hf₂⟩
      rcases ih f₂ (by omega) (Hom.setNode_congr Γ' a' (con B)) with ⟨g₂, hg₂⟩
      refine ⟨.and a' A B hΘ' hX g₁ g₂, ?_⟩
      simp only [Fam.depth]
      omega
    | @or _ Θ a A B hΘ hA d₁ =>
      simp only [Fam.depth] at hd
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
      have hX : A ⋎ B ∈ Θ'.forms := hs.forms hA
      have key : Hom (((Θ.erase (A ⋎ B)).add B).add A) ((Θ'.add B).add A) :=
        Hom.of_parts hs
          (fun D hD => by
            simp only [forms_add, forms_erase, List.mem_cons] at hD ⊢
            rcases hD with hD | hD | hD
            · exact .inl hD
            · exact .inr (.inl hD)
            · exact .inr (.inr (hs.forms (List.mem_of_mem_erase hD))))
          (fun Λ hΛ => .inl (by simpa using hΛ)) (fun Λ hΛ => by simpa using hΛ)
      have ext : Hom Θ' ((Θ'.add B).add A) :=
        Hom.of_subset (fun D hD => by simp [hD]) (fun Λ hΛ => by simpa using hΛ)
      have con : Hom (((((Θ'.add B).add A).erase (A ⋎ B)).add B).add A)
          (((Θ'.erase (A ⋎ B)).add B).add A) :=
        Hom.of_subset
          (fun D hD => by
            simp only [forms_add, forms_erase, List.mem_cons] at hD ⊢
            rcases hD with hD | hD | hD
            · exact .inl hD
            · exact .inr (.inl hD)
            · rcases mem_erase_cons hD with hD | hD
              · exact .inl hD
              · rcases mem_erase_cons hD with hD | hD
                · exact .inr (.inl hD)
                · exact .inr (.inr hD))
          (fun Λ hΛ => by simpa using hΛ)
      rcases ih d₁ (by omega) (hset _ _ key ext) with ⟨e, he⟩
      have i₁ := inv_or (A := A) (B := B) (node?_setNode _ hΘ') (by simp [hX]) e
      rw [setNode_setNode _ _ hΘ'] at i₁
      rcases i₁ with ⟨f, hf⟩
      rcases ih f (by omega) (Hom.setNode_congr Γ' a' con) with ⟨g, hg⟩
      refine ⟨.or a' A B hΘ' hX g, ?_⟩
      simp only [Fam.depth]
      omega
    | @box _ Θ a A hΘ hA d₁ =>
      simp only [Fam.depth] at hd
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
      have hX : □A ∈ Θ'.forms := hs.forms hA
      have key : Hom ((Θ.erase (□A)).addBox (.leaf [A])) (Θ'.addBox (.leaf [A])) :=
        Hom.of_parts hs
          (fun D hD => by
            simp only [forms_addBox, forms_erase] at hD ⊢
            exact hs.forms (List.mem_of_mem_erase hD))
          (fun Λ hΛ => by
            simp only [boxes_addBox, boxes_erase, List.mem_append, List.mem_singleton] at hΛ ⊢
            rcases hΛ with hΛ | hΛ
            · exact .inl hΛ
            · exact .inr (.inr hΛ))
          (fun Λ hΛ => by simp [hΛ])
      have ext : Hom Θ' (Θ'.addBox (.leaf [A])) :=
        Hom.of_subset (fun D hD => by simpa using hD) (fun Λ hΛ => by simp [hΛ])
      have con : Hom (((Θ'.addBox (.leaf [A])).erase (□A)).addBox (.leaf [A]))
          ((Θ'.erase (□A)).addBox (.leaf [A])) :=
        Hom.of_subset (fun D hD => by simpa using hD)
          (fun Λ hΛ => by
            simp only [boxes_addBox, boxes_erase, List.mem_append, List.mem_singleton] at hΛ ⊢
            rcases hΛ with (hΛ | hΛ) | hΛ
            · exact .inl hΛ
            · exact .inr hΛ
            · exact .inr hΛ)
      rcases ih d₁ (by omega) (hset _ _ key ext) with ⟨e, he⟩
      have i₁ := inv_box (A := A) (node?_setNode _ hΘ') (by simp [hX]) e
      rw [setNode_setNode _ _ hΘ'] at i₁
      rcases i₁ with ⟨f, hf⟩
      rcases ih f (by omega) (Hom.setNode_congr Γ' a' con) with ⟨g, hg⟩
      refine ⟨.box a' A hΘ' hX g, ?_⟩
      simp only [Fam.depth]
      omega
    | @dia _ Θ Δ a i A hΘ hA hΔ d₁ =>
      simp only [Fam.depth] at hd
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
      rcases hs.box hΔ with ⟨i', Δ', hΔ', hsΔ, hsetΔ⟩
      have ext : Hom Δ' (Δ'.add A) :=
        Hom.of_subset (fun D hD => by simp [hD]) (fun Λ hΛ => by simpa using hΛ)
      have key : Hom (Δ.add A) (Δ'.add A) :=
        Hom.of_parts hsΔ
          (fun D hD => by
            simp only [forms_add, List.mem_cons] at hD ⊢
            rcases hD with hD | hD
            · exact .inl hD
            · exact .inr (hsΔ.forms hD))
          (fun Λ hΛ => .inl (by simpa using hΛ)) (fun Λ hΛ => by simpa using hΛ)
      rcases ih d₁ (by omega) (hset _ _ (hsetΔ _ _ key ext) (Hom.setBox_ext hΔ' ext))
        with ⟨e, he⟩
      refine ⟨.dia a' i' A hΘ' (hs.forms hA) hΔ' e, ?_⟩
      simp only [Fam.depth]
      omega
    | @cut _ Θ a A hc hΘ d₁ d₂ =>
      simp only [Fam.depth] at hd
      rcases h.node hΘ with ⟨a', Θ', hΘ', hs, hset⟩
      have key : ∀ C, Hom (Θ.add C) (Θ'.add C) := fun C =>
        Hom.of_parts hs
          (fun D hD => by
            simp only [forms_add, List.mem_cons] at hD ⊢
            rcases hD with hD | hD
            · exact .inl hD
            · exact .inr (hs.forms hD))
          (fun Λ hΛ => .inl (by simpa using hΛ)) (fun Λ hΛ => by simpa using hΛ)
      have ext : ∀ C, Hom Θ' (Θ'.add C) := fun C =>
        Hom.of_subset (fun D hD => by simp [hD]) (fun Λ hΛ => by simpa using hΛ)
      rcases ih d₁ (by omega) (hset _ _ (key A) (ext A)) with ⟨e₁, he₁⟩
      rcases ih d₂ (by omega) (hset _ _ (key ∼A) (ext ∼A)) with ⟨e₂, he₂⟩
      refine ⟨.cut a' A hc hΘ' e₁ e₂, ?_⟩
      simp only [Fam.depth]
      omega

/-- **If `Γ` maps into `Γ'`, a proof of `Γ` gives a proof of `Γ'` of at
most the same depth.**  In K, and in K with cut. -/
theorem Fam.hom {c : Bool} {Γ Γ' : NSeq} (d : Fam c Γ) (h : NSeq.Hom Γ Γ') :
    ∃ d' : Fam c Γ', d'.depth ≤ d.depth :=
  Fam.hom_aux (d.depth + 1) d (Nat.lt_succ_self _) h

/-! ## Contraction (Lemma 2.4 (i), Figure 2.4) -/

/-- **`ctr` is admissible, with the depth**: from a proof of `Γ{Δ, Δ}`, a
proof of `Γ{Δ}` of at most the same depth. -/
theorem ctr {c : Bool} (C : Ctx) (Δ : NSeq) (d : Fam c (C.fill (Δ.comma Δ))) :
    ∃ d' : Fam c (C.fill Δ), d'.depth ≤ d.depth := by
  refine d.hom (NSeq.Hom.setNode_congr C.seq C.path (NSeq.Hom.of_subset ?_ ?_))
  · intro A hA
    simp only [NSeq.forms_comma, List.mem_append] at hA ⊢
    rcases hA with (hA | hA) | hA
    · exact .inl hA
    · exact .inl hA
    · exact .inr hA
  · intro Λ hΛ
    simp only [NSeq.boxes_comma, List.mem_append] at hΛ ⊢
    rcases hΛ with hΛ | hΛ | hΛ
    · exact .inl hΛ
    · exact .inr hΛ
    · exact .inr hΛ

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
