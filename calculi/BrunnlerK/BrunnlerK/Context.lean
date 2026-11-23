/-
Lemmas about the functions on nested sequents, and the lemma that carries
a proof of a subtree into its context.

Source: none.  These rest on the families of `BrunnlerK/System.lean` only.
Theory file: it ends with its bound on axioms.
-/
import BrunnlerK.System

namespace BrunnlerK

namespace NSeq

/-! ## The formulas and the boxes of a changed sequent -/

@[simp] theorem forms_add (Γ : NSeq) (A : Form) : (Γ.add A).forms = A :: Γ.forms := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [add, forms] using ih

@[simp] theorem boxes_add (Γ : NSeq) (A : Form) : (Γ.add A).boxes = Γ.boxes := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [add, boxes] using ih

@[simp] theorem forms_erase (Γ : NSeq) (A : Form) :
    (Γ.erase A).forms = Γ.forms.erase A := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [erase, forms] using ih

@[simp] theorem boxes_erase (Γ : NSeq) (A : Form) : (Γ.erase A).boxes = Γ.boxes := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [erase, boxes] using ih

@[simp] theorem forms_addBox (Γ Λ : NSeq) : (Γ.addBox Λ).forms = Γ.forms := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [addBox, forms] using ih

@[simp] theorem boxes_addBox (Γ Λ : NSeq) : (Γ.addBox Λ).boxes = Γ.boxes ++ [Λ] := by
  induction Γ with
  | leaf fs => rfl
  | cons Δ r _ ih => simpa [addBox, boxes] using ih

@[simp] theorem forms_setBox (Γ : NSeq) (i : Nat) (Λ : NSeq) :
    (Γ.setBox i Λ).forms = Γ.forms := by
  induction Γ generalizing i with
  | leaf fs => rfl
  | cons Δ r _ ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [setBox, forms] using ih i

/-- The box at position `i`, where there is one, after it is replaced. -/
theorem box?_setBox_self {Γ Δ : NSeq} {i : Nat} (Λ : NSeq) (h : Γ.box? i = some Δ) :
    (Γ.setBox i Λ).box? i = some Λ := by
  induction Γ generalizing i with
  | leaf fs => cases h
  | cons Δ' r _ ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa [box?] using h)

/-- Replacing a box twice is replacing it once. -/
theorem setBox_setBox (Γ : NSeq) (i : Nat) (Λ Λ' : NSeq) :
    (Γ.setBox i Λ).setBox i Λ' = Γ.setBox i Λ' := by
  induction Γ generalizing i with
  | leaf fs => rfl
  | cons Δ r _ ih =>
    cases i with
    | zero => rfl
    | succ i => simp [setBox, ih]

/-- Replacing a box by itself changes nothing. -/
theorem setBox_self {Γ Δ : NSeq} {i : Nat} (h : Γ.box? i = some Δ) :
    Γ.setBox i Δ = Γ := by
  induction Γ generalizing i with
  | leaf fs => rfl
  | cons Δ' r _ ih =>
    cases i with
    | zero =>
      have : Δ' = Δ := by simpa [box?] using h
      simp [setBox, this]
    | succ i =>
      have := ih (i := i) (by simpa [box?] using h)
      simp [setBox, this]

/-- A box at a position is one of the boxes. -/
theorem mem_boxes_of_box? {Γ Δ : NSeq} {i : Nat} (h : Γ.box? i = some Δ) :
    Δ ∈ Γ.boxes := by
  induction Γ generalizing i with
  | leaf fs => cases h
  | cons Δ' r _ ih =>
    cases i with
    | zero =>
      have : Δ' = Δ := by simpa [box?] using h
      simp [boxes, this]
    | succ i => exact List.mem_cons_of_mem _ (ih (by simpa [box?] using h))

/-- A position of a box that is one of the boxes: the first. -/
def boxIdx : NSeq → NSeq → Nat
  | leaf _, _ => 0
  | cons Δ r, Δ' => if Δ = Δ' then 0 else r.boxIdx Δ' + 1

theorem box?_boxIdx {Γ Δ : NSeq} (h : Δ ∈ Γ.boxes) : Γ.box? (Γ.boxIdx Δ) = some Δ := by
  induction Γ with
  | leaf fs => cases h
  | cons Δ' r _ ih =>
    by_cases e : Δ' = Δ
    · simp [boxIdx, e, box?]
    · have h' : Δ ∈ r.boxes := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      simpa [boxIdx, e, box?] using ih h'

/-! ## Paths -/

/-- The node at a path that goes on: first to `a`, then from there. -/
theorem node?_append {Γ Θ : NSeq} {a : Path} (b : Path) (h : Γ.node? a = some Θ) :
    Γ.node? (a ++ b) = Θ.node? b := by
  induction a generalizing Γ with
  | nil =>
    have : Γ = Θ := by simpa [node?] using h
    simp [this]
  | cons i a ih =>
    simp only [node?, List.cons_append] at h ⊢
    cases hb : Γ.box? i with
    | none => simp [hb] at h
    | some Δ =>
      simp only [hb] at h ⊢
      exact ih h

/-- After the node at `a ++ b` is replaced, the node at `a` is the old one
with its node at `b` replaced. -/
theorem node?_setNode_append {Γ Θ : NSeq} {a : Path} (b : Path) (X : NSeq)
    (h : Γ.node? a = some Θ) :
    (Γ.setNode (a ++ b) X).node? a = some (Θ.setNode b X) := by
  induction a generalizing Γ with
  | nil =>
    have : Γ = Θ := by simpa [node?] using h
    simp [this, node?]
  | cons i a ih =>
    simp only [node?, setNode, List.cons_append] at h ⊢
    cases hb : Γ.box? i with
    | none => simp [hb] at h
    | some Δ =>
      simp only [hb] at h ⊢
      rw [box?_setBox_self _ hb]
      exact ih h

end NSeq

/-! ## A proof of a subtree is a proof of the whole

Every rule acts at any depth, so a proof of the sequent at a path of `Γ`,
taken alone, is a proof of `Γ`: each of its rule instances at a path `b`
is the same instance at `a ++ b`.  With the root's `◇k_c` this is what
the source gets from the rules `nec` and `wk`. -/

/-- If `Θ` is the sequent at the path `a` of `Γ`, a proof of `Θ` gives a
proof of `Γ`. -/
def Fam.lift {c : Bool} : {Θ : NSeq} → Fam c Θ →
    {Γ : NSeq} → (a : Path) → Γ.node? a = some Θ → Fam c Γ
  | _, .ax b p hΘ hp hn, _, a, h =>
    .ax (a ++ b) p ((NSeq.node?_append b h).trans hΘ) hp hn
  | _, .and b A B hΘ hA d₁ d₂, _, a, h =>
    .and (a ++ b) A B ((NSeq.node?_append b h).trans hΘ) hA
      (d₁.lift a (NSeq.node?_setNode_append b _ h))
      (d₂.lift a (NSeq.node?_setNode_append b _ h))
  | _, .or b A B hΘ hA d, _, a, h =>
    .or (a ++ b) A B ((NSeq.node?_append b h).trans hΘ) hA
      (d.lift a (NSeq.node?_setNode_append b _ h))
  | _, .box b A hΘ hA d, _, a, h =>
    .box (a ++ b) A ((NSeq.node?_append b h).trans hΘ) hA
      (d.lift a (NSeq.node?_setNode_append b _ h))
  | _, .dia b i A hΘ hA hΔ d, _, a, h =>
    .dia (a ++ b) i A ((NSeq.node?_append b h).trans hΘ) hA hΔ
      (d.lift a (NSeq.node?_setNode_append b _ h))
  | _, .cut b A hc hΘ d₁ d₂, _, a, h =>
    .cut (a ++ b) A hc ((NSeq.node?_append b h).trans hΘ)
      (d₁.lift a (NSeq.node?_setNode_append b _ h))
      (d₂.lift a (NSeq.node?_setNode_append b _ h))

/-- `◇k_c` for each formula of a list: from a proof of `Γ` with all of
`B₁, …, Bₖ` put into the box at position `i`, where each `◇Bⱼ` is in `Γ`,
a proof of `Γ`. -/
def Fam.diaAll {c : Bool} : (Bs : List Form) → {Γ Δ : NSeq} → (i : Nat) →
    (∀ B, B ∈ Bs → ◇B ∈ Γ.forms) → Γ.box? i = some Δ →
    Fam c (Γ.setBox i (Bs.foldl NSeq.add Δ)) → Fam c Γ
  | [], _, _, _, _, hΔ, d => NSeq.setBox_self hΔ ▸ d
  | B :: Bs, Γ, Δ, i, hB, hΔ, d =>
    .dia [] i B rfl (hB B (List.mem_cons_self ..)) hΔ <|
      Fam.diaAll Bs (Γ := Γ.setBox i (Δ.add B)) (Δ := Δ.add B) i
        (fun B' h => by
          rw [NSeq.forms_setBox]
          exact hB B' (List.mem_cons_of_mem _ h))
        (NSeq.box?_setBox_self _ hΔ)
        (by rw [NSeq.setBox_setBox]; exact d)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
