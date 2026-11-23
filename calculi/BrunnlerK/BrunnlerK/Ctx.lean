/-
Sequent contexts, and the rules of Figures 2.3 and 2.4 in the figure's
own shape, as derived rules.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, §2.1.1,
"Sequent contexts, unary", pp. 7–8; Figure 2.3 (`fig:kx`) and Figure 2.4
(`fig:admissible`), p. 10.  Theory file: it ends with its bound on
axioms.

The family `Fam` states each rule for a variable conclusion, a path and
the whole node at that path (`campaign/rule-table.md`, D2).  Here the
same rules are stated as the figure prints them, `Γ{A}  Γ{B} / Γ{A ∧ B}`,
for a context `Γ{ }` and what fills its hole.  Each is derived from the
constructor of `Fam` for that rule.
-/
import BrunnlerK.Context

namespace BrunnlerK

namespace NSeq

/-! ## The comma -/

/-- A sequent with more formulas put after its own. -/
def appendForms : NSeq → List Form → NSeq
  | leaf gs, fs => leaf (gs ++ fs)
  | cons Δ r, fs => cons Δ (r.appendForms fs)

/-- **The comma**: `Θ.comma Δ` is the sequent `Θ, Δ`, "the comma in the
expression `Γ, Δ` is multiset union" (p. 7).  As lists: the formulas of
`Δ` are put in front of those of `Θ`, and the boxes of `Δ` after those of
`Θ`, as `add` and `addBox` put one formula and one box. -/
def comma : NSeq → NSeq → NSeq
  | leaf fs, Δ => Δ.appendForms fs
  | cons Λ r, Δ => cons Λ (r.comma Δ)

@[simp] theorem forms_appendForms (Γ : NSeq) (fs : List Form) :
    (Γ.appendForms fs).forms = Γ.forms ++ fs := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simpa [appendForms, forms] using ih

@[simp] theorem boxes_appendForms (Γ : NSeq) (fs : List Form) :
    (Γ.appendForms fs).boxes = Γ.boxes := by
  induction Γ with
  | leaf gs => rfl
  | cons Δ r _ ih => simpa [appendForms, boxes] using ih

/-- The formulas of `Θ, Δ`: those of `Δ`, then those of `Θ`. -/
@[simp] theorem forms_comma (Θ Δ : NSeq) : (Θ.comma Δ).forms = Δ.forms ++ Θ.forms := by
  induction Θ with
  | leaf fs => simp [comma, forms]
  | cons Λ r _ ih => simpa [comma, forms] using ih

/-- The boxes of `Θ, Δ`: those of `Θ`, then those of `Δ`. -/
@[simp] theorem boxes_comma (Θ Δ : NSeq) : (Θ.comma Δ).boxes = Θ.boxes ++ Δ.boxes := by
  induction Θ with
  | leaf fs => simp [comma, boxes]
  | cons Λ r _ ih => simpa [comma, boxes] using ih

/-- `Θ, ∅` is `Θ`. -/
@[simp] theorem comma_empty (Θ : NSeq) : Θ.comma (leaf []) = Θ := by
  induction Θ with
  | leaf fs => simp [comma, appendForms]
  | cons Λ r _ ih => simp [comma, ih]

/-- `Θ, (A, Δ)` is `(Θ, Δ), A`. -/
theorem comma_add (Θ Δ : NSeq) (A : Form) : Θ.comma (Δ.add A) = (Θ.comma Δ).add A := by
  induction Θ with
  | leaf fs =>
    simp only [comma]
    induction Δ with
    | leaf gs => rfl
    | cons Λ r _ ih => simp [add, appendForms, ih]
  | cons Λ r _ ih => simp [comma, add, ih]

/-- `Θ, A` is `Θ.add A`. -/
@[simp] theorem comma_single (Θ : NSeq) (A : Form) : Θ.comma (leaf [A]) = Θ.add A := by
  have := comma_add Θ (leaf []) A
  simpa [add] using this

/-- `Θ, A, B` is `(Θ.add B).add A`. -/
@[simp] theorem comma_pair (Θ : NSeq) (A B : Form) :
    Θ.comma (leaf [A, B]) = (Θ.add B).add A := by
  have := comma_add Θ (leaf [B]) A
  simpa [add] using this

/-- `Θ, [Λ]` is `Θ.addBox Λ`. -/
@[simp] theorem comma_box (Θ Λ : NSeq) : Θ.comma (cons Λ (leaf [])) = Θ.addBox Λ := by
  induction Θ with
  | leaf fs => simp [comma, appendForms, addBox]
  | cons Λ' r _ ih => simp [comma, addBox, ih]

theorem add_addBox (Θ Λ : NSeq) (A : Form) : (Θ.addBox Λ).add A = (Θ.add A).addBox Λ := by
  induction Θ with
  | leaf fs => rfl
  | cons Λ' r _ ih => simp [addBox, add, ih]

/-- `Θ, A, [Λ]` is `(Θ.add A).addBox Λ`. -/
@[simp] theorem comma_box_single (Θ Λ : NSeq) (A : Form) :
    Θ.comma (cons Λ (leaf [A])) = (Θ.add A).addBox Λ := by
  have := comma_add Θ (cons Λ (leaf [])) A
  simpa [add, add_addBox] using this

/-- A formula just added is the one `erase` takes out. -/
@[simp] theorem erase_add (Θ : NSeq) (A : Form) : (Θ.add A).erase A = Θ := by
  induction Θ with
  | leaf fs => simp [add, erase]
  | cons Λ r _ ih => simp [add, erase, ih]

/-- The box just added is at the position after the old boxes. -/
theorem box?_addBox (Θ Λ : NSeq) : (Θ.addBox Λ).box? Θ.boxes.length = some Λ := by
  induction Θ with
  | leaf fs => rfl
  | cons Λ' r _ ih => simpa [addBox, boxes, box?] using ih

theorem setBox_addBox (Θ Λ Λ' : NSeq) :
    (Θ.addBox Λ).setBox Θ.boxes.length Λ' = Θ.addBox Λ' := by
  induction Θ with
  | leaf fs => rfl
  | cons Λ'' r _ ih => simpa [addBox, boxes, setBox] using ih

/-! ## A node that is replaced -/

/-- The node at a path, after it is replaced. -/
theorem node?_setNode {Γ Θ : NSeq} {a : Path} (X : NSeq) (h : Γ.node? a = some Θ) :
    (Γ.setNode a X).node? a = some X := by
  have := node?_setNode_append [] X h
  simpa [setNode] using this

/-- Replacing a node twice is replacing it once. -/
theorem setNode_setNode {Γ Θ : NSeq} {a : Path} (X Y : NSeq) (h : Γ.node? a = some Θ) :
    (Γ.setNode a X).setNode a Y = Γ.setNode a Y := by
  induction a generalizing Γ with
  | nil => rfl
  | cons i a ih =>
    simp only [node?] at h
    cases hb : Γ.box? i with
    | none => simp [hb] at h
    | some Δ =>
      simp only [hb] at h
      simp only [setNode, hb, box?_setBox_self _ hb, setBox_setBox, ih h]

/-- Replacing a node by itself changes nothing. -/
theorem setNode_self {Γ Θ : NSeq} {a : Path} (h : Γ.node? a = some Θ) :
    Γ.setNode a Θ = Γ := by
  induction a generalizing Γ with
  | nil =>
    have : Γ = Θ := by simpa [node?] using h
    simp [setNode, this]
  | cons i a ih =>
    simp only [node?] at h
    cases hb : Γ.box? i with
    | none => simp [hb] at h
    | some Δ =>
      simp only [hb] at h
      simp only [setNode, hb, ih h, setBox_self hb]

end NSeq

/-! ## Contexts (pp. 7–8) -/

/-- **A sequent context** `Γ{ }`: "a sequent with exactly one occurrence
of the symbol `{ }`, the hole, which does not occur inside formulas"
(p. 7).  Here: the sequent without the hole, the path to the node where
the hole is, and that node.  The hole itself is not written: it is beside
the members of that node. -/
structure Ctx where
  /-- The context with its hole taken out: `Γ{∅}`. -/
  seq : NSeq
  /-- The place of the hole: the path to its node. -/
  path : Path
  /-- The node of the hole, without the hole. -/
  side : NSeq
  /-- That node is at that path. -/
  at_path : seq.node? path = some side

namespace Ctx

/-- **Filling the hole**: `C.fill Δ` is the sequent `Γ{Δ}`, "the sequent
`Γ{Δ}` is obtained by replacing `{ }` inside `Γ{ }` by `Δ`" (p. 7).  The
members of `Δ` join the node of the hole: `side, Δ`. -/
def fill (C : Ctx) (Δ : NSeq) : NSeq := C.seq.setNode C.path (C.side.comma Δ)

/-- The depth of a context, "the number of boxed sequents the hole is
inside of" (p. 8). -/
def depth (C : Ctx) : Nat := C.path.length

/-- The context `Θ, { }`: the hole at the root, beside `Θ`. -/
def root (Θ : NSeq) : Ctx := ⟨Θ, [], Θ, rfl⟩

/-- The context whose hole is at the path `a` of `Γ`. -/
def at_ (Γ : NSeq) (a : Path) {Θ : NSeq} (h : Γ.node? a = some Θ) : Ctx := ⟨Γ, a, Θ, h⟩

/-- `Γ{∅}` is the context with its hole taken out. -/
@[simp] theorem fill_empty (C : Ctx) : C.fill (.leaf []) = C.seq := by
  simp [fill, NSeq.setNode_self C.at_path]

/-- The node of the hole, after the hole is filled. -/
theorem node?_fill (C : Ctx) (Δ : NSeq) :
    (C.fill Δ).node? C.path = some (C.side.comma Δ) :=
  NSeq.node?_setNode _ C.at_path

/-- Replacing the node of the hole in a filled context. -/
theorem setNode_fill (C : Ctx) (Δ X : NSeq) :
    (C.fill Δ).setNode C.path X = C.seq.setNode C.path X :=
  NSeq.setNode_setNode _ _ C.at_path

end Ctx

/-! ## The rules as the figures print them

`Γ{ }` is a context `C`; a filling is a sequent, written with `leaf` and
`cons`: `.leaf [A]` is the sequent `A`, `.leaf [A, B]` is `A, B`,
`.cons (.leaf [A]) (.leaf [])` is `[A]`, and `.cons Δ (.leaf [◇A])` is
`◇A, [Δ]`. -/

/-- The axiom, Figure 2.3: `Γ{p, p̄}`. -/
def Fam.axC {c : Bool} (C : Ctx) (p : Nat) :
    Fam c (C.fill (.leaf [.atom p, .natom p])) :=
  .ax C.path p (C.node?_fill _) (by simp) (by simp)

/-- The rule `∧`, Figure 2.3: from `Γ{A}` and `Γ{B}`, `Γ{A ∧ B}`. -/
def Fam.andC {c : Bool} (C : Ctx) (A B : Form)
    (d₁ : Fam c (C.fill (.leaf [A]))) (d₂ : Fam c (C.fill (.leaf [B]))) :
    Fam c (C.fill (.leaf [A ⋏ B])) :=
  .and C.path A B (C.node?_fill _) (by simp)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d₁)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d₂)

/-- The rule `∨`, Figure 2.3: from `Γ{A, B}`, `Γ{A ∨ B}`. -/
def Fam.orC {c : Bool} (C : Ctx) (A B : Form)
    (d : Fam c (C.fill (.leaf [A, B]))) :
    Fam c (C.fill (.leaf [A ⋎ B])) :=
  .or C.path A B (C.node?_fill _) (by simp)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d)

/-- The rule `□`, Figure 2.3: from `Γ{[A]}`, `Γ{□A}`. -/
def Fam.boxC {c : Bool} (C : Ctx) (A : Form)
    (d : Fam c (C.fill (.cons (.leaf [A]) (.leaf [])))) :
    Fam c (C.fill (.leaf [□A])) :=
  .box C.path A (C.node?_fill _) (by simp)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d)

/-- The rule `◇k_c`, Figure 2.3: from `Γ{◇A, [Δ, A]}`, `Γ{◇A, [Δ]}`. -/
def Fam.diaC {c : Bool} (C : Ctx) (A : Form) (Δ : NSeq)
    (d : Fam c (C.fill (.cons (Δ.add A) (.leaf [◇A])))) :
    Fam c (C.fill (.cons Δ (.leaf [◇A]))) :=
  .dia C.path (C.side.add ◇A).boxes.length A (C.node?_fill _) (by simp)
    (by simpa using NSeq.box?_addBox (C.side.add ◇A) Δ)
    (by
      have e : ((C.side.add ◇A).addBox Δ).setBox C.side.boxes.length (Δ.add A)
          = (C.side.add ◇A).addBox (Δ.add A) := by
        simpa using NSeq.setBox_addBox (C.side.add ◇A) Δ (Δ.add A)
      rw [Ctx.setNode_fill]
      simpa [Ctx.fill, e] using d)

/-- The rule `cut`, Figure 2.4: from `Γ{A}` and `Γ{Ā}`, `Γ{∅}`. -/
def Fam.cutC (C : Ctx) (A : Form)
    (d₁ : Kcut (C.fill (.leaf [A]))) (d₂ : Kcut (C.fill (.leaf [∼A]))) :
    Kcut (C.fill (.leaf [])) :=
  .cut C.path A rfl (C.node?_fill _)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d₁)
    (by rw [Ctx.setNode_fill]; simpa [Ctx.fill] using d₂)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
