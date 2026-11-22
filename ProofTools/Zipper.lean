/-
# `ProofTools.Zipper`: the zipper of an indexed family

Huet's zipper works for any tree-like type once two things are given: what
one layer of a tree with a hole looks like (a **crumb**), and how to fill the
hole (**plug**).  This file states that once, for an *indexed* family
`W : I → Type`, where the index of a subtree may differ from the index of
the tree around it, and builds the paths, the zipper, its moves and its laws
on top.  The instances in this package are the attempts of a proof system
(`ProofTools.Explore`: `I` is the type of judgments, `W j` the attempts at
`j`, and a direction is the number of a premise) and rose trees
(`ProofTools.Zipper.RoseIndexed`: one index, and a direction is the label of
an edge).

**The derivative** (`Deriv`).  A crumb `c : L.Crumb d i j` is one layer at the
root of a tree of index `j`, with a hole at direction `d` whose subtree has
index `i`; `L.plug c w : W j` fills the hole with `w : W i`.  The name is the
textbook one: the crumbs are the one-hole contexts of one layer, that is, the
derivative of the family's signature (McBride 2001; Abbott, Altenkirch, Ghani
and McBride, *Derivatives of containers*, TLCA 2003).

**Opening a layer** (`Deriv.Unplug`) is separate: it is the partial inverse of
`plug`.  The paths and the zipper's upward moves do not need it.

**Passing to the next hole of a layer** (`Deriv.Sibling`) is separate again:
from a crumb and what fills its hole, the same layer with its hole one place
to the left or to the right, in one step.  `sibling d'` reaches a hole of
the same layer by going up and opening the layer again at `d'`, which takes
time in the size of the layer; `left` and `right` keep the layer open.

**A path** `L.Path ds i k` is a list of crumbs, nearest first, from a hole of
index `i` to a root of index `k`, each crumb's root index matching the next
crumb's hole index (a type-aligned list).  `ds` lists the directions of the
holes, nearest first: the reversed address of the hole.  Stored reversed so
that one step down conses a direction, which Lean can match on.

**A zipper** `L.Zipper ds i k` is a focus `w : W i` with a path from it to
the root: three indices, the address `ds`, the focus index `i`, the root
index `k`.  Because `ds` is in the type, `up` is total on
`L.Zipper (d :: ds) i k`.  The parent's index is returned with it (`Σ j`),
since only the crumb knows it.

`z.crumb` is the nearest crumb of a zipper that has one: the layer the focus
sits in, for a caller that keeps something of its own about the path (the
explorer's cursor keeps a count of open goals).

Results (all PROVED):

    z.up.2.toRoot = z.toRoot                              (toRoot_up)
    z.path = .cons z.crumb z.up.2.path                    (path_eq_cons)
    z.down d = some x  →  x.2.up = ⟨j, z⟩                 (up_down)
    z.down d = some x  →  x.2.toRoot = z.toRoot           (toRoot_down)
    z.path.Canon  →  z.up.2.down d = some ⟨i, z⟩          (down_up)
    z.descend a = some x  →  x.2.toRoot = z.toRoot        (toRoot_descend)
    z.path.Canon → z'.path.Canon → z.toRoot = z'.toRoot  →  z = z'   (eq_of_toRoot)
    z.path.Canon → z.descend a = some x  →  x.2.path.Canon           (canon_descend)
    z.path.Canon → ∃ x, (ofRoot z.toRoot).descend ds.reverse = some x ∧
        (⟨_, x.1, x.2⟩ : L.Pos k) = ⟨ds, i, z⟩                         (descend_addr)

The last says that the descent from the root along a zipper's address
reaches the zipper; `L.Pos k` packs a zipper with its address and focus
index, so that positions under one root can be compared.

`Canon` marks the crumbs that `unplug` produces; on them `unplug` undoes
`plug` (`Unplug.unplug_plug`).  With it, a zipper is determined by its root
and its address: the zipper is an optimised form of the pair (root, address),
and holds nothing more.

For the one step to a sibling, with `x` the direction, the index and the
zipper reached (all PROVED):

    z.left = some x   →  x.2.2.up = z.up                  (up_left)
    z.right = some x  →  x.2.2.up = z.up                  (up_right)
    z.left = some x   →  x.2.2.toRoot = z.toRoot          (toRoot_left)
    z.right = some x  →  x.2.2.toRoot = z.toRoot          (toRoot_right)
    z.left = some x   →  x.2.2.right = some ⟨d, i, z⟩     (right_left)
    z.right = some x  →  x.2.2.left = some ⟨d, i, z⟩      (left_right)
    z.left = some x  → x.2.2.path.Canon → z.sibling x.1 = some x.2   (sibling_of_left)
    z.right = some x → x.2.2.path.Canon → z.sibling x.1 = some x.2   (sibling_of_right)

The last two say that the one step is `sibling` at the direction it
reaches.

Core Lean only.
-/

import ProofTools.Audit.FileBound
namespace ProofTools.Zip

universe u v w

/-- **The derivative of an indexed family** `W : I → Type v`, with directions
`D`: the crumbs (one layer with one hole) and how to fill the hole. -/
structure Deriv (I : Type u) (W : I → Type v) (D : Type w) where
  /-- `Crumb d i j`: one layer at the root of a `W j`, with a hole at
  direction `d` whose subtree has index `i`. -/
  Crumb : D → I → I → Type v
  /-- Fill the hole of a crumb. -/
  plug : {d : D} → {i j : I} → Crumb d i j → W i → W j

namespace Deriv

variable {I : Type u} {W : I → Type v} {D : Type w}

/-- **Opening a layer**: the partial inverse of `plug`.  `unplug w d` is the
subtree of `w` at direction `d` and the crumb left behind, if `w` has a hole
at `d`.  `Canon` marks the crumbs `unplug` produces. -/
class Unplug (L : Deriv I W D) where
  /-- Open the root layer of `w` at direction `d`. -/
  unplug : {j : I} → W j → (d : D) → Option ((i : I) × W i × L.Crumb d i j)
  /-- The crumbs that `unplug` produces. -/
  Canon : {d : D} → {i j : I} → L.Crumb d i j → Prop
  /-- Opening and refilling gives the tree back. -/
  plug_unplug : ∀ {j : I} {w : W j} {d : D} {i : I} {w' : W i} {c : L.Crumb d i j},
    unplug w d = some ⟨i, w', c⟩ → L.plug c w' = w
  /-- On a canonical crumb, opening undoes filling. -/
  unplug_plug : ∀ {d : D} {i j : I} {c : L.Crumb d i j} (w : W i),
    Canon c → unplug (L.plug c w) d = some ⟨i, w, c⟩
  /-- `unplug` produces canonical crumbs. -/
  canon_unplug : ∀ {j : I} {w : W j} {d : D} {i : I} {w' : W i} {c : L.Crumb d i j},
    unplug w d = some ⟨i, w', c⟩ → Canon c

/-- **Passing to the next hole of a layer**, in one step.  `right c w` takes
a crumb `c` and what fills its hole, and gives the same layer with its hole
at the next place to the right: the direction and the index of that hole,
what was in it, and the crumb left behind, in which `w` is now a sibling.
`left` is the same to the left.  `none`: there is no hole on that side.
The layer is the same one (`plug_left`, `plug_right`), and the two steps
undo each other.  Separate from `Unplug`: a layer is not opened here, the
hole of an open one is moved. -/
class Sibling (L : Deriv I W D) where
  /-- The hole one place to the left. -/
  left : {d : D} → {i j : I} → L.Crumb d i j → W i →
    Option ((d' : D) × (i' : I) × W i' × L.Crumb d' i' j)
  /-- The hole one place to the right. -/
  right : {d : D} → {i j : I} → L.Crumb d i j → W i →
    Option ((d' : D) × (i' : I) × W i' × L.Crumb d' i' j)
  /-- A step to the left keeps the layer. -/
  plug_left : ∀ {d d' : D} {i i' j : I} {c : L.Crumb d i j} {w : W i} {w' : W i'}
    {c' : L.Crumb d' i' j}, left c w = some ⟨d', i', w', c'⟩ → L.plug c' w' = L.plug c w
  /-- A step to the right keeps the layer. -/
  plug_right : ∀ {d d' : D} {i i' j : I} {c : L.Crumb d i j} {w : W i} {w' : W i'}
    {c' : L.Crumb d' i' j}, right c w = some ⟨d', i', w', c'⟩ → L.plug c' w' = L.plug c w
  /-- Left, then right, returns. -/
  right_left : ∀ {d d' : D} {i i' j : I} {c : L.Crumb d i j} {w : W i} {w' : W i'}
    {c' : L.Crumb d' i' j}, left c w = some ⟨d', i', w', c'⟩ → right c' w' = some ⟨d, i, w, c⟩
  /-- Right, then left, returns. -/
  left_right : ∀ {d d' : D} {i i' j : I} {c : L.Crumb d i j} {w : W i} {w' : W i'}
    {c' : L.Crumb d' i' j}, right c w = some ⟨d', i', w', c'⟩ → left c' w' = some ⟨d, i, w, c⟩

/-- **A path**: crumbs from a hole of index `i` back to a root of index `k`,
nearest first; `ds` lists the directions of the holes, nearest first (the
reversed address of the hole). -/
inductive Path (L : Deriv I W D) : List D → I → I → Type (max u v w) where
  | top {k : I} : Path L [] k k
  | cons {d : D} {ds : List D} {i j k : I} (c : L.Crumb d i j) (p : Path L ds j k) :
      Path L (d :: ds) i k

namespace Path

variable {L : Deriv I W D}

/-- **Fill the hole** with `w` and rebuild the root, crumb by crumb. -/
def plug : {ds : List D} → {i k : I} → L.Path ds i k → W i → W k
  | _, _, _, .top, w => w
  | _, _, _, .cons c p, w => p.plug (L.plug c w)

/-- Every crumb on the path is canonical. -/
def Canon [L.Unplug] : {ds : List D} → {i k : I} → L.Path ds i k → Prop
  | _, _, _, .top => True
  | _, _, _, .cons c p => Unplug.Canon c ∧ p.Canon

@[simp] theorem plug_top {k : I} (w : W k) : (Path.top : L.Path [] k k).plug w = w := rfl

@[simp] theorem plug_cons {d : D} {ds : List D} {i j k : I} (c : L.Crumb d i j)
    (p : L.Path ds j k) (w : W i) : (Path.cons c p).plug w = p.plug (L.plug c w) := rfl

/-- **Plugging is injective on canonical paths with one address**: the hole
index, the path and the filling are all determined by the root. -/
theorem plug_inj [L.Unplug] : ∀ {ds : List D} {i i' k : I} (p : L.Path ds i k)
    (p' : L.Path ds i' k) (w : W i) (w' : W i'), p.Canon → p'.Canon →
      p.plug w = p'.plug w' → (⟨i, p, w⟩ : (i : I) × L.Path ds i k × W i) = ⟨i', p', w'⟩
  | [], _, _, _, .top, .top, w, w', _, _, h => by
    simp only [plug_top] at h
    subst h
    rfl
  | _ :: _, _, _, _, .cons c p, .cons c' p', w, w', hc, hc', h => by
    simp only [Canon] at hc hc'
    simp only [plug_cons] at h
    have ih := plug_inj p p' _ _ hc.2 hc'.2 h
    obtain ⟨hj, hrest⟩ := Sigma.mk.inj ih
    subst hj
    obtain ⟨rfl, hpl⟩ := Prod.mk.inj (eq_of_heq hrest)
    have e := Unplug.unplug_plug w hc.1
    rw [hpl, Unplug.unplug_plug w' hc'.1] at e
    obtain ⟨hi, hwc⟩ := Sigma.mk.inj (Option.some.inj e)
    subst hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hwc)
    rfl

end Path

/-- **A zipper**: a focus of index `i` and the path from it back to the root,
of index `k`; `ds` is the reversed address of the focus. -/
structure Zipper (L : Deriv I W D) (ds : List D) (i k : I) where
  focus : W i
  path : L.Path ds i k

namespace Zipper

variable {L : Deriv I W D} {ds : List D} {i j k : I}

/-- Focus on the root. -/
def ofRoot (w : W k) : L.Zipper [] k k := ⟨w, .top⟩

/-- The whole tree: the path plugged with the focus. -/
def toRoot (z : L.Zipper ds i k) : W k := z.path.plug z.focus

/-- The address of the focus, from the root. -/
abbrev addr (_ : L.Zipper ds i k) : List D := ds.reverse

/-- **Up**: total, since the type says there is a crumb.  The parent's index
comes with it. -/
def up {d : D} : L.Zipper (d :: ds) i k → (j : I) × L.Zipper ds j k
  | ⟨w, .cons c p⟩ => ⟨_, ⟨L.plug c w, p⟩⟩

/-- **The nearest crumb**: the layer the focus sits in.  Its root has the
index that `up` returns. -/
def crumb {d : D} : (z : L.Zipper (d :: ds) i k) → L.Crumb d i z.up.1
  | ⟨_, .cons c _⟩ => c

/-- Replace the focus.  (The zipper comes first, so that it fixes the family
before the new focus is elaborated.) -/
def replace (z : L.Zipper ds i k) (w : W i) : L.Zipper ds i k := ⟨w, z.path⟩

/-- Change the focus. -/
def modify (z : L.Zipper ds i k) (f : W i → W i) : L.Zipper ds i k := ⟨f z.focus, z.path⟩

section Unplug

variable [L.Unplug]

/-- **Down** to direction `d`, if the focus has a hole there. -/
def down (d : D) (z : L.Zipper ds j k) : Option ((i : I) × L.Zipper (d :: ds) i k) :=
  (Unplug.unplug z.focus d).map fun x => ⟨x.1, ⟨x.2.1, .cons x.2.2 z.path⟩⟩

/-- Follow directions down from the focus. -/
def descend : {ds : List D} → {j : I} → (a : List D) → L.Zipper ds j k →
    Option ((i : I) × L.Zipper (a.reverseAux ds) i k)
  | _, _, [], z => some ⟨_, z⟩
  | _, _, d :: a, z => (z.down d).bind fun x => descend a x.2

/-- To the hole at direction `d'` of the same layer. -/
def sibling {d : D} (d' : D) (z : L.Zipper (d :: ds) i k) :
    Option ((i' : I) × L.Zipper (d' :: ds) i' k) :=
  z.up.2.down d'

end Unplug

section Sibling

variable [L.Sibling]

/-- **Left**: to the hole one place to the left in the same layer, in one
step; its direction and index come with it. -/
def left {d : D} : L.Zipper (d :: ds) i k → Option ((d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k)
  | ⟨w, .cons c p⟩ => (Sibling.left c w).map fun x => ⟨x.1, x.2.1, ⟨x.2.2.1, .cons x.2.2.2 p⟩⟩

/-- **Right**: to the hole one place to the right in the same layer, in one
step. -/
def right {d : D} : L.Zipper (d :: ds) i k → Option ((d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k)
  | ⟨w, .cons c p⟩ => (Sibling.right c w).map fun x => ⟨x.1, x.2.1, ⟨x.2.2.1, .cons x.2.2.2 p⟩⟩

end Sibling

/-! ### Laws -/

theorem toRoot_up {d : D} (z : L.Zipper (d :: ds) i k) : z.up.2.toRoot = z.toRoot := by
  obtain ⟨w, p⟩ := z
  cases p
  rfl

theorem toRoot_replace (z : L.Zipper ds i k) (w : W i) :
    (z.replace w).toRoot = z.path.plug w := rfl

/-- The path is the nearest crumb, then the path of the parent. -/
theorem path_eq_cons {d : D} (z : L.Zipper (d :: ds) i k) :
    z.path = .cons z.crumb z.up.2.path := by
  obtain ⟨w, p⟩ := z
  cases p
  rfl

section Sibling

variable [L.Sibling]

/-- **A step to the left keeps the parent.** -/
theorem up_left {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.left = some x) :
    x.2.2.up = z.up := by
  obtain ⟨w, p⟩ := z
  cases p with
  | cons c p =>
    simp only [left, Option.map_eq_some_iff] at h
    obtain ⟨⟨d', i', w', c'⟩, hl, rfl⟩ := h
    show (⟨_, ⟨L.plug c' w', p⟩⟩ : (j : I) × L.Zipper ds j k) = ⟨_, ⟨L.plug c w, p⟩⟩
    rw [Sibling.plug_left hl]

/-- **A step to the right keeps the parent.** -/
theorem up_right {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.right = some x) :
    x.2.2.up = z.up := by
  obtain ⟨w, p⟩ := z
  cases p with
  | cons c p =>
    simp only [right, Option.map_eq_some_iff] at h
    obtain ⟨⟨d', i', w', c'⟩, hr, rfl⟩ := h
    show (⟨_, ⟨L.plug c' w', p⟩⟩ : (j : I) × L.Zipper ds j k) = ⟨_, ⟨L.plug c w, p⟩⟩
    rw [Sibling.plug_right hr]

/-- A step to the left keeps the whole tree. -/
theorem toRoot_left {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.left = some x) :
    x.2.2.toRoot = z.toRoot := by
  rw [← toRoot_up x.2.2, ← toRoot_up z]
  exact congrArg (fun y : (j : I) × L.Zipper ds j k => y.2.toRoot) (up_left h)

/-- A step to the right keeps the whole tree. -/
theorem toRoot_right {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.right = some x) :
    x.2.2.toRoot = z.toRoot := by
  rw [← toRoot_up x.2.2, ← toRoot_up z]
  exact congrArg (fun y : (j : I) × L.Zipper ds j k => y.2.toRoot) (up_right h)

/-- **Left, then right, returns.** -/
theorem right_left {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.left = some x) :
    x.2.2.right = some ⟨d, i, z⟩ := by
  obtain ⟨w, p⟩ := z
  cases p with
  | cons c p =>
    simp only [left, Option.map_eq_some_iff] at h
    obtain ⟨⟨d', i', w', c'⟩, hl, rfl⟩ := h
    show (Sibling.right c' w').map _ = _
    rw [Sibling.right_left hl]
    rfl

/-- **Right, then left, returns.** -/
theorem left_right {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.right = some x) :
    x.2.2.left = some ⟨d, i, z⟩ := by
  obtain ⟨w, p⟩ := z
  cases p with
  | cons c p =>
    simp only [right, Option.map_eq_some_iff] at h
    obtain ⟨⟨d', i', w', c'⟩, hr, rfl⟩ := h
    show (Sibling.left c' w').map _ = _
    rw [Sibling.left_right hr]
    rfl

end Sibling

section Unplug

variable [L.Unplug]

theorem down_eq_some {d : D} {z : L.Zipper ds j k} {x : (i : I) × L.Zipper (d :: ds) i k}
    (h : z.down d = some x) :
    ∃ c : L.Crumb d x.1 j, Unplug.unplug z.focus d = some ⟨x.1, x.2.focus, c⟩ ∧
      x.2.path = .cons c z.path := by
  simp only [down, Option.map_eq_some_iff] at h
  obtain ⟨⟨i', w', c⟩, hu, rfl⟩ := h
  exact ⟨c, hu, rfl⟩

/-- **Down, then up, returns.** -/
theorem up_down {d : D} {z : L.Zipper ds j k} {x : (i : I) × L.Zipper (d :: ds) i k}
    (h : z.down d = some x) : x.2.up = ⟨j, z⟩ := by
  simp only [down, Option.map_eq_some_iff] at h
  obtain ⟨⟨i', w', c⟩, hu, rfl⟩ := h
  show (⟨j, ⟨L.plug c w', z.path⟩⟩ : (j : I) × L.Zipper ds j k) = ⟨j, z⟩
  rw [Unplug.plug_unplug hu]

/-- Down keeps the whole tree. -/
theorem toRoot_down {d : D} {z : L.Zipper ds j k} {x : (i : I) × L.Zipper (d :: ds) i k}
    (h : z.down d = some x) : x.2.toRoot = z.toRoot := by
  rw [← toRoot_up x.2]
  exact congrArg (fun y : (j : I) × L.Zipper ds j k => y.2.toRoot) (up_down h)

/-- **Up, then down the same way, returns**, on a canonical path. -/
theorem down_up {d : D} (z : L.Zipper (d :: ds) i k) (hc : z.path.Canon) :
    z.up.2.down d = some ⟨i, z⟩ := by
  obtain ⟨w, p⟩ := z
  cases p with
  | cons c p =>
    simp only [Path.Canon] at hc
    show (Unplug.unplug (L.plug c w) d).map _ = _
    rw [Unplug.unplug_plug w hc.1]
    rfl

/-- **The step to the left is `sibling`** at the direction it reaches, when
the path reached is canonical: one step, where `sibling` goes up and opens
the layer again. -/
theorem sibling_of_left [L.Sibling] {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.left = some x)
    (hc : x.2.2.path.Canon) : z.sibling x.1 = some x.2 := by
  rw [sibling, ← up_left h]
  exact down_up x.2.2 hc

/-- **The step to the right is `sibling`** at the direction it reaches, when
the path reached is canonical. -/
theorem sibling_of_right [L.Sibling] {d : D} {z : L.Zipper (d :: ds) i k}
    {x : (d' : D) × (i' : I) × L.Zipper (d' :: ds) i' k} (h : z.right = some x)
    (hc : x.2.2.path.Canon) : z.sibling x.1 = some x.2 := by
  rw [sibling, ← up_right h]
  exact down_up x.2.2 hc

theorem toRoot_descend : ∀ {ds : List D} {j : I} (a : List D) {z : L.Zipper ds j k}
    {x : (i : I) × L.Zipper (a.reverseAux ds) i k}, z.descend a = some x →
      x.2.toRoot = z.toRoot
  | _, _, [], _, _, h => by
    simp only [descend, Option.some.injEq] at h
    subst h
    rfl
  | _, _, d :: a, _, _, h => by
    simp only [descend, Option.bind_eq_some_iff] at h
    obtain ⟨x₁, h₁, h₂⟩ := h
    exact (toRoot_descend a h₂).trans (toRoot_down h₁)

theorem canon_down {d : D} {z : L.Zipper ds j k} {x : (i : I) × L.Zipper (d :: ds) i k}
    (hc : z.path.Canon) (h : z.down d = some x) : x.2.path.Canon := by
  obtain ⟨c, hu, hp⟩ := down_eq_some h
  rw [hp]
  exact ⟨Unplug.canon_unplug hu, hc⟩

theorem canon_descend : ∀ {ds : List D} {j : I} (a : List D) {z : L.Zipper ds j k}
    {x : (i : I) × L.Zipper (a.reverseAux ds) i k}, z.path.Canon → z.descend a = some x →
      x.2.path.Canon
  | _, _, [], _, _, hc, h => by
    simp only [descend, Option.some.injEq] at h
    subst h
    exact hc
  | _, _, d :: a, _, _, hc, h => by
    simp only [descend, Option.bind_eq_some_iff] at h
    obtain ⟨x₁, h₁, h₂⟩ := h
    exact canon_descend a (canon_down hc h₁) h₂

/-- **A zipper is determined by its root**, among canonical zippers with the
same address, focus index and root index. -/
theorem eq_of_toRoot {z z' : L.Zipper ds i k} (hc : z.path.Canon) (hc' : z'.path.Canon)
    (h : z.toRoot = z'.toRoot) : z = z' := by
  obtain ⟨w, p⟩ := z
  obtain ⟨w', p'⟩ := z'
  have e := Path.plug_inj p p' w w' hc hc' h
  obtain ⟨-, he⟩ := Sigma.mk.inj e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq he)
  rfl

/-- A descent whose first step is known. -/
theorem descend_cons_of_down {d : D} (a : List D) {z : L.Zipper ds j k}
    {x : (i : I) × L.Zipper (d :: ds) i k} (h : z.down d = some x) :
    z.descend (d :: a) = x.2.descend a := by
  rw [descend, h]
  rfl

/-- Going down one more step after a descent is a descent along the longer
address; the focus reached is the same. -/
theorem descend_snoc : ∀ {ds : List D} {j : I} (a : List D) (d : D) {z : L.Zipper ds j k}
    {x : (i : I) × L.Zipper (a.reverseAux ds) i k} {y : (i : I) × L.Zipper (d :: a.reverseAux ds) i k},
    z.descend a = some x → x.2.down d = some y →
      ∃ y' : (i : I) × L.Zipper ((a ++ [d]).reverseAux ds) i k, z.descend (a ++ [d]) = some y' ∧
        (⟨y'.1, y'.2.focus⟩ : (i : I) × W i) = ⟨y.1, y.2.focus⟩
  | _, _, [], d, z, x, y, hx, hy => by
    simp only [descend, Option.some.injEq] at hx
    subst hx
    have hy' : z.down d = some y := hy
    exact ⟨y, (descend_cons_of_down [] hy').trans rfl, rfl⟩
  | _, _, d' :: a, d, z, x, y, hx, hy => by
    simp only [descend, Option.bind_eq_some_iff] at hx
    obtain ⟨x₁, h₁, h₂⟩ := hx
    obtain ⟨y', hy', he⟩ := descend_snoc a d h₂ hy
    exact ⟨y', (descend_cons_of_down (a ++ [d]) h₁).trans hy', he⟩

/-- From a zipper whose focus is a plugged canonical path, the descent along
the path's address succeeds and reaches what was plugged. -/
theorem exists_descend_plug : ∀ {ds : List D} {i j : I} (p : L.Path ds i j), p.Canon →
    ∀ (w : W i) {ds₀ : List D} (z₀ : L.Zipper ds₀ j k), z₀.focus = p.plug w →
      ∃ x : (i' : I) × L.Zipper (ds.reverse.reverseAux ds₀) i' k, z₀.descend ds.reverse = some x ∧
        (⟨x.1, x.2.focus⟩ : (i : I) × W i) = ⟨i, w⟩
  | _, _, _, .top, _, w, _, z₀, h => ⟨⟨_, z₀⟩, rfl, by rw [h]; rfl⟩
  | d :: ds, _, _, .cons c p, hc, w, ds₀, z₀, h => by
    simp only [Path.Canon] at hc
    obtain ⟨⟨x₁, xf, xp⟩, hx, hfx⟩ := exists_descend_plug p hc.2 (L.plug c w) z₀ h
    dsimp only at hfx
    obtain ⟨rfl, hf⟩ := Sigma.mk.inj hfx
    have hf' : xf = L.plug c w := eq_of_heq hf
    subst hf'
    have hd : (⟨L.plug c w, xp⟩ : L.Zipper (ds.reverse.reverseAux ds₀) _ k).down d =
        some ⟨_, ⟨w, .cons c xp⟩⟩ := by
      show (Unplug.unplug (L.plug c w) d).map _ = _
      rw [Unplug.unplug_plug w hc.1]
      rfl
    obtain ⟨y', hy', he⟩ := descend_snoc ds.reverse d hx hd
    have e : (d :: ds).reverse = ds.reverse ++ [d] := List.reverse_cons
    exact e ▸ ⟨y', hy', he⟩

end Unplug

/-- **A position** under a root of index `k`: a zipper with its address and
the index of its focus packed, so that all positions under one root have one
type. -/
structure _root_.ProofTools.Zip.Deriv.Pos (L : Deriv I W D) (k : I) where
  /-- The directions from the focus back to the root, nearest first. -/
  ds : List D
  /-- The index of the focus. -/
  i : I
  /-- The zipper. -/
  z : L.Zipper ds i k

section Unplug

variable [L.Unplug]

/-- **The descent from the root along a zipper's address reaches the
zipper**, on a canonical path.  With `toRoot_descend` this says that a
zipper and the pair (root, address) determine each other. -/
theorem descend_addr {ds : List D} (z : L.Zipper ds i k) (hc : z.path.Canon) :
    ∃ x, (ofRoot z.toRoot).descend ds.reverse = some x ∧ (⟨_, x.1, x.2⟩ : L.Pos k) = ⟨ds, i, z⟩ := by
  obtain ⟨x, hx, -⟩ := exists_descend_plug z.path hc z.focus (ofRoot z.toRoot) rfl
  refine ⟨x, hx, ?_⟩
  have hroot := toRoot_descend ds.reverse hx
  have hcx := canon_descend (z := ofRoot z.toRoot) ds.reverse
    (show (Path.top : L.Path [] k k).Canon from trivial) hx
  generalize hg : ds.reverse = g at x hx hroot hcx
  have hds : ds = g.reverseAux [] := by
    rw [List.reverseAux_eq, List.append_nil, ← hg, List.reverse_reverse]
  subst hds
  obtain ⟨x₁, x₂⟩ := x
  have e := Path.plug_inj x₂.path z.path x₂.focus z.focus hcx hc hroot
  obtain ⟨rfl, he⟩ := Sigma.mk.inj e
  obtain ⟨hp, hf⟩ := Prod.mk.inj (eq_of_heq he)
  obtain ⟨xf, xp⟩ := x₂
  obtain ⟨zf, zp⟩ := z
  simp only at hp hf
  subst hp hf
  rfl

end Unplug

end Zipper

end Deriv

end ProofTools.Zip

-- The bound on the axioms of this file (`docs/campaign.md`): an upper bound.
#axioms_within_file [propext, Quot.sound]
