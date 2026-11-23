/-
# `ProofTools.Zipper.Rose`: Huet's zipper for edge-labelled rose trees

G. Huet, *Functional Pearl: The Zipper*, J. Functional Programming 7(5),
1997.  A zipper is a tree with one position in focus: the subtree at the
focus, and the path back to the root, where each step (a *crumb*) records the
parent's label, the edge taken, and the siblings on either side.  Moving the
focus one step costs `O(1)`, and so does changing the tree at the focus.

The trees are rose trees with labels on nodes (`α`) and on edges (`κ`).  A
child is known by its position among its siblings (`downAt i`) or by its
edge (`down k`: the first child along `k`), and the address of a node is the
list of the edges from the root (`Zipper.addr`).  With `κ = Unit` these are
Huet's trees; with `κ = Bool`, binary trees whose edges say left or right;
in general the edge says what kind of successor a child is.

Results (all PROVED).  Every move keeps the whole tree:

    z.up = some z'         →  z'.toTree = z.toTree                 (toTree_up)
    z.downAt i = some z'   →  z'.toTree = z.toTree                 (toTree_downAt)
    z.down k = some z'     →  z'.toTree = z.toTree                 (toTree_down)
    z.left = some z'       →  z'.toTree = z.toTree                 (toTree_left)
    z.right = some z'      →  z'.toTree = z.toTree                 (toTree_right)
    z.descend a = some z'  →  z'.toTree = z.toTree                 (toTree_descend)
    z.top.toTree = z.toTree                                        (toTree_top)

The moves undo each other:

    z.down k = some z'     →  z'.up = some z                       (up_down)
    z.downAt i = some z'   →  z'.up = some z                       (up_downAt)
    (⟨c.plug t, p⟩ : Zipper κ α).downAt c.left.length = some ⟨t, c :: p⟩
                                                                   (downAt_up)
    z.left = some z'       →  z'.right = some z                    (right_left)
    z.right = some z'      →  z'.left = some z                     (left_right)

The address of the focus:

    z.up = some z'         →  z'.addr = z.addr.dropLast            (addr_up)
    z.down k = some z'     →  z'.addr = z.addr ++ [k]              (addr_down)
    z.left = some z'       →  z'.addr.dropLast = z.addr.dropLast   (addr_left)
    z.right = some z'      →  z'.addr.dropLast = z.addr.dropLast   (addr_right)
    z.descend a = some z'  →  z'.addr = z.addr ++ a                (addr_descend)
    goto t a = some z      →  z.addr = a ∧ z.toTree = t            (goto_addr)

Navigating by address finds the subtree at that address (`t.get? a`: the
first child along each edge):

    (z.down k).map focus = find? k z.focus.children                (focus_down)
    (z.descend a).map focus = z.focus.get? a                       (focus_descend)
    (goto t a).map focus = t.get? a                                (goto_focus)

and, for a list of children:

    splitKey k cs = some (l, b, r)  →  l.reverse ++ (k, b) :: r = cs
                                                                   (splitKey_spec)
    (splitKey k cs).map (·.2.1) = find? k cs                       (splitKey_find?)

No law is stated here for the edits at the focus (`modify`, `replace`,
`addChild`, `insertLeft`, `insertRight`, `delete`).

Beside this file: the same trees as an instance of the zipper of an indexed
family, with the address in the type (`ProofTools.Zipper.RoseIndexed`);
changing a tree at an address (`ProofTools.Zipper.RoseUpdate`); drawing, and
an equality test proved lawful (`ProofTools.Zipper.RoseRender`).

Core Lean only.
-/
import ProofTools.Audit.FileBound

namespace ProofTools.Zip

universe u v

/-- A rose tree with node labels `α` and edge labels `κ`: a node carries a label
and a list of children, each reached by a labelled edge. -/
inductive RTree (κ : Type u) (α : Type v) where
  | node (label : α) (children : List (κ × RTree κ α))

namespace RTree

variable {κ : Type u} {α : Type v}

/-- The label at the root. -/
def label : RTree κ α → α
  | .node a _ => a

/-- The labelled children of the root. -/
def children : RTree κ α → List (κ × RTree κ α)
  | .node _ cs => cs

/-- A leaf. -/
abbrev leaf (a : α) : RTree κ α := .node a []

end RTree

section Lookup

variable {κ : Type u} {β : Type v} [DecidableEq κ]

/-- The value of the first pair with key `k`. -/
def find? (k : κ) : List (κ × β) → Option β
  | [] => none
  | (k', b) :: cs => if k' = k then some b else find? k cs

/-- Split a list at the first pair with key `k`: the pairs to its left (nearest
first), its value, and the pairs to its right. -/
def splitKey (k : κ) : List (κ × β) → Option (List (κ × β) × β × List (κ × β))
  | [] => none
  | (k', b) :: cs =>
    if k' = k then some ([], b, cs)
    else (splitKey k cs).map fun (l, b', r) => (l ++ [(k', b)], b', r)

theorem splitKey_spec {k : κ} :
    ∀ {cs : List (κ × β)} {l b r}, splitKey k cs = some (l, b, r) → l.reverse ++ (k, b) :: r = cs
  | [], _, _, _, h => by simp [splitKey] at h
  | (k', b') :: cs, l, b, r, h => by
    unfold splitKey at h
    by_cases hk : k' = k
    · subst hk
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · simp only [if_neg hk, Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨l', b'', r', h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp [← splitKey_spec h']

theorem splitKey_find? {k : κ} :
    ∀ cs : List (κ × β), (splitKey k cs).map (·.2.1) = find? k cs
  | [] => rfl
  | (k', b) :: cs => by
    unfold splitKey find?
    by_cases hk : k' = k
    · simp [hk]
    · simp only [if_neg hk, Option.map_map]
      rw [← splitKey_find? cs]
      rfl

end Lookup

/-- One step back towards the root: the parent's label, the edge from the parent
to the focus, and the siblings to the left (nearest first) and to the right. -/
structure Crumb (κ : Type u) (α : Type v) where
  label : α
  edge : κ
  left : List (κ × RTree κ α)
  right : List (κ × RTree κ α)

/-- Put a subtree back into the hole of a crumb. -/
def Crumb.plug {κ : Type u} {α : Type v} (c : Crumb κ α) (t : RTree κ α) : RTree κ α :=
  .node c.label (c.left.reverse ++ (c.edge, t) :: c.right)

/-- A zipper: the subtree in focus and the path back to the root, nearest crumb
first. -/
structure Zipper (κ : Type u) (α : Type v) where
  focus : RTree κ α
  path : List (Crumb κ α)

namespace Zipper

variable {κ : Type u} {α : Type v}

/-- Focus on the root of a tree. -/
def ofTree (t : RTree κ α) : Zipper κ α := ⟨t, []⟩

/-- The whole tree: plug the focus back in, crumb by crumb. -/
def toTree (z : Zipper κ α) : RTree κ α :=
  z.path.foldl (fun t c => c.plug t) z.focus

/-- The address of the focus: the edges from the root. -/
def addr (z : Zipper κ α) : List κ :=
  (z.path.map Crumb.edge).reverse

/-- The focus is at the root. -/
def atRoot (z : Zipper κ α) : Bool := z.path.isEmpty

/-- The label at the focus. -/
def label (z : Zipper κ α) : α := z.focus.label

/-! ## Moves -/

/-- Move to the parent. -/
def up : Zipper κ α → Option (Zipper κ α)
  | ⟨_, []⟩ => none
  | ⟨t, c :: p⟩ => some ⟨c.plug t, p⟩

/-- Move to the `i`-th child (from `0`). -/
def downAt (i : Nat) : Zipper κ α → Option (Zipper κ α)
  | ⟨.node a cs, p⟩ =>
    match cs.drop i with
    | [] => none
    | (k, t) :: r => some ⟨t, ⟨a, k, (cs.take i).reverse, r⟩ :: p⟩

/-- Move to the first child along edge `k`. -/
def down [DecidableEq κ] (k : κ) : Zipper κ α → Option (Zipper κ α)
  | ⟨.node a cs, p⟩ => (splitKey k cs).map fun (l, t, r) => ⟨t, ⟨a, k, l, r⟩ :: p⟩

/-- Move to the left sibling. -/
def left : Zipper κ α → Option (Zipper κ α)
  | ⟨t, ⟨a, k, (k', t') :: l, r⟩ :: p⟩ => some ⟨t', ⟨a, k', l, (k, t) :: r⟩ :: p⟩
  | _ => none

/-- Move to the right sibling. -/
def right : Zipper κ α → Option (Zipper κ α)
  | ⟨t, ⟨a, k, l, (k', t') :: r⟩ :: p⟩ => some ⟨t', ⟨a, k', (k, t) :: l, r⟩ :: p⟩
  | _ => none

/-- Move to the root. -/
def top (z : Zipper κ α) : Zipper κ α := ofTree z.toTree

/-- Follow a list of edges down from the focus. -/
def descend [DecidableEq κ] : List κ → Zipper κ α → Option (Zipper κ α)
  | [], z => some z
  | k :: a, z => (z.down k).bind (descend a)

/-- Focus on the node at address `a` of `t`. -/
def goto [DecidableEq κ] (t : RTree κ α) (a : List κ) : Option (Zipper κ α) :=
  (ofTree t).descend a

/-! ## Edits at the focus -/

/-- Change the label at the focus. -/
def modify (f : α → α) : Zipper κ α → Zipper κ α
  | ⟨.node a cs, p⟩ => ⟨.node (f a) cs, p⟩

/-- Replace the subtree at the focus. -/
def replace (t : RTree κ α) (z : Zipper κ α) : Zipper κ α := ⟨t, z.path⟩

/-- Add a last child to the focus. -/
def addChild (k : κ) (t : RTree κ α) : Zipper κ α → Zipper κ α
  | ⟨.node a cs, p⟩ => ⟨.node a (cs ++ [(k, t)]), p⟩

/-- Insert a sibling to the left of the focus (the focus stays). -/
def insertLeft (k : κ) (t : RTree κ α) : Zipper κ α → Option (Zipper κ α)
  | ⟨f, ⟨a, e, l, r⟩ :: p⟩ => some ⟨f, ⟨a, e, (k, t) :: l, r⟩ :: p⟩
  | _ => none

/-- Insert a sibling to the right of the focus (the focus stays). -/
def insertRight (k : κ) (t : RTree κ α) : Zipper κ α → Option (Zipper κ α)
  | ⟨f, ⟨a, e, l, r⟩ :: p⟩ => some ⟨f, ⟨a, e, l, (k, t) :: r⟩ :: p⟩
  | _ => none

/-- Delete the subtree at the focus, as Huet does: the focus moves to the right
sibling, or else to the left sibling, or else to the parent. -/
def delete : Zipper κ α → Option (Zipper κ α)
  | ⟨_, ⟨a, _, l, (k', t') :: r⟩ :: p⟩ => some ⟨t', ⟨a, k', l, r⟩ :: p⟩
  | ⟨_, ⟨a, _, (k', t') :: l, []⟩ :: p⟩ => some ⟨t', ⟨a, k', l, []⟩ :: p⟩
  | ⟨_, ⟨a, _, [], []⟩ :: p⟩ => some ⟨.node a [], p⟩
  | ⟨_, []⟩ => none

/-! ## Laws -/

@[simp] theorem toTree_ofTree (t : RTree κ α) : (ofTree t).toTree = t := rfl

@[simp] theorem toTree_cons (t : RTree κ α) (c : Crumb κ α) (p : List (Crumb κ α)) :
    toTree ⟨t, c :: p⟩ = toTree ⟨c.plug t, p⟩ := rfl

@[simp] theorem addr_cons (t : RTree κ α) (c : Crumb κ α) (p : List (Crumb κ α)) :
    addr ⟨t, c :: p⟩ = addr ⟨c.plug t, p⟩ ++ [c.edge] := by
  simp [addr]

theorem toTree_up {z z' : Zipper κ α} (h : z.up = some z') : z'.toTree = z.toTree := by
  obtain ⟨t, _ | ⟨c, p⟩⟩ := z
  · simp [up] at h
  · simp only [up, Option.some.injEq] at h
    subst h
    rfl

theorem addr_up {z z' : Zipper κ α} (h : z.up = some z') : z'.addr = z.addr.dropLast := by
  obtain ⟨t, _ | ⟨c, p⟩⟩ := z
  · simp [up] at h
  · simp only [up, Option.some.injEq] at h
    subst h
    simp [addr]

theorem up_downAt {z z' : Zipper κ α} {i : Nat} (h : z.downAt i = some z') : z'.up = some z := by
  obtain ⟨⟨a, cs⟩, p⟩ := z
  simp only [downAt] at h
  split at h
  · simp at h
  · rename_i k t r hd
    simp only [Option.some.injEq] at h
    subst h
    simp only [up, Crumb.plug, List.reverse_reverse, ← hd, List.take_append_drop]

theorem toTree_downAt {z z' : Zipper κ α} {i : Nat} (h : z.downAt i = some z') :
    z'.toTree = z.toTree :=
  (toTree_up (up_downAt h)).symm

/-- Going up and then down at the position of the old focus returns it. -/
theorem downAt_up (t : RTree κ α) (c : Crumb κ α) (p : List (Crumb κ α)) :
    (⟨c.plug t, p⟩ : Zipper κ α).downAt c.left.length = some ⟨t, c :: p⟩ := by
  obtain ⟨a, k, l, r⟩ := c
  have hd : (l.reverse ++ (k, t) :: r).drop l.length = (k, t) :: r := by
    simp
  have ht : (l.reverse ++ (k, t) :: r).take l.length = l.reverse := by
    simp
  simp only [Crumb.plug, downAt, hd, ht, List.reverse_reverse]

theorem up_down [DecidableEq κ] {z z' : Zipper κ α} {k : κ} (h : z.down k = some z') :
    z'.up = some z := by
  obtain ⟨⟨a, cs⟩, p⟩ := z
  simp only [down, Option.map_eq_some_iff, Prod.exists] at h
  obtain ⟨l, t, r, hs, rfl⟩ := h
  simp [up, Crumb.plug, splitKey_spec hs]

theorem toTree_down [DecidableEq κ] {z z' : Zipper κ α} {k : κ} (h : z.down k = some z') :
    z'.toTree = z.toTree :=
  (toTree_up (up_down h)).symm

theorem addr_down [DecidableEq κ] {z z' : Zipper κ α} {k : κ} (h : z.down k = some z') :
    z'.addr = z.addr ++ [k] := by
  obtain ⟨⟨a, cs⟩, p⟩ := z
  simp only [down, Option.map_eq_some_iff, Prod.exists] at h
  obtain ⟨l, t, r, _, rfl⟩ := h
  simp [addr]

theorem focus_down [DecidableEq κ] (z : Zipper κ α) (k : κ) :
    (z.down k).map focus = find? k z.focus.children := by
  obtain ⟨⟨a, cs⟩, p⟩ := z
  simp only [down, Option.map_map, RTree.children]
  rw [← splitKey_find? cs]
  rfl

theorem right_left {z z' : Zipper κ α} (h : z.left = some z') : z'.right = some z := by
  obtain ⟨t, _ | ⟨⟨a, k, _ | ⟨⟨k', t'⟩, l⟩, r⟩, p⟩⟩ := z <;> simp [left] at h
  subst h
  rfl

theorem left_right {z z' : Zipper κ α} (h : z.right = some z') : z'.left = some z := by
  obtain ⟨t, _ | ⟨⟨a, k, l, _ | ⟨⟨k', t'⟩, r⟩⟩, p⟩⟩ := z <;> simp [right] at h
  subst h
  rfl

theorem toTree_left {z z' : Zipper κ α} (h : z.left = some z') : z'.toTree = z.toTree := by
  obtain ⟨t, _ | ⟨⟨a, k, _ | ⟨⟨k', t'⟩, l⟩, r⟩, p⟩⟩ := z <;> simp [left] at h
  subst h
  simp [Crumb.plug]

theorem toTree_right {z z' : Zipper κ α} (h : z.right = some z') : z'.toTree = z.toTree :=
  (toTree_left (left_right h)).symm

theorem addr_left {z z' : Zipper κ α} (h : z.left = some z') :
    z'.addr.dropLast = z.addr.dropLast := by
  obtain ⟨t, _ | ⟨⟨a, k, _ | ⟨⟨k', t'⟩, l⟩, r⟩, p⟩⟩ := z <;> simp [left] at h
  subst h
  simp [addr]

theorem addr_right {z z' : Zipper κ α} (h : z.right = some z') :
    z'.addr.dropLast = z.addr.dropLast :=
  (addr_left (left_right h)).symm

theorem toTree_top (z : Zipper κ α) : z.top.toTree = z.toTree := rfl

theorem toTree_descend [DecidableEq κ] :
    ∀ {a : List κ} {z z' : Zipper κ α}, z.descend a = some z' → z'.toTree = z.toTree
  | [], _, _, h => by simp only [descend, Option.some.injEq] at h; rw [h]
  | k :: a, z, z', h => by
    simp only [descend, Option.bind_eq_some_iff] at h
    obtain ⟨z₁, h₁, h₂⟩ := h
    rw [toTree_descend h₂, toTree_down h₁]

theorem addr_descend [DecidableEq κ] :
    ∀ {a : List κ} {z z' : Zipper κ α}, z.descend a = some z' → z'.addr = z.addr ++ a
  | [], _, _, h => by simp only [descend, Option.some.injEq] at h; simp [h]
  | k :: a, z, z', h => by
    simp only [descend, Option.bind_eq_some_iff] at h
    obtain ⟨z₁, h₁, h₂⟩ := h
    rw [addr_descend h₂, addr_down h₁]
    simp

/-- `goto t a` focuses on a node with address `a`, inside the tree `t`. -/
theorem goto_addr [DecidableEq κ] {t : RTree κ α} {a : List κ} {z : Zipper κ α}
    (h : goto t a = some z) : z.addr = a ∧ z.toTree = t := by
  exact ⟨(addr_descend h).trans (List.nil_append a), toTree_descend h⟩

end Zipper

namespace RTree

variable {κ : Type u} {α : Type v} [DecidableEq κ]

/-- The subtree at an address: follow the first child along each edge. -/
def get? : RTree κ α → List κ → Option (RTree κ α)
  | t, [] => some t
  | t, k :: a => (find? k t.children).bind fun t' => get? t' a

end RTree

namespace Zipper

variable {κ : Type u} {α : Type v} [DecidableEq κ]

theorem focus_descend :
    ∀ (a : List κ) (z : Zipper κ α), (z.descend a).map focus = z.focus.get? a
  | [], z => rfl
  | k :: a, z => by
    have hd := focus_down z k
    simp only [descend, RTree.get?]
    rw [← hd]
    cases hz : z.down k with
    | none => rfl
    | some z₁ => simpa using focus_descend a z₁

/-- **Navigation by address finds the subtree at that address.** -/
theorem goto_focus (t : RTree κ α) (a : List κ) : (goto t a).map focus = t.get? a :=
  focus_descend a (ofTree t)

end Zipper

end ProofTools.Zip

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
