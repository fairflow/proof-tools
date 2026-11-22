/-
# `ProofTools.Zipper.RoseIndexed`: the indexed zipper of rose trees, an instance

Rose trees `RTree κ α` (`ProofTools.Zipper.Rose`) are an instance of the
zipper of an indexed family (`ProofTools.Zipper`), with one index (`Unit`:
every subtree has the same type), directions the edge labels `κ`, and as
crumb at edge `k` the parent's label with the siblings to the left (nearest
first) and to the right of the hole:

    rtreeDeriv κ α : Deriv Unit (fun _ => RTree κ α) κ
    IPath κ α ra   := (rtreeDeriv κ α).Path ra () ()
    IZipper κ α ra := (rtreeDeriv κ α).Zipper ra () ()

`IZipper κ α ra` has its focus at the *reversed* address `ra` (nearest edge
first), so the address `ra.reverse` is in the type:
* `up` is total on `IZipper κ α (k :: ra)`: the type says the focus is not the
  root;
* `down k` lands in `IZipper κ α (k :: ra)`, and `goto t a` in
  `IZipper κ α a.reverse`, with no casts.

`ofTree`, `up`, `down`, `descend`, `goto` and `toTree`, their laws and the
injectivity of plugging are the generic ones of `ProofTools.Zipper`, read at
this instance.  `left` and `right` (to the next sibling, whatever its edge)
and the edits `modify` and `replace` are written here.  Opening a layer
(`unplug`) takes the *first* child along an edge, so it needs
`DecidableEq κ`; paths, `up` and `plug` do not.  A crumb is canonical
(`Canon`) when no left sibling shares the edge to the hole; `down` makes only
canonical crumbs.

Results (all PROVED), for `z : IZipper κ α ra`:

    z.up.toTree = z.toTree                                         (toTree_up)
    z.down k = some z'  →  z'.up = z                               (up_down)
    z.path.Canon  →  z.up.down k = some z                          (down_up)
    z.down k = some z'  →  z'.toTree = z.toTree                    (toTree_down)
    z.path.Canon → z'.path.Canon → z.toTree = z'.toTree  →  z = z' (eq_of_toTree)
    z.path.Canon → z.down k = some z'  →  z'.path.Canon            (canon_down)
    z.path.Canon → z.descend a = some z'  →  z'.path.Canon         (canon_descend)
    goto t a = some z  →  z.path.Canon                             (canon_goto)
    goto t a = some z → z'.path.Canon → z'.toTree = t  →  z' = z   (goto_unique)
    p.Canon → p'.Canon → p.plug t = p'.plug t'  →  p = p' ∧ t = t' (IPath.plug_inj)

The last but one says that `goto t a` is the only canonical zipper on `t` at
the address `a`.

`forget` maps an indexed zipper to a plain one (`ProofTools.Zipper.Rose`),
and `Zipper.index` maps back; both are compatible with the moves (all
PROVED):

    z.forget.addr = z.addr                                         (addr_forget)
    z.toTree = z.forget.toTree                                     (toTree_eq_forget)
    z.forget.up = some z.up.forget                                 (forget_up)
    (z.down k).map forget = z.forget.down k                        (forget_down)
    (z.descend a).map forget = z.forget.descend a                  (forget_descend)
    (goto t a).map forget = Zipper.goto t a                        (forget_goto)
    z.index.forget = z              for `z : Zipper κ α`           (Zipper.forget_index)
    p.toList.map Crumb.edge = ra    for `p : IPath κ α ra`         (IPath.map_edge_toList)
    (IPath.ofList l).toList = l                                    (IPath.toList_ofList)
    p.plug t = p.toList.foldl (fun t c => c.plug t) t              (IPath.plug_eq_foldl)

and, for a list of children:

    k ∉ m.map Prod.fst  →  splitKey k (m ++ (k, b) :: r) = some (m.reverse, b, r)
                                                                   (splitKey_append)
    k ∉ l.map Prod.fst  →  splitKey k (l.reverse ++ (k, b) :: r) = some (l, b, r)
                                                                   (splitKey_plug)
    splitKey k cs = some (l, b, r)  →  k ∉ l.map Prod.fst          (splitKey_left)

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Zipper
import ProofTools.Zipper.Rose

namespace ProofTools.Zip

universe u v

section SplitKey

variable {κ : Type u} [DecidableEq κ] {β : Type v}

theorem splitKey_append {k : κ} {b : β} {r : List (κ × β)} :
    ∀ {m : List (κ × β)}, k ∉ m.map Prod.fst →
      splitKey k (m ++ (k, b) :: r) = some (m.reverse, b, r)
  | [], _ => by simp [splitKey]
  | (k', b') :: m, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hk : k' ≠ k := fun e => h.1 e.symm
    simp only [List.cons_append, splitKey, if_neg hk, splitKey_append h.2, Option.map_some,
      List.reverse_cons]

/-- Splitting at the hole of a crumb whose left siblings avoid its edge gives
the crumb back. -/
theorem splitKey_plug {k : κ} {b : β} {l r : List (κ × β)} (h : k ∉ l.map Prod.fst) :
    splitKey k (l.reverse ++ (k, b) :: r) = some (l, b, r) := by
  have h' : k ∉ l.reverse.map Prod.fst := by simpa [List.map_reverse] using h
  simpa using splitKey_append h'

/-- The siblings left of the first child along `k` avoid `k`. -/
theorem splitKey_left {k : κ} :
    ∀ {cs : List (κ × β)} {l b r}, splitKey k cs = some (l, b, r) → k ∉ l.map Prod.fst
  | [], _, _, _, h => by simp [splitKey] at h
  | (k', b') :: cs, l, b, r, h => by
    unfold splitKey at h
    by_cases hk : k' = k
    · simp only [if_pos hk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp
    · simp only [if_neg hk, Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨l', b'', r', h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, not_or]
      exact ⟨splitKey_left h', fun e => hk e.symm⟩

end SplitKey

/-- **The derivative of rose trees.**  A crumb at edge `k` is the parent's
label and the siblings to the left (nearest first) and to the right of the
hole; the hole's edge is the direction `k`.  One index: every subtree has the
same type. -/
def rtreeDeriv (κ : Type u) (α : Type v) : Deriv Unit (fun _ => RTree κ α) κ where
  Crumb _ _ _ := α × List (κ × RTree κ α) × List (κ × RTree κ α)
  plug := @fun k _ _ c t => Crumb.plug ⟨c.1, k, c.2.1, c.2.2⟩ t

/-- **Opening a rose tree** at edge `k`: the first child along `k`. -/
instance rtreeUnplug (κ : Type u) (α : Type v) [DecidableEq κ] : (rtreeDeriv κ α).Unplug where
  unplug := fun t k => match t with
    | .node a cs => (splitKey k cs).map fun x => ⟨(), x.2.1, (a, x.1, x.2.2)⟩
  Canon := @fun k _ _ c => k ∉ c.2.1.map Prod.fst
  plug_unplug := by
    intro j w d i w' c h
    cases i
    obtain ⟨a, cs⟩ := w
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨l, t, r⟩, hs, he⟩ := h
    obtain ⟨-, he⟩ := Sigma.mk.inj he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq he)
    show RTree.node a (l.reverse ++ (d, t) :: r) = _
    rw [splitKey_spec hs]
  unplug_plug := by
    intro d i j c w h
    show (splitKey d (c.2.1.reverse ++ (d, w) :: c.2.2)).map _ = _
    rw [splitKey_plug h]
    rfl
  canon_unplug := by
    intro j w d i w' c h
    obtain ⟨a, cs⟩ := w
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨l, t, r⟩, hs, he⟩ := h
    obtain ⟨-, he⟩ := Sigma.mk.inj he
    obtain ⟨-, rfl⟩ := Prod.mk.inj (eq_of_heq he)
    exact splitKey_left hs

/-- A path back to the root whose type is the list of edges taken, nearest
first: the reversed address of the focus. -/
abbrev IPath (κ : Type u) (α : Type v) (ra : List κ) := (rtreeDeriv κ α).Path ra () ()

/-- A zipper whose focus has reversed address `ra`. -/
abbrev IZipper (κ : Type u) (α : Type v) (ra : List κ) := (rtreeDeriv κ α).Zipper ra () ()

variable {κ : Type u} {α : Type v}

namespace IPath

/-- The crumbs of an indexed path, as plain crumbs. -/
def toList : {ra : List κ} → IPath κ α ra → List (Crumb κ α)
  | [], .top => []
  | k :: _, .cons c p => ⟨c.1, k, c.2.1, c.2.2⟩ :: toList p

theorem map_edge_toList : {ra : List κ} → (p : IPath κ α ra) → p.toList.map Crumb.edge = ra
  | [], .top => rfl
  | _ :: _, .cons _ p => by simp [toList, map_edge_toList p]

/-- Index a list of crumbs by its edges. -/
def ofList : (l : List (Crumb κ α)) → IPath κ α (l.map Crumb.edge)
  | [] => .top
  | c :: l => .cons (c.label, c.left, c.right) (ofList l)

theorem toList_ofList : (l : List (Crumb κ α)) → (ofList l).toList = l
  | [] => rfl
  | c :: l => by simp [ofList, toList, toList_ofList l]

/-- Plugging an indexed path is folding `Crumb.plug` over its crumbs. -/
theorem plug_eq_foldl : {ra : List κ} → (p : IPath κ α ra) → (t : RTree κ α) →
    p.plug t = p.toList.foldl (fun t c => c.plug t) t
  | [], .top, _ => rfl
  | _ :: _, .cons _ p, _ => plug_eq_foldl p _

/-- **Plugging is injective on canonical paths of one index.** -/
theorem plug_inj [DecidableEq κ] {ra : List κ} {p p' : IPath κ α ra} (hc : p.Canon)
    (hc' : p'.Canon) {t t' : RTree κ α} (h : p.plug t = p'.plug t') : p = p' ∧ t = t' := by
  obtain ⟨-, he⟩ := Sigma.mk.inj (Deriv.Path.plug_inj p p' t t' hc hc' h)
  exact Prod.mk.inj (eq_of_heq he)

end IPath

namespace IZipper

/-- Forget the index. -/
def forget {ra : List κ} (z : IZipper κ α ra) : Zipper κ α := ⟨z.focus, IPath.toList z.path⟩

/-- The address of the focus, read off the type. -/
abbrev addr {ra : List κ} (_ : IZipper κ α ra) : List κ := ra.reverse

/-- The index is the address. -/
theorem addr_forget {ra : List κ} (z : IZipper κ α ra) : z.forget.addr = z.addr := by
  simp [forget, Zipper.addr, IPath.map_edge_toList]

/-- Focus on the root of a tree. -/
def ofTree (t : RTree κ α) : IZipper κ α [] := Deriv.Zipper.ofRoot (L := rtreeDeriv κ α) t

/-- **Up**: total, since the type says the focus is not the root. -/
def up {k : κ} {ra : List κ} (z : IZipper κ α (k :: ra)) : IZipper κ α ra :=
  (Deriv.Zipper.up (L := rtreeDeriv κ α) z).2

/-- Move to the first child along edge `k`. -/
def down [DecidableEq κ] {ra : List κ} (k : κ) (z : IZipper κ α ra) :
    Option (IZipper κ α (k :: ra)) :=
  (Deriv.Zipper.down (L := rtreeDeriv κ α) k z).map (·.2)

/-- Follow a list of edges down from the focus. -/
def descend [DecidableEq κ] {ra : List κ} (a : List κ) (z : IZipper κ α ra) :
    Option (IZipper κ α (a.reverseAux ra)) :=
  (Deriv.Zipper.descend (L := rtreeDeriv κ α) a z).map (·.2)

/-- Focus on the node at address `a` of `t`; the result's type records `a`. -/
def goto [DecidableEq κ] (t : RTree κ α) (a : List κ) : Option (IZipper κ α a.reverse) :=
  (ofTree t).descend a

/-- Move to the left sibling; its edge is returned with the zipper. -/
def left {k : κ} {ra : List κ} : IZipper κ α (k :: ra) → Option (Σ k', IZipper κ α (k' :: ra))
  | ⟨t, .cons (a, (k', t') :: l, r) p⟩ => some ⟨k', ⟨t', .cons (a, l, (k, t) :: r) p⟩⟩
  | ⟨_, .cons (_, [], _) _⟩ => none

/-- Move to the right sibling; its edge is returned with the zipper. -/
def right {k : κ} {ra : List κ} : IZipper κ α (k :: ra) → Option (Σ k', IZipper κ α (k' :: ra))
  | ⟨t, .cons (a, l, (k', t') :: r) p⟩ => some ⟨k', ⟨t', .cons (a, (k, t) :: l, r) p⟩⟩
  | ⟨_, .cons (_, _, []) _⟩ => none

/-- Change the label at the focus. -/
def modify {ra : List κ} (f : α → α) : IZipper κ α ra → IZipper κ α ra
  | ⟨.node a cs, p⟩ => ⟨.node (f a) cs, p⟩

/-- Replace the subtree at the focus. -/
def replace {ra : List κ} (t : RTree κ α) (z : IZipper κ α ra) : IZipper κ α ra := ⟨t, z.path⟩

/-- The whole tree. -/
def toTree {ra : List κ} (z : IZipper κ α ra) : RTree κ α :=
  Deriv.Zipper.toRoot (L := rtreeDeriv κ α) z

/-! ### Laws, read off the generic ones -/

/-- The whole tree is the path plugged with the focus. -/
theorem toTree_eq_plug {ra : List κ} (z : IZipper κ α ra) : z.toTree = z.path.plug z.focus :=
  rfl

/-- … which is the plain zipper's whole tree. -/
theorem toTree_eq_forget {ra : List κ} (z : IZipper κ α ra) : z.toTree = z.forget.toTree :=
  IPath.plug_eq_foldl z.path z.focus

theorem toTree_up {k : κ} {ra : List κ} (z : IZipper κ α (k :: ra)) :
    z.up.toTree = z.toTree :=
  Deriv.Zipper.toRoot_up z

theorem up_down [DecidableEq κ] {ra : List κ} {k : κ} {z : IZipper κ α ra}
    {z' : IZipper κ α (k :: ra)} (h : z.down k = some z') : z'.up = z := by
  simp only [down, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact congrArg (fun y : (j : Unit) × IZipper κ α ra => y.2) (Deriv.Zipper.up_down hx)

theorem down_up [DecidableEq κ] {k : κ} {ra : List κ} (z : IZipper κ α (k :: ra))
    (hc : z.path.Canon) : z.up.down k = some z := by
  simp only [down, up, Deriv.Zipper.down_up z hc, Option.map_some]

theorem toTree_down [DecidableEq κ] {ra : List κ} {k : κ} {z : IZipper κ α ra}
    {z' : IZipper κ α (k :: ra)} (h : z.down k = some z') : z'.toTree = z.toTree := by
  rw [← up_down h, toTree_up]

/-- **An indexed zipper is determined by its tree**, among canonical ones of
the same index. -/
theorem eq_of_toTree [DecidableEq κ] {ra : List κ} {z z' : IZipper κ α ra}
    (hc : z.path.Canon) (hc' : z'.path.Canon) (h : z.toTree = z'.toTree) : z = z' :=
  Deriv.Zipper.eq_of_toRoot hc hc' h

theorem canon_down [DecidableEq κ] {ra : List κ} {k : κ} {z : IZipper κ α ra}
    {z' : IZipper κ α (k :: ra)} (hc : z.path.Canon) (h : z.down k = some z') :
    z'.path.Canon := by
  simp only [down, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact Deriv.Zipper.canon_down hc hx

theorem canon_descend [DecidableEq κ] {ra : List κ} (a : List κ) {z : IZipper κ α ra}
    {z' : IZipper κ α (a.reverseAux ra)} (hc : z.path.Canon) (h : z.descend a = some z') :
    z'.path.Canon := by
  simp only [descend, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact Deriv.Zipper.canon_descend a hc hx

theorem canon_goto [DecidableEq κ] {t : RTree κ α} {a : List κ} {z : IZipper κ α a.reverse}
    (h : goto t a = some z) : z.path.Canon :=
  canon_descend a (z := ofTree t) trivial h

/-! ### Agreement with the plain zipper -/

theorem forget_up {k : κ} {ra : List κ} (z : IZipper κ α (k :: ra)) :
    z.forget.up = some z.up.forget := by
  obtain ⟨t, p⟩ := z
  cases p
  rfl

theorem forget_down [DecidableEq κ] {ra : List κ} (k : κ) (z : IZipper κ α ra) :
    (z.down k).map forget = z.forget.down k := by
  obtain ⟨⟨a, cs⟩, p⟩ := z
  simp only [down, Deriv.Zipper.down, forget, Zipper.down, Option.map_map]
  show Option.map _ ((splitKey k cs).map _) = _
  cases splitKey k cs <;> rfl

theorem forget_descend [DecidableEq κ] :
    ∀ {ra : List κ} (a : List κ) (z : IZipper κ α ra),
      (z.descend a).map forget = z.forget.descend a
  | _, [], z => rfl
  | _, k :: a, z => by
    simp only [descend, Deriv.Zipper.descend, Zipper.descend] at *
    rw [← forget_down k z]
    simp only [down, Option.map_map]
    cases Deriv.Zipper.down k z with
    | none => rfl
    | some x => simpa [descend] using forget_descend a x.2

/-- The indexed and the plain `goto` agree. -/
theorem forget_goto [DecidableEq κ] (t : RTree κ α) (a : List κ) :
    (goto t a).map forget = Zipper.goto t a :=
  forget_descend a (ofTree t)

/-- **`goto t a` is the only canonical zipper on `t` at `a`.** -/
theorem goto_unique [DecidableEq κ] {t : RTree κ α} {a : List κ} {z : IZipper κ α a.reverse}
    (h : goto t a = some z) (z' : IZipper κ α a.reverse) (hc : z'.path.Canon)
    (ht : z'.toTree = t) : z' = z := by
  have hz : z.toTree = t := by
    have := forget_goto t a
    rw [h] at this
    rw [toTree_eq_forget]
    exact (Zipper.goto_addr this.symm).2
  exact eq_of_toTree hc (canon_goto h) (ht.trans hz.symm)

end IZipper

/-- Index a plain zipper by its reversed address. -/
def Zipper.index (z : Zipper κ α) : IZipper κ α (z.path.map Crumb.edge) :=
  ⟨z.focus, IPath.ofList z.path⟩

theorem Zipper.forget_index (z : Zipper κ α) : z.index.forget = z := by
  simp [Zipper.index, IZipper.forget, IPath.toList_ofList]

end ProofTools.Zip

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
