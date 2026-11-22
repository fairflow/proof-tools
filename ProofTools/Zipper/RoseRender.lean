/-
# `ProofTools.Zipper.RoseRender`: printing and comparing rose trees

`RTree.drawWith ek ea t` prints `t` one node per line, indented by depth, each
line `edge ↦ label`; `Zipper.drawWith` prints the whole tree with the focus
marked `▶`.  For `#eval IO.println …` in examples.

`Repr` is derived.  `DecidableEq` does not derive for this type (it recurs
through `List`), so `BEq` is written by hand and proved lawful: a `#guard`
comparing trees checks real equality.

Results (PROVED), with `LawfulBEq` for the edges and the labels:

    RTree.beq t t' = true ↔ t = t'                                 (RTree.beq_iff_eq)
    RTree.beqL cs ds = true ↔ cs = ds                              (RTree.beqL_iff_eq)

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Zipper.Rose

namespace ProofTools.Zip

universe u v w

variable {κ : Type u} {α : Type v} {β : Type w}

deriving instance Repr for RTree

namespace RTree

mutual
/-- Equality test on trees. -/
def beq [BEq κ] [BEq α] : RTree κ α → RTree κ α → Bool
  | .node a cs, .node b ds => a == b && beqL cs ds

/-- Equality test on lists of children. -/
def beqL [BEq κ] [BEq α] : List (κ × RTree κ α) → List (κ × RTree κ α) → Bool
  | [], [] => true
  | (k, t) :: cs, (k', t') :: ds => k == k' && beq t t' && beqL cs ds
  | _, _ => false
end

instance [BEq κ] [BEq α] : BEq (RTree κ α) := ⟨beq⟩

mutual
theorem beq_iff_eq [BEq κ] [LawfulBEq κ] [BEq α] [LawfulBEq α] :
    ∀ {t t' : RTree κ α}, beq t t' = true ↔ t = t'
  | .node a cs, .node b ds => by
    simp only [beq, Bool.and_eq_true, _root_.beq_iff_eq, beqL_iff_eq, RTree.node.injEq]

theorem beqL_iff_eq [BEq κ] [LawfulBEq κ] [BEq α] [LawfulBEq α] :
    ∀ {cs ds : List (κ × RTree κ α)}, beqL cs ds = true ↔ cs = ds
  | [], [] => by simp [beqL]
  | [], _ :: _ => by simp [beqL]
  | _ :: _, [] => by simp [beqL]
  | (k, t) :: cs, (k', t') :: ds => by
    simp only [beqL, Bool.and_eq_true, _root_.beq_iff_eq, beq_iff_eq, beqL_iff_eq,
      List.cons.injEq, Prod.mk.injEq, and_assoc]
end

instance [BEq κ] [LawfulBEq κ] [BEq α] [LawfulBEq α] : LawfulBEq (RTree κ α) where
  eq_of_beq h := beq_iff_eq.1 h
  rfl := beq_iff_eq.2 rfl

mutual
/-- Relabel every node. -/
def map (f : α → β) : RTree κ α → RTree κ β
  | .node a cs => .node (f a) (mapL f cs)

/-- Relabel every node of a list of children. -/
def mapL (f : α → β) : List (κ × RTree κ α) → List (κ × RTree κ β)
  | [] => []
  | (k, t) :: cs => (k, map f t) :: mapL f cs
end

mutual
/-- The lines of a drawing of `t`, each indented by `ind`, the root reached by
the edge text `e`. -/
def linesAt (ek : κ → String) (ea : α → String) (ind e : String) : RTree κ α → List String
  | .node a cs => (ind ++ e ++ ea a) :: linesL ek ea (ind ++ "    ") cs

/-- The lines of a drawing of a list of children. -/
def linesL (ek : κ → String) (ea : α → String) (ind : String) :
    List (κ × RTree κ α) → List String
  | [] => []
  | (k, t) :: cs => linesAt ek ea ind (ek k ++ " ↦ ") t ++ linesL ek ea ind cs
end

/-- Draw a tree, with printers for edges and labels. -/
def drawWith (ek : κ → String) (ea : α → String) (t : RTree κ α) : String :=
  "\n".intercalate (linesAt ek ea "" "" t)

/-- Draw a tree with the default printers. -/
def draw [ToString κ] [ToString α] (t : RTree κ α) : String := drawWith toString toString t

end RTree

/-- Relabel a crumb. -/
def Crumb.map (f : α → β) (c : Crumb κ α) : Crumb κ β :=
  ⟨f c.label, c.edge, RTree.mapL f c.left, RTree.mapL f c.right⟩

namespace Zipper

/-- Draw the whole tree with the focus marked `▶`. -/
def drawWith (ek : κ → String) (ea : α → String) (z : Zipper κ α) : String :=
  let f : RTree κ String := match z.focus.map ea with
    | .node a cs => .node ("▶ " ++ a) cs
  (Zipper.toTree ⟨f, z.path.map (Crumb.map ea)⟩).drawWith ek id

/-- Draw with the default printers. -/
def draw [ToString κ] [ToString α] (z : Zipper κ α) : String := z.drawWith toString toString

end Zipper

end ProofTools.Zip

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
