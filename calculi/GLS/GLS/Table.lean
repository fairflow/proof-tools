/-
Truth at the root of a finite tree, computed one formula at a time over
all the worlds of the tree: the check of the certifiers `noValid` and
`noDerivable` (`GLS/Run.lean`).

`Form.holds` (`GLS/Semantics.lean`) is the definition: `□A` holds at a
tree if `A` holds at every proper descendant.  Run as it is written it
asks for `A` at every world below and keeps nothing, so on a chain of `n`
worlds and a formula with `n` nested boxes it makes `2ⁿ` calls for `n²`
different questions (compiled: 18.6 s at `n = 30`).

Here a formula is evaluated at every world of the tree at once.  Its
**marks** are a tree of the same shape with two bits at each world: the
formula is true there, and it is true there and at every world below.
The marks of `A ⟶ B` are computed from the marks of `A` and of `B` world
by world, and those of `□A` from the marks of `A`: `□A` is true at a world
if the second bit of `A` is set at each child.  The work is the size of
the formula times the number of worlds.

    Form.holdsT A t = Form.holds A t                    (Form.holdsT_eq)
    Seq.refutedT s t = Seq.refutedAt s t                (Seq.refutedT_eq)

Theory file: it ends with its bound on axioms.
-/
import GLS.Semantics

namespace GLS

/-- **The marks of a formula on a tree**: at each world, whether the
formula is true there (`here`), and whether it is true there and at every
world below (`all`). -/
inductive Marks where
  | node (here all : Bool) (kids : List Marks)
  deriving Repr

/-- The formula is true at the root. -/
def Marks.here : Marks → Bool
  | .node h _ _ => h

/-- The formula is true at the root and at every world below. -/
def Marks.all : Marks → Bool
  | .node _ a _ => a

/-- The marks at a world, from the truth of the formula there and the
marks at its children. -/
def Marks.join (here : Bool) (kids : List Marks) : Marks :=
  .node here (here && kids.all Marks.all) kids

mutual
  /-- The marks of a property of trees: at each world, the property of
  the subtree there. -/
  def Marks.of (f : Tree → Bool) : Tree → Marks
    | .node v ks => .join (f (.node v ks)) (Marks.ofL f ks)
  /-- `Marks.of` on a list. -/
  def Marks.ofL (f : Tree → Bool) : List Tree → List Marks
    | [] => []
    | t :: ts => Marks.of f t :: Marks.ofL f ts
end

mutual
  /-- The marks of `A ⟶ B` from those of `A` and of `B`, world by world. -/
  def Marks.imp : Marks → Marks → Marks
    | .node a _ ks, .node b _ ls => .join (!a || b) (Marks.impL ks ls)
  /-- `Marks.imp` on two lists. -/
  def Marks.impL : List Marks → List Marks → List Marks
    | k :: ks, l :: ls => Marks.imp k l :: Marks.impL ks ls
    | _, _ => []
end

mutual
  /-- The marks of `□A` from those of `A`: true at a world if `A` is true
  at each child and at every world below it. -/
  def Marks.box : Marks → Marks
    | .node _ _ ks => .join (ks.all Marks.all) (Marks.boxL ks)
  /-- `Marks.box` on a list. -/
  def Marks.boxL : List Marks → List Marks
    | [] => []
    | k :: ks => Marks.box k :: Marks.boxL ks
end

/-- **The marks of a formula on a tree.** -/
def Form.marks : Form → Tree → Marks
  | .var p, t => Marks.of (fun u => u.val.contains p) t
  | ⊥, t => Marks.of (fun _ => false) t
  | A ⟶ B, t => (A.marks t).imp (B.marks t)
  | □A, t => (A.marks t).box

/-- **Truth at the root of a tree, by the marks.** -/
def Form.holdsT (A : Form) (t : Tree) : Bool := (A.marks t).here

/-- **A sequent is false at the root of a tree, by the marks**: every
formula of the antecedent is true there and none of the succedent. -/
def Seq.refutedT (s : Seq) (t : Tree) : Bool :=
  s.ant.all (fun A => A.holdsT t) && s.suc.all (fun B => !B.holdsT t)

/-! ## The marks are right -/

theorem Marks.here_join (h : Bool) (ks : List Marks) : (Marks.join h ks).here = h := rfl

theorem Marks.all_join (h : Bool) (ks : List Marks) :
    (Marks.join h ks).all = (h && ks.all Marks.all) := rfl

mutual
  /-- The second bit of `Marks.of f t`: `f` at `t` and at every proper
  descendant. -/
  theorem Marks.all_of (f : Tree → Bool) : (t : Tree) →
      (Marks.of f t).all = (f t && t.desc.all f)
    | .node v ks => by
      rw [Marks.of, Marks.all_join, Marks.all_ofL f ks, Tree.desc]
  theorem Marks.all_ofL (f : Tree → Bool) : (ts : List Tree) →
      (Marks.ofL f ts).all Marks.all = (Tree.descL ts).all f
    | [] => by simp [Marks.ofL, Tree.descL]
    | t :: ts => by
      rw [Marks.ofL, List.all_cons, Marks.all_of f t, Marks.all_ofL f ts, Tree.descL,
        List.all_cons, List.all_append, Bool.and_assoc]
end

theorem Marks.here_of (f : Tree → Bool) : (t : Tree) → (Marks.of f t).here = f t
  | .node _ _ => by rw [Marks.of, Marks.here_join]

mutual
  theorem Marks.imp_of (f g : Tree → Bool) : (t : Tree) →
      (Marks.of f t).imp (Marks.of g t) = Marks.of (fun u => !f u || g u) t
    | .node v ks => by
      simp only [Marks.of, Marks.join, Marks.imp]
      rw [Marks.impL_of f g ks]
  theorem Marks.impL_of (f g : Tree → Bool) : (ts : List Tree) →
      Marks.impL (Marks.ofL f ts) (Marks.ofL g ts) = Marks.ofL (fun u => !f u || g u) ts
    | [] => by simp [Marks.ofL, Marks.impL]
    | t :: ts => by
      simp only [Marks.ofL, Marks.impL]
      rw [Marks.imp_of f g t, Marks.impL_of f g ts]
end

mutual
  theorem Marks.box_of (f : Tree → Bool) : (t : Tree) →
      (Marks.of f t).box = Marks.of (fun u => u.desc.all f) t
    | .node v ks => by
      simp only [Marks.of, Marks.join, Marks.box]
      rw [Marks.boxL_of f ks, Marks.all_ofL f ks, Tree.desc]
  theorem Marks.boxL_of (f : Tree → Bool) : (ts : List Tree) →
      Marks.boxL (Marks.ofL f ts) = Marks.ofL (fun u => u.desc.all f) ts
    | [] => by simp [Marks.ofL, Marks.boxL]
    | t :: ts => by
      simp only [Marks.ofL, Marks.boxL]
      rw [Marks.box_of f t, Marks.boxL_of f ts]
end

/-- **The marks of a formula are its truth at each world.** -/
theorem Form.marks_eq : (A : Form) → (t : Tree) → A.marks t = Marks.of (fun u => A.holds u) t
  | .var p, t => by simp only [Form.marks, Form.holds]
  | ⊥, t => by simp only [Form.marks, Form.holds]
  | A ⟶ B, t => by
    simp only [Form.marks, Form.holds]
    rw [Form.marks_eq A t, Form.marks_eq B t, Marks.imp_of]
  | □A, t => by
    simp only [Form.marks, Form.holds]
    rw [Form.marks_eq A t, Marks.box_of]

/-- **S25.  Truth by the marks is truth.** -/
theorem Form.holdsT_eq (A : Form) (t : Tree) : A.holdsT t = A.holds t := by
  rw [Form.holdsT, Form.marks_eq, Marks.here_of]

/-- **S26.  The two checks of a countermodel are one function.** -/
theorem Seq.refutedT_eq (s : Seq) (t : Tree) : s.refutedT t = s.refutedAt t := by
  simp only [Seq.refutedT, Seq.refutedAt, Form.holdsT_eq]

end GLS

#axioms_within_file [propext, Quot.sound]
