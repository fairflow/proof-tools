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

and, with the marks of each different subformula kept in a table, which
is the check the certifiers run:

    Seq.refutedM s t = Seq.refutedAt s t                (Seq.refutedM_eq)

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

/-! ## A table over the different subformulas

`Form.marks` computes the marks of a formula for each **occurrence** of a
subformula.  A formula in which a subformula occurs twice at each level
(`binForm n` of the corpus: `2ⁿ` connectives written out, `n` different
subformulas) costs its written size times the worlds, where the kernel,
which keeps what it has reduced, pays for each different subformula once
(7.7 s compiled against 2.0 s in the kernel at `binTree 12`).

Here the marks of a subformula are kept in a table once computed, and
looked up before the subformula is entered.  An entry holds the size of
its formula, and the table is in order of size, the largest first: a
subformula is entered after its parts, so it goes in at the head, and a
search for a formula stops at the first smaller entry.  A variable and
`⊥` are not kept.  Nothing proved rests on the order or on the sizes:
an entry found for a formula has that formula. -/

/-- **The table**: formulas with their marks on one tree, each with the
size of the formula. -/
abbrev Memo : Type := List (Nat × Form × Marks)

/-- The marks kept for a formula of size `s`, if any: among the entries
of that size. -/
def Memo.find (s : Nat) (A : Form) : Memo → Option Marks
  | [] => none
  | (u, B, m) :: memo =>
    if s < u then Memo.find s A memo
    else if u < s then none
    else if B = A then some m
    else Memo.find s A memo

/-- A formula of size `s` put into the table with its marks, before the
first entry that is not larger. -/
def Memo.put (s : Nat) (A : Form) (m : Marks) : Memo → Memo
  | [] => [(s, A, m)]
  | (u, B, x) :: memo =>
    if s < u then (u, B, x) :: Memo.put s A m memo
    else (s, A, m) :: (u, B, x) :: memo

/-- **The marks of a formula on a tree, with a table**: the marks, and
the table with the subformulas met. -/
def Form.marksM (t : Tree) : Form → Memo → Marks × Memo
  | .var p, memo => (Marks.of (fun u => u.val.contains p) t, memo)
  | ⊥, memo => (Marks.of (fun _ => false) t, memo)
  | A ⟶ B, memo =>
    match memo.find (A ⟶ B).size (A ⟶ B) with
    | some m => (m, memo)
    | none =>
      let ra := A.marksM t memo
      let rb := B.marksM t ra.2
      (ra.1.imp rb.1, rb.2.put (A ⟶ B).size (A ⟶ B) (ra.1.imp rb.1))
  | □A, memo =>
    match memo.find (□A).size (□A) with
    | some m => (m, memo)
    | none =>
      let ra := A.marksM t memo
      (ra.1.box, ra.2.put (□A).size (□A) ra.1.box)

/-- Truth at the root of a tree of each formula of a list, with a
table. -/
def holdsM (t : Tree) : List Form → Memo → List Bool × Memo
  | [], memo => ([], memo)
  | A :: l, memo =>
    let ra := A.marksM t memo
    let rl := holdsM t l ra.2
    (ra.1.here :: rl.1, rl.2)

/-- **A sequent is false at the root of a tree, by the marks with one
table for the sequent**: every formula of the antecedent is true there
and none of the succedent. -/
def Seq.refutedM (s : Seq) (t : Tree) : Bool :=
  let ra := holdsM t s.ant []
  let rs := holdsM t s.suc ra.2
  ra.1.all (fun b => b) && rs.1.all (fun b => !b)

/-- **Every entry of the table has the marks of its formula** on the
tree. -/
def Memo.Ok (t : Tree) (memo : Memo) : Prop := ∀ e ∈ memo, e.2.2 = e.2.1.marks t

theorem Memo.ok_nil (t : Tree) : Memo.Ok t [] := fun _ h => nomatch h

theorem Memo.find_sound {t : Tree} {s : Nat} {A : Form} {m : Marks} :
    (memo : Memo) → memo.Ok t → memo.find s A = some m → m = A.marks t
  | [], _, h => by cases h
  | (u, B, x) :: memo, hok, h => by
    have hrest : Memo.Ok t memo := fun e he => hok e (List.mem_cons_of_mem _ he)
    unfold Memo.find at h
    split at h
    · exact Memo.find_sound memo hrest h
    · split at h
      · cases h
      · split at h
        · next hBA =>
          cases h
          subst hBA
          exact hok (u, B, m) (List.mem_cons_self ..)
        · exact Memo.find_sound memo hrest h

theorem Memo.put_ok {t : Tree} {s : Nat} {A : Form} {m : Marks} (hm : m = A.marks t) :
    (memo : Memo) → memo.Ok t → (memo.put s A m).Ok t
  | [], _ => by
    intro e he
    rcases List.mem_singleton.1 he with rfl
    exact hm
  | (u, B, x) :: memo, hok => by
    have hrest : Memo.Ok t memo := fun e he => hok e (List.mem_cons_of_mem _ he)
    unfold Memo.put
    split
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hok _ (List.mem_cons_self ..)
      · exact Memo.put_ok hm memo hrest e he
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hm
      · exact hok e he

/-- **The marks with a table are the marks**, and the table stays
right. -/
theorem Form.marksM_spec (t : Tree) : (A : Form) → (memo : Memo) → memo.Ok t →
    (A.marksM t memo).1 = A.marks t ∧ (A.marksM t memo).2.Ok t
  | .var p, memo, h => ⟨rfl, h⟩
  | ⊥, memo, h => ⟨rfl, h⟩
  | A ⟶ B, memo, h => by
    unfold Form.marksM
    cases hf : memo.find (A ⟶ B).size (A ⟶ B) with
    | some m => exact ⟨Memo.find_sound memo h hf, h⟩
    | none =>
      obtain ⟨ha, hma⟩ := Form.marksM_spec t A memo h
      obtain ⟨hb, hmb⟩ := Form.marksM_spec t B _ hma
      have e : (A.marksM t memo).1.imp (B.marksM t (A.marksM t memo).2).1 = (A ⟶ B).marks t := by
        rw [ha, hb]
        rfl
      exact ⟨e, Memo.put_ok e _ hmb⟩
  | □A, memo, h => by
    unfold Form.marksM
    cases hf : memo.find (□A).size (□A) with
    | some m => exact ⟨Memo.find_sound memo h hf, h⟩
    | none =>
      obtain ⟨ha, hma⟩ := Form.marksM_spec t A memo h
      have e : (A.marksM t memo).1.box = (□A).marks t := by
        rw [ha]
        rfl
      exact ⟨e, Memo.put_ok e _ hma⟩

theorem holdsM_spec (t : Tree) : (l : List Form) → (memo : Memo) → memo.Ok t →
    (holdsM t l memo).1 = l.map (fun A => A.holds t) ∧ (holdsM t l memo).2.Ok t
  | [], memo, h => ⟨rfl, h⟩
  | A :: l, memo, h => by
    obtain ⟨ha, hma⟩ := Form.marksM_spec t A memo h
    obtain ⟨hl, hml⟩ := holdsM_spec t l _ hma
    refine ⟨?_, hml⟩
    show (A.marksM t memo).1.here :: (holdsM t l (A.marksM t memo).2).1 = _
    rw [ha, hl, List.map_cons]
    exact congrArg (· :: _) (Form.holdsT_eq A t)

/-- **S30.  The check with a table is the definition**: the two checks of
a countermodel are one function. -/
theorem Seq.refutedM_eq (s : Seq) (t : Tree) : s.refutedM t = s.refutedAt t := by
  obtain ⟨ha, hma⟩ := holdsM_spec t s.ant [] (Memo.ok_nil t)
  obtain ⟨hs, _⟩ := holdsM_spec t s.suc _ hma
  show ((holdsM t s.ant []).1.all (fun b => b) &&
    (holdsM t s.suc (holdsM t s.ant []).2).1.all (fun b => !b)) = _
  rw [ha, hs, Seq.refutedAt, List.all_map, List.all_map]
  rfl

end GLS

#axioms_within_file [propext, Quot.sound]
