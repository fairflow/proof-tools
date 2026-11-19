/-
# `ProofTools.Explore.System`: proof systems, attempts, derivations

A **proof system** is a type of judgments, a type of moves (a rule, named by
its data) and one function, `step`: the premises a move asks for at a
judgment, or the reason it does not apply.

An **attempt** `Att S o j` is a tree of moves with conclusion `j`.  The
Boolean `o` says whether open goals are allowed; a **derivation** `Der S j`
is an attempt where they are not.  Each node writes its premises `ps` and
carries the equation `S.step m j = .ok ps`, which the kernel proves by
evaluating `step`.  The children are a list indexed by the premises
(`Atts`), so an attempt is first-order data.

The one theorem an instance proves about its `step` is `S.Sound D`, for its
own notion `D` of what holds (derivability in the calculus as its source
states it, or validity).  Then (PROVED here):

    S.Sound D → (d : Att S o j) → (∀ g ∈ d.goals, D g) → D j        (Att.sound)
    S.Sound D → Der S j → D j                                        (Der.sound)

`Att.sound` says that an attempt is a derived rule, from its open goals to
its root.

Functions on attempts are written for every `o`, since Lean's structural
recursion needs the index to be a variable.

Core Lean only.
-/

import ProofTools.Audit.FileBound
namespace ProofTools.Explore

/-- **A proof system**: judgments, moves, and the premises a move asks for
at a judgment (or why it does not apply). -/
structure ProofSystem where
  /-- What is derived. -/
  Judg : Type
  /-- A rule, named by its data. -/
  Move : Type
  /-- The premises, or why the move does not apply. -/
  step : Move → Judg → Except String (List Judg)

mutual
/-- **An attempt** at `j`.  With `o = true` open goals are allowed. -/
inductive Att (S : ProofSystem) : Bool → S.Judg → Type
  /-- An open goal. -/
  | goal {j : S.Judg} : Att S true j
  /-- A move `m` at `j`, its premises `ps` as `S.step` gives them, and an
  attempt at each. -/
  | node {o : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
      (h : S.step m j = .ok ps) (ds : Atts S o ps) : Att S o j
/-- Attempts at each judgment of a list. -/
inductive Atts (S : ProofSystem) : Bool → List S.Judg → Type
  | nil {o : Bool} : Atts S o []
  | cons {o : Bool} {p : S.Judg} {ps : List S.Judg} (d : Att S o p) (ds : Atts S o ps) :
      Atts S o (p :: ps)
end

/-- **A derivation**: an attempt with no open goal. -/
abbrev Der (S : ProofSystem) (j : S.Judg) : Type := Att S false j

variable {S : ProofSystem}

mutual
/-- The open goals, leftmost first. -/
def Att.goals : {o : Bool} → {j : S.Judg} → Att S o j → List S.Judg
  | _, j, .goal => [j]
  | _, _, .node _ _ _ ds => ds.goals
/-- The open goals of a list of attempts, leftmost first. -/
def Atts.goals : {o : Bool} → {ps : List S.Judg} → Atts S o ps → List S.Judg
  | _, _, .nil => []
  | _, _, .cons d ds => d.goals ++ ds.goals
end

mutual
/-- The number of moves. -/
def Att.size : {o : Bool} → {j : S.Judg} → Att S o j → Nat
  | _, _, .goal => 0
  | _, _, .node _ _ _ ds => ds.size + 1
/-- The number of moves in a list of attempts. -/
def Atts.size : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Nat
  | _, _, .nil => 0
  | _, _, .cons d ds => d.size + ds.size
end

@[simp] theorem Att.goals_goal {j : S.Judg} : (Att.goal : Att S true j).goals = [j] := by
  simp [Att.goals]

@[simp] theorem Att.goals_node {o : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
    (h : S.step m j = .ok ps) (ds : Atts S o ps) : (Att.node m ps h ds).goals = ds.goals := by
  simp [Att.goals]

@[simp] theorem Atts.goals_nil {o : Bool} : (Atts.nil : Atts S o []).goals = [] := by
  simp [Atts.goals]

@[simp] theorem Atts.goals_cons {o : Bool} {p : S.Judg} {ps : List S.Judg} (d : Att S o p)
    (ds : Atts S o ps) : (Atts.cons d ds).goals = d.goals ++ ds.goals := by
  simp [Atts.goals]

/-- Every premise open. -/
def Atts.open : (ps : List S.Judg) → Atts S true ps
  | [] => .nil
  | _ :: ps => .cons .goal (Atts.open ps)

@[simp] theorem Atts.goals_open : (ps : List S.Judg) → (Atts.open ps : Atts S true ps).goals = ps
  | [] => by simp [Atts.open]
  | p :: ps => by simp [Atts.open, Atts.goals_open ps]

/-! ## A derivation is an attempt -/

mutual
/-- An attempt with or without open goals, as one where they are allowed. -/
def Att.toAtt : {o : Bool} → {j : S.Judg} → Att S o j → Att S true j
  | _, _, .goal => .goal
  | _, _, .node m ps h ds => .node m ps h ds.toAtts
/-- `Att.toAtt` on a list. -/
def Atts.toAtts : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Atts S true ps
  | _, _, .nil => .nil
  | _, _, .cons d ds => .cons d.toAtt ds.toAtts
end

private theorem Att.node_heq {o o' : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
    (h : S.step m j = .ok ps) (e : o = o') {ds : Atts S o ps} {ds' : Atts S o' ps}
    (hd : HEq ds ds') : HEq (Att.node m ps h ds) (Att.node m ps h ds') := by
  subst e
  cases hd
  rfl

private theorem Atts.cons_heq {o o' : Bool} {p : S.Judg} {ps : List S.Judg} (e : o = o')
    {d : Att S o p} {d' : Att S o' p} {ds : Atts S o ps} {ds' : Atts S o' ps}
    (hd : HEq d d') (hds : HEq ds ds') : HEq (Atts.cons d ds) (Atts.cons d' ds') := by
  subst e
  cases hd
  cases hds
  rfl

private theorem Atts.nil_heq {o o' : Bool} (e : o = o') :
    HEq (Atts.nil : Atts S o []) (Atts.nil : Atts S o' []) := by
  subst e
  rfl

mutual
private theorem Att.toAtt_heq : {o : Bool} → {j : S.Judg} → (d : Att S o j) → o = true →
    HEq d.toAtt d
  | _, _, .goal, _ => HEq.rfl
  | _, _, .node m ps h ds, ho => Att.node_heq m ps h ho.symm (Atts.toAtts_heq ds ho)
private theorem Atts.toAtts_heq : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    o = true → HEq ds.toAtts ds
  | _, _, .nil, ho => Atts.nil_heq ho.symm
  | _, _, .cons d ds, ho => Atts.cons_heq ho.symm (Att.toAtt_heq d ho) (Atts.toAtts_heq ds ho)
end

/-- On an attempt, `toAtt` changes nothing. -/
@[simp] theorem Att.toAtt_eq {j : S.Judg} (d : Att S true j) : d.toAtt = d :=
  eq_of_heq (Att.toAtt_heq d rfl)

@[simp] theorem Atts.toAtts_eq {ps : List S.Judg} (ds : Atts S true ps) : ds.toAtts = ds :=
  eq_of_heq (Atts.toAtts_heq ds rfl)

mutual
@[simp] theorem Att.goals_toAtt : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    d.toAtt.goals = d.goals
  | _, _, .goal => rfl
  | _, _, .node _ _ _ ds => by simp [Att.toAtt, Atts.goals_toAtts ds]
@[simp] theorem Atts.goals_toAtts : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    ds.toAtts.goals = ds.goals
  | _, _, .nil => rfl
  | _, _, .cons d ds => by simp [Atts.toAtts, Att.goals_toAtt d, Atts.goals_toAtts ds]
end

mutual
/-- An attempt with no open goal left, as a derivation. -/
def Att.toDer : {o : Bool} → {j : S.Judg} → (d : Att S o j) → d.goals = [] → Der S j
  | _, _, .goal, h => by simp at h
  | _, _, .node m ps hs ds, h => .node m ps hs (ds.toDers (by simpa using h))
/-- `Att.toDer` on a list. -/
def Atts.toDers : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) → ds.goals = [] →
    Atts S false ps
  | _, _, .nil, _ => .nil
  | _, _, .cons d ds, h =>
    .cons (d.toDer (by simp at h; exact h.1)) (ds.toDers (by simp at h; exact h.2))
end

mutual
/-- A derivation has no open goal. -/
theorem Att.goals_of_closed : {o : Bool} → {j : S.Judg} → (d : Att S o j) → o = false →
    d.goals = []
  | _, _, .goal, ho => by cases ho
  | _, _, .node _ _ _ ds, ho => by simp [Atts.goals_of_closed ds ho]
theorem Atts.goals_of_closed : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    o = false → ds.goals = []
  | _, _, .nil, _ => rfl
  | _, _, .cons d ds, ho => by simp [Att.goals_of_closed d ho, Atts.goals_of_closed ds ho]
end

@[simp] theorem Der.goals {j : S.Judg} (d : Der S j) : Att.goals d = [] :=
  Att.goals_of_closed d rfl

/-! ## The first checker: steps -/

/-- **Soundness of the moves** for a notion `D` of what holds: where a move
applies and its premises hold, its conclusion holds.  The one theorem an
instance proves about its `step`. -/
def ProofSystem.Sound (S : ProofSystem) (D : S.Judg → Prop) : Prop :=
  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, D p) → D j

variable {D : S.Judg → Prop}

mutual
/-- **An attempt is a derived rule**, from its open goals to its root. -/
theorem Att.sound (hS : S.Sound D) : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    (∀ g ∈ d.goals, D g) → D j
  | _, _, .goal, hg => hg _ (by simp)
  | _, _, .node m ps h ds, hg => hS m _ ps h (Atts.sound hS ds (by simpa using hg))
theorem Atts.sound (hS : S.Sound D) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (∀ g ∈ ds.goals, D g) → ∀ p ∈ ps, D p
  | _, _, .nil, _ => by simp
  | _, _, .cons d ds, hg => by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · exact hp ▸ Att.sound hS d fun g hgm => hg g (by simp [hgm])
    · exact Atts.sound hS ds (fun g hgm => hg g (by simp [hgm])) p hp
end

/-- **What a derivation derives holds.** -/
theorem Der.sound (hS : S.Sound D) {j : S.Judg} (d : Der S j) : D j :=
  Att.sound hS d (by simp)

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
