/-
# `ProofTools.Explore.Zipper`: the zipper of attempts

The attempts of a proof system are an indexed family (`Att S o j`, indexed
by the judgment `j`), and this file gives it the zipper of
`ProofTools.Zipper`: a direction is the number of a premise, and a **crumb**
is a node with one of its attempts taken out.

    structure Crumb S o d p j     -- a node at `j` whose premise number `d`, the judgment `p`, is the hole
      move  : S.Move
      lsr   : List S.Judg         -- the premises left of the hole, nearest first
      rs    : List S.Judg         -- the premises right of the hole
      h     : S.step move j = .ok (lsr.reverseAux (p :: rs))
      left  : Atts S o lsr        -- the attempts left of the hole, nearest first
      right : Atts S o rs
      hd    : lsr.length = d

The left siblings are kept nearest first, so that passing to the next
sibling is one cons and the equation `h` serves unchanged: for lists,
`(p :: lsr).reverseAux rs` and `lsr.reverseAux (p :: rs)` are the same term
after one step of computation.

Results (PROVED):

    (l.revAppend r).goals = l.goalsRev ++ r.goals              (Atts.goals_revAppend)
    (p.plug d).goals = goalsL p ++ d.goals ++ goalsR p         (Path.goals_plug)

and the three laws of `Zip.Deriv.Unplug`, so that `down`, `descend`,
`sibling` and the laws of `ProofTools.Zipper` hold for attempts.  Every
path of attempts is canonical (`Path.canon`): the direction is part of the
crumb.

**The next premise** (`Crumb.stepLeft`, `Crumb.stepRight`): the hole of a
crumb moved one premise, in one step; with them attempts are an instance of
`Zip.Deriv.Sibling`, and the zipper's `left` and `right` hold for them.
PROVED: each is the node filled and opened again at the neighbouring
premise,

    (c.plug w).unplug d = some (c.stepLeft w)       for c at premise d + 1   (Crumb.unplug_plug_pred)
    (c.plug w).unplug (d + 1) = c.stepRight w                                (Crumb.unplug_plug_succ)

`goalsBefore z` is the number of open goals of the premises before the
focus in its node, read off the nearest crumb; PROVED:

    (goalsL z.path).length = (goalsL z.up.2.path).length + goalsBefore z     (length_goalsL)

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Zipper
import ProofTools.Explore.System

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-! ## Lists of attempts, nearest first -/

/-- `l.revAppend r`: the attempts of `l` in reverse order, then those of
`r`.  With `l` the left siblings of a hole, nearest first, this is the
premises in their order. -/
def Atts.revAppend : {o : Bool} → {ls rs : List S.Judg} → Atts S o ls → Atts S o rs →
    Atts S o (ls.reverseAux rs)
  | _, _, _, .nil, r => r
  | _, p :: ls, rs, .cons d l, r => Atts.revAppend (ls := ls) (rs := p :: rs) l (.cons d r)

/-- The open goals of attempts kept nearest first, in the order of the
premises. -/
def Atts.goalsRev : {o : Bool} → {ls : List S.Judg} → Atts S o ls → List S.Judg
  | _, _, .nil => []
  | _, _, .cons d l => Atts.goalsRev l ++ d.goals

@[simp] theorem Atts.goalsRev_nil {o : Bool} : (Atts.nil : Atts S o []).goalsRev = [] := rfl

@[simp] theorem Atts.goalsRev_cons {o : Bool} {p : S.Judg} {ls : List S.Judg} (d : Att S o p)
    (l : Atts S o ls) : (Atts.cons d l).goalsRev = l.goalsRev ++ d.goals := rfl

/-- Kept nearest first or in the order of the premises, the attempts have as
many open goals.  (`goalsRev` appends on the left at each attempt; to count,
`goals` is the one to run.) -/
theorem Atts.length_goalsRev : {o : Bool} → {ls : List S.Judg} → (l : Atts S o ls) →
    l.goalsRev.length = l.goals.length
  | _, _, .nil => rfl
  | _, _, .cons d l => by
    simp only [Atts.goalsRev_cons, Atts.goals_cons, List.length_append, Atts.length_goalsRev l]
    omega

theorem Atts.goals_revAppend : {o : Bool} → {ls rs : List S.Judg} → (l : Atts S o ls) →
    (r : Atts S o rs) → (l.revAppend r).goals = l.goalsRev ++ r.goals
  | _, _, _, .nil, r => by simp [Atts.revAppend]
  | _, p :: ls, rs, .cons d l, r => by
    have ih := Atts.goals_revAppend (ls := ls) (rs := p :: rs) l (.cons d r)
    simp only [Atts.revAppend, Atts.goalsRev_cons, List.append_assoc]
    simpa using ih

/-! ## Crumbs -/

/-- **A crumb**: a node at `j` with the attempt at its premise number `d`
taken out; `p` is that premise. -/
structure Crumb (S : ProofSystem) (o : Bool) (d : Nat) (p j : S.Judg) where
  /-- The node's move. -/
  move : S.Move
  /-- The premises left of the hole, nearest first. -/
  lsr : List S.Judg
  /-- The premises right of the hole. -/
  rs : List S.Judg
  /-- The node's equation. -/
  h : S.step move j = .ok (lsr.reverseAux (p :: rs))
  /-- The attempts left of the hole, nearest first. -/
  left : Atts S o lsr
  /-- The attempts right of the hole. -/
  right : Atts S o rs
  /-- The hole is premise number `d`. -/
  hd : lsr.length = d

/-- Fill the hole. -/
def Crumb.plug {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o d p j) (w : Att S o p) :
    Att S o j :=
  .node c.move _ c.h (c.left.revAppend (.cons w c.right))

/-- **The derivative of attempts**: crumbs, and how to fill them. -/
@[reducible] def attDeriv (S : ProofSystem) (o : Bool) : Zip.Deriv S.Judg (Att S o) Nat where
  Crumb := Crumb S o
  plug c w := c.plug w

/-- A path of attempts: from a hole at `i` to the root at `k`. -/
abbrev Path (S : ProofSystem) (o : Bool) (ds : List Nat) (i k : S.Judg) : Type :=
  (attDeriv S o).Path ds i k

/-- A zipper of attempts. -/
abbrev Zipper (S : ProofSystem) (o : Bool) (ds : List Nat) (i k : S.Judg) : Type :=
  (attDeriv S o).Zipper ds i k

/-- A position in an attempt at `k`: a zipper, with its address and the
judgment of its focus. -/
abbrev Pos (S : ProofSystem) (o : Bool) (k : S.Judg) : Type := (attDeriv S o).Pos k

/-! ## Opening a node -/

/-- Walk `n` premises to the right, moving the attempts passed to the left
side, and take out the attempt reached. -/
def Atts.unplugAux (m : S.Move) {j : S.Judg} (d : Nat) : {o : Bool} → {lsr rs : List S.Judg} →
    S.step m j = .ok (lsr.reverseAux rs) → Atts S o lsr → Atts S o rs → (n : Nat) →
    lsr.length + n = d → Option ((p : S.Judg) × Att S o p × Crumb S o d p j)
  | _, _, _, _, _, .nil, _, _ => none
  | _, _, _, h, left, .cons w right, 0, e => some ⟨_, w, ⟨m, _, _, h, left, right, e⟩⟩
  | _, lsr, p :: rs, h, left, .cons w right, n + 1, e =>
    Atts.unplugAux m d (lsr := p :: lsr) (rs := rs) h (.cons w left) right n
      (by simp only [List.length_cons]; omega)

/-- Open the root node of an attempt at premise `d`. -/
def Att.unplug {o : Bool} {j : S.Judg} : Att S o j → (d : Nat) →
    Option ((p : S.Judg) × Att S o p × Crumb S o d p j)
  | .goal, _ => none
  | .node m _ h ds, d => Atts.unplugAux m d (lsr := []) h .nil ds d (by simp)

theorem Atts.plug_unplugAux (m : S.Move) {j : S.Judg} (d : Nat) : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m j = .ok (lsr.reverseAux rs)) → (left : Atts S o lsr) →
    (right : Atts S o rs) → (n : Nat) → (e : lsr.length + n = d) → {p : S.Judg} →
    {w : Att S o p} → {c : Crumb S o d p j} →
    Atts.unplugAux m d h left right n e = some ⟨p, w, c⟩ →
      c.plug w = Att.node m _ h (left.revAppend right)
  | _, _, _, _, _, .nil, _, _, _, _, _, hu => by simp [Atts.unplugAux] at hu
  | _, _, _, h, left, .cons w' right, 0, e, _, _, _, hu => by
    simp only [Atts.unplugAux, Option.some.injEq] at hu
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj hu
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
    rfl
  | _, lsr, p' :: rs, h, left, .cons w' right, n + 1, e, _, _, _, hu => by
    simp only [Atts.unplugAux] at hu
    exact Atts.plug_unplugAux m d (lsr := p' :: lsr) (rs := rs) h (.cons w' left) right n _ hu

/-- Append, for attempts kept nearest first: `l`, then `a`. -/
def Atts.append : {o : Bool} → {ls as : List S.Judg} → Atts S o ls → Atts S o as →
    Atts S o (ls ++ as)
  | _, _, _, .nil, a => a
  | _, _, _, .cons d l, a => .cons d (Atts.append l a)

/-- Walking past the attempts of `l` moves them to the left side. -/
theorem Atts.unplugAux_revAppend (m : S.Move) {j : S.Judg} (d : Nat) : {o : Bool} →
    {ls as rs : List S.Judg} → (l : Atts S o ls) → (acc : Atts S o as) → (rest : Atts S o rs) →
    (n c : Nat) → c = n + ls.length →
    (h₁ : S.step m j = .ok (as.reverseAux (ls.reverseAux rs))) →
    (h₂ : S.step m j = .ok ((ls ++ as).reverseAux rs)) →
    (e₁ : as.length + c = d) → (e₂ : (ls ++ as).length + n = d) →
      Atts.unplugAux m d h₁ acc (l.revAppend rest) c e₁ =
        Atts.unplugAux m d h₂ (l.append acc) rest n e₂
  | _, _, _, _, .nil, acc, rest, n, c, hc, h₁, h₂, e₁, e₂ => by
    have hc' : c = n := hc
    subst hc'
    rfl
  | _, _, _, _, .cons x l, acc, rest, n, c, hc, h₁, h₂, e₁, e₂ => by
    have ih := Atts.unplugAux_revAppend m d l acc (.cons x rest) (n + 1) c
      (by simp only [List.length_cons] at hc; omega) h₁ h₂ e₁
      (by simp only [List.length_append, List.length_cons] at e₂ ⊢; omega)
    exact ih

private theorem Atts.cons_heq_tail {o : Bool} {p : S.Judg} {ps ps' : List S.Judg} (e : ps = ps')
    (d : Att S o p) {ds : Atts S o ps} {ds' : Atts S o ps'} (h : HEq ds ds') :
    HEq (Atts.cons d ds) (Atts.cons d ds') := by
  subst e
  cases h
  rfl

private theorem Atts.append_nil_heq : {o : Bool} → {ls : List S.Judg} → (l : Atts S o ls) →
    HEq (l.append .nil) l
  | _, _, .nil => HEq.rfl
  | _, _, .cons d l => Atts.cons_heq_tail (List.append_nil _) d (Atts.append_nil_heq l)

/-- Opening undoes filling. -/
theorem Crumb.unplug_plug {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o d p j)
    (w : Att S o p) : (c.plug w).unplug d = some ⟨p, w, c⟩ := by
  obtain ⟨m, lsr, rs, h, left, right, hd⟩ := c
  subst hd
  show Atts.unplugAux m lsr.length (lsr := []) h .nil (left.revAppend (.cons w right))
    lsr.length _ = _
  have key : ∀ (as : List S.Judg) (acc : Atts S o as), as = lsr → HEq acc left →
      ∀ (h₂ : S.step m j = .ok (as.reverseAux (p :: rs))) (e₂ : as.length + 0 = lsr.length),
      Atts.unplugAux m lsr.length h₂ acc (.cons w right) 0 e₂ =
        some ⟨p, w, ⟨m, lsr, rs, h, left, right, rfl⟩⟩ := by
    intro as acc has hacc h₂ e₂
    subst has
    cases hacc
    rfl
  rw [Atts.unplugAux_revAppend m lsr.length left .nil (.cons w right) 0 lsr.length
    (by simp) h (by simpa using h) (by simp) (by simp)]
  exact key _ _ (List.append_nil _) (Atts.append_nil_heq left) _ _

/-! ## The next premise -/

/-- **The hole one premise to the right**: the attempt that filled the hole
joins the left side, and the first attempt on the right is taken out.  One
step, and the node's equation serves unchanged. -/
def Crumb.stepRight {o : Bool} {d : Nat} {p j : S.Judg} : Crumb S o d p j → Att S o p →
    Option ((p' : S.Judg) × Att S o p' × Crumb S o (d + 1) p' j)
  | ⟨_, _, _, _, _, .nil, _⟩, _ => none
  | ⟨m, lsr, _ :: rs, h, left, .cons w' right, hd⟩, w =>
    some ⟨_, w', ⟨m, p :: lsr, rs, h, .cons w left, right, congrArg (· + 1) hd⟩⟩

/-- **The hole one premise to the left**: there is one, since the hole is
not premise number 0. -/
def Crumb.stepLeft {o : Bool} {d : Nat} {p j : S.Judg} : Crumb S o (d + 1) p j → Att S o p →
    (p' : S.Judg) × Att S o p' × Crumb S o d p' j
  | ⟨_, _, _, _, .nil, _, hd⟩, _ => nomatch hd
  | ⟨m, _ :: lsr, rs, h, .cons w' left, right, hd⟩, w =>
    ⟨_, w', ⟨m, lsr, p :: rs, h, left, .cons w right, Nat.succ.inj hd⟩⟩

theorem Crumb.plug_stepRight {o : Bool} {d : Nat} {p p' j : S.Judg} {c : Crumb S o d p j}
    {w : Att S o p} {w' : Att S o p'} {c' : Crumb S o (d + 1) p' j}
    (h : c.stepRight w = some ⟨p', w', c'⟩) : c'.plug w' = c.plug w := by
  obtain ⟨m, lsr, rs, hs, left, right, hd⟩ := c
  cases right with
  | nil => simp [Crumb.stepRight] at h
  | cons w₀ right =>
    simp only [Crumb.stepRight, Option.some.injEq] at h
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
    rfl

theorem Crumb.plug_stepLeft {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o (d + 1) p j)
    (w : Att S o p) : (c.stepLeft w).2.2.plug (c.stepLeft w).2.1 = c.plug w := by
  obtain ⟨m, lsr, rs, hs, left, right, hd⟩ := c
  cases left with
  | nil => exact nomatch hd
  | cons w₀ left => rfl

/-- Right, then left, returns. -/
theorem Crumb.stepLeft_stepRight {o : Bool} {d : Nat} {p p' j : S.Judg} {c : Crumb S o d p j}
    {w : Att S o p} {w' : Att S o p'} {c' : Crumb S o (d + 1) p' j}
    (h : c.stepRight w = some ⟨p', w', c'⟩) : c'.stepLeft w' = ⟨p, w, c⟩ := by
  obtain ⟨m, lsr, rs, hs, left, right, hd⟩ := c
  cases right with
  | nil => simp [Crumb.stepRight] at h
  | cons w₀ right =>
    simp only [Crumb.stepRight, Option.some.injEq] at h
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
    rfl

/-- Left, then right, returns. -/
theorem Crumb.stepRight_stepLeft {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o (d + 1) p j)
    (w : Att S o p) : (c.stepLeft w).2.2.stepRight (c.stepLeft w).2.1 = some ⟨p, w, c⟩ := by
  obtain ⟨m, lsr, rs, hs, left, right, hd⟩ := c
  cases left with
  | nil => exact nomatch hd
  | cons w₀ left => rfl

/-- **The step to the left is the node opened again one premise earlier.** -/
theorem Crumb.unplug_plug_pred {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o (d + 1) p j)
    (w : Att S o p) : (c.plug w).unplug d = some (c.stepLeft w) := by
  rw [← Crumb.plug_stepLeft c w, Crumb.unplug_plug]

/-- **The step to the right is the node opened again one premise later**; and
there is no step where the node has no later premise. -/
theorem Crumb.unplug_plug_succ {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o d p j)
    (w : Att S o p) : (c.plug w).unplug (d + 1) = c.stepRight w := by
  cases hr : c.stepRight w with
  | some x =>
    obtain ⟨p', w', c'⟩ := x
    rw [← Crumb.plug_stepRight hr, Crumb.unplug_plug]
  | none =>
    obtain ⟨m, lsr, rs, h, left, right, hd⟩ := c
    subst hd
    cases right with
    | cons w' right => simp [Crumb.stepRight] at hr
    | nil =>
      show Atts.unplugAux m (lsr.length + 1) (lsr := []) h .nil (left.revAppend (.cons w .nil))
        (lsr.length + 1) _ = none
      rw [Atts.unplugAux_revAppend m (lsr.length + 1) left .nil (.cons w .nil) 1 (lsr.length + 1)
        (by omega) h (by simpa using h) (by simp) (by simp)]
      rfl

/-! ## The instances, and the goals around a hole -/

-- `no_index`: for a system declared as an `abbrev`, `S.Judg` unfolds to the
-- instance's own type, and would not be found under the key `S.Judg`.  The
-- instance is found by the family, `Att S o`.
instance (S : ProofSystem) (o : Bool) :
    Zip.Deriv.Unplug (I := no_index S.Judg) (no_index (attDeriv S o)) where
  unplug w d := Att.unplug w d
  Canon _ := True
  plug_unplug := by
    intro j w d i w' c hu
    cases w with
    | goal => simp [Att.unplug] at hu
    | node m ps h ds => exact Atts.plug_unplugAux m d (lsr := []) h .nil ds d _ hu
  unplug_plug := fun {_ _ _ c} w _ => Crumb.unplug_plug c w
  canon_unplug := fun _ => trivial

/-- **The next premise, on either side**: the zipper's `left` and `right`
for attempts, in one step each. -/
instance (S : ProofSystem) (o : Bool) :
    Zip.Deriv.Sibling (I := no_index S.Judg) (no_index (attDeriv S o)) where
  left := @fun d _ _ c w =>
    match d, c with
    | 0, _ => none
    | d + 1, c => some ⟨d, (c.stepLeft w).1, (c.stepLeft w).2.1, (c.stepLeft w).2.2⟩
  right := @fun d _ _ c w => (c.stepRight w).map fun x => ⟨d + 1, x.1, x.2.1, x.2.2⟩
  plug_left := by
    intro d d' i i' j c w w' c' h
    cases d with
    | zero => cases h
    | succ d =>
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj h
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj (eq_of_heq hrest)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
      exact Crumb.plug_stepLeft c w
  plug_right := by
    intro d d' i i' j c w w' c' h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨p', w₀, c₀⟩, hs, he⟩ := h
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj he
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj (eq_of_heq hrest)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
    exact Crumb.plug_stepRight hs
  right_left := by
    intro d d' i i' j c w w' c' h
    cases d with
    | zero => cases h
    | succ d =>
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj h
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj (eq_of_heq hrest)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
      show ((c.stepLeft w).2.2.stepRight (c.stepLeft w).2.1).map _ = _
      rw [Crumb.stepRight_stepLeft c w]
      rfl
  left_right := by
    intro d d' i i' j c w w' c' h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨p', w₀, c₀⟩, hs, he⟩ := h
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj he
    obtain ⟨rfl, hrest⟩ := Sigma.mk.inj (eq_of_heq hrest)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hrest)
    show some _ = _
    rw [Crumb.stepLeft_stepRight hs]

/-- Every path of attempts is canonical. -/
theorem Path.canon {o : Bool} : {ds : List Nat} → {i k : S.Judg} → (p : Path S o ds i k) →
    Zip.Deriv.Path.Canon p
  | _, _, _, .top => trivial
  | _, _, _, .cons _ p => ⟨trivial, Path.canon p⟩

/-- The open goals left of the hole, over the whole attempt. -/
def Path.goalsL {o : Bool} : {ds : List Nat} → {i k : S.Judg} → Path S o ds i k → List S.Judg
  | _, _, _, .top => []
  | _, _, _, .cons c p => Path.goalsL p ++ c.left.goalsRev

/-- The open goals right of the hole, over the whole attempt. -/
def Path.goalsR {o : Bool} : {ds : List Nat} → {i k : S.Judg} → Path S o ds i k → List S.Judg
  | _, _, _, .top => []
  | _, _, _, .cons c p => c.right.goals ++ Path.goalsR p

@[simp] theorem Crumb.goals_plug {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o d p j)
    (w : Att S o p) : (c.plug w).goals = c.left.goalsRev ++ w.goals ++ c.right.goals := by
  simp [Crumb.plug, Atts.goals_revAppend, List.append_assoc]

/-- **The goals of a plugged path**: those left of the hole, those of the
filling, those right of the hole. -/
theorem Path.goals_plug {o : Bool} : {ds : List Nat} → {i k : S.Judg} → (p : Path S o ds i k) →
    (d : Att S o i) → (Zip.Deriv.Path.plug p d).goals = Path.goalsL p ++ d.goals ++ Path.goalsR p
  | _, _, _, .top, d => by simp [Path.goalsL, Path.goalsR]
  | _, _, _, .cons c p, d => by
    show (Zip.Deriv.Path.plug p (c.plug d)).goals = _
    rw [Path.goals_plug p (c.plug d)]
    simp [Path.goalsL, Path.goalsR, List.append_assoc]

/-- **The open goals before the focus in its node**: the number of open
goals of the premises left of the focus, in the node the focus is a premise
of.  Read off the nearest crumb (`Zip.Deriv.Zipper.crumb`). -/
def goalsBefore {o : Bool} {d : Nat} {ds : List Nat} {i k : S.Judg}
    (z : Zipper S o (d :: ds) i k) : Nat :=
  (Zip.Deriv.Zipper.crumb z).left.goals.length

/-- The goals left of the focus are those left of its node, and those before
it in its node. -/
theorem length_goalsL {o : Bool} {d : Nat} {ds : List Nat} {i k : S.Judg}
    (z : Zipper S o (d :: ds) i k) :
    (Path.goalsL z.path).length = (Path.goalsL z.up.2.path).length + goalsBefore z := by
  rw [Zip.Deriv.Zipper.path_eq_cons z]
  simp only [Path.goalsL, List.length_append, goalsBefore, Atts.length_goalsRev]

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
