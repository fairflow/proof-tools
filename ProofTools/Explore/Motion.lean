/-
# `ProofTools.Explore.Motion`: moving the cursor in an attempt that is built

A cursor (`ProofTools.Explore.Cursor`) is a position in an attempt with its
count of the open goals left of the focus.  `run` moves it with `seek`, to
an open goal.  This file gives it the other motions, so that an attempt
that is built (by a script, by the tactic, by a search) can be walked:

    inductive Motion
      | up            to the node this one is a premise of
      | down (i)      to premise number `i` of the focus, numbered from 0
      | left          to the premise before this one, of the same node
      | right         to the premise after it
      | top           to the root
      | goal (k)      to open goal `k` of the whole attempt (`Cursor.seek`)

    Cursor.move m c      one motion: the cursor reached, if there is one
    Cursor.whyNot m c    why not, as text
    Cursor.moves c ms    motions in turn: the cursor reached, or the number
                         of the first motion that fails and why
    Cursor.trail n c ms  the same with every position kept: the one loop
                         over motions, which the others are read off

**The motions are the moves of the zipper** (`ProofTools/Zipper.lean`), with
the cursor's count kept beside them: `Cursor.up` is its `up`, `Cursor.down`
its `down`, `left` and `right` its one step to a sibling (`Cursor.sibling`),
`top` its `ofRoot` of `toRoot`, the address its `addr`.  The count changes
by `goalsBefore`, the open goals before the focus in its node, read off the
zipper's nearest crumb.

A motion changes the position and nothing else (PROVED, from the zipper's
laws `toRoot_up`, `toRoot_down`, `up_down`, `up_left`, `up_right`; `c.Ok`
says that `c.left` is the number of open goals left of the focus):

    c.Ok → c.move m = some c'   →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.move_some)
    c.Ok → c.moves ms = .ok c'  →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.moves_ok)
    c.down i = some c'  →  c'.up = some c                            (Cursor.up_down)

What the motions do on the crumbs is PROVED of them (`Cursor.up_top`,
`Cursor.up_cons`, `Cursor.down_eq`), and the one step to a sibling is up,
then down again at the premise number before or after:

    c.move .right = match c.pos.ds with
      | [] => none | d :: _ => c.up.bind (·.down (d + 1))            (Cursor.move_right)
    c.move .left = match c.pos.ds with
      | [] => none | 0 :: _ => none | (d + 1) :: _ => c.up.bind (·.down d)   (Cursor.move_left)

`Cursor.motions c` lists the motions that can be made from `c` (PROVED:
`m ∈ c.motions → ∃ c', c.move m = some c'`, `Cursor.motions_move`); `#walk`
offers them.

The name `Cursor.left` is the count of goals, so the motions to a sibling
are `Cursor.move .left` and `Cursor.move .right`; the function behind both
is `Cursor.sibling`.

A derivation (`Der S j`) is walked as an attempt, through `Att.toAtt`
(`Cursor.ofAtt`).

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Cursor

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-- **A motion of the cursor.** -/
inductive Motion where
  /-- To the node this one is a premise of. -/
  | up
  /-- To premise number `i` of the focus, numbered from 0. -/
  | down (i : Nat)
  /-- To the premise before this one, of the same node. -/
  | left
  /-- To the premise after this one, of the same node. -/
  | right
  /-- To the root. -/
  | top
  /-- To open goal `k` of the whole attempt, numbered from 0. -/
  | goal (k : Nat)
  deriving DecidableEq, Repr

/-- A motion as it is written. -/
def Motion.text : Motion → String
  | .up => "up"
  | .down i => s!"down {i}"
  | .left => "left"
  | .right => "right"
  | .top => "top"
  | .goal k => s!"goal {k}"

/-- The premises of the node at the root of an attempt; none for an open
goal. -/
def Att.premises {o : Bool} {j : S.Judg} : Att S o j → List S.Judg
  | .goal => []
  | .node _ ps _ _ => ps

/-- The cursor at the root of an attempt or of a derivation. -/
def Cursor.ofAtt {o : Bool} {j : S.Judg} (d : Att S o j) : Cursor S j := .ofRoot d.toAtt

/-- The attempt at the focus. -/
def Cursor.focus {j : S.Judg} (c : Cursor S j) : Att S true c.pos.i := c.pos.z.focus

/-- The address of the focus: the premise numbers from the root. -/
def Cursor.addr {j : S.Judg} (c : Cursor S j) : List Nat := c.pos.z.addr

/-! ## The motions -/

/-- **Up**: to the node the focus is a premise of (the zipper's `up`).  The
open goals of the premises before the focus are no longer left of it. -/
def Cursor.up {j : S.Judg} : Cursor S j → Option (Cursor S j)
  | ⟨⟨[], _, _⟩, _⟩ => none
  | ⟨⟨_ :: _, _, z⟩, l⟩ => some ⟨⟨_, _, z.up.2⟩, l - goalsBefore z⟩

/-- **Down** to premise number `i` of the focus (the zipper's `down`).  The
open goals of the premises before it are now left of the focus. -/
def Cursor.down {j : S.Judg} (i : Nat) (c : Cursor S j) : Option (Cursor S j) :=
  (c.pos.z.down i).map fun x => ⟨⟨_, _, x.2⟩, c.left + goalsBefore x.2⟩

/-- **To the premise beside the focus**, of the same node: the one after it
(`right`) or the one before it, by one step of the zipper (its `right`, its
`left`).  The count loses the goals before the old focus in the node and
gains those before the new one. -/
def Cursor.sibling {j : S.Judg} (right : Bool) : Cursor S j → Option (Cursor S j)
  | ⟨⟨[], _, _⟩, _⟩ => none
  | ⟨⟨_ :: _, _, z⟩, l⟩ =>
    (if right then z.right else z.left).map fun x =>
      ⟨⟨_, _, x.2.2⟩, l - goalsBefore z + goalsBefore x.2.2⟩

/-- **To the root.** -/
def Cursor.top {j : S.Judg} (c : Cursor S j) : Cursor S j := .ofRoot c.toRoot

/-- **One motion.** -/
def Cursor.move {j : S.Judg} (m : Motion) (c : Cursor S j) : Option (Cursor S j) :=
  match m with
  | .up => c.up
  | .down i => c.down i
  | .left => c.sibling false
  | .right => c.sibling true
  | .top => some c.top
  | .goal k => c.seek k

/-- Why a motion cannot be made, as text. -/
def Cursor.whyNot {j : S.Judg} (m : Motion) (c : Cursor S j) : String :=
  let n := c.pos.z.focus.premises.length
  match m with
  | .up => "the focus is the root"
  | .down i =>
    if c.pos.z.focus.isGoal then "the focus is an open goal: it has no premises"
    else if n = 0 then "the move at the focus has no premises"
    else s!"the focus has no premise {i}: its premises are numbered 0 to {n - 1}"
  | .left =>
    match c.pos.ds with
    | [] => "the focus is the root"
    | _ => "the focus is the first premise of its node"
  | .right =>
    match c.pos.ds with
    | [] => "the focus is the root"
    | _ => "the focus is the last premise of its node"
  | .top => "the motion can be made"
  | .goal k => s!"there is no goal {k}"

/-- **What motions in turn leave behind**: the cursors passed, the first
first; the cursor reached, which is the last one before a motion that cannot
be made; and that motion's number and why, if there is one. -/
structure Trail (S : ProofSystem) (j : S.Judg) where
  /-- The cursors passed, the first first. -/
  passed : List (Cursor S j)
  /-- The cursor reached. -/
  last : Cursor S j
  /-- The number of the motion that cannot be made, and why. -/
  failed : Option (Nat × String)

/-- **Motions in turn, every position kept**; `n` is the number of the first
motion.  The one loop over motions: `Cursor.moves`, the views of `#walk`
(`walkViews`) and the panel's focus (`Cursor.movesWhile`) are read off it. -/
def Cursor.trail {j : S.Judg} : Nat → Cursor S j → List Motion → Trail S j
  | _, c, [] => ⟨[], c, none⟩
  | n, c, m :: ms =>
    match c.move m with
    | some c' => let t := Cursor.trail (n + 1) c' ms; ⟨c :: t.passed, t.last, t.failed⟩
    | none => ⟨[], c, some (n, c.whyNot m)⟩

/-- **Motions in turn**: the cursor reached, or the number of the first
motion that cannot be made (from `n`) and why. -/
def Cursor.movesFrom {j : S.Judg} (n : Nat) (c : Cursor S j) (ms : List Motion) :
    Except (Nat × String) (Cursor S j) :=
  let t := Cursor.trail n c ms
  match t.failed with
  | none => .ok t.last
  | some e => .error e

theorem Cursor.movesFrom_nil {j : S.Judg} (n : Nat) (c : Cursor S j) :
    Cursor.movesFrom n c [] = .ok c := rfl

theorem Cursor.movesFrom_cons {j : S.Judg} (n : Nat) (c : Cursor S j) (m : Motion)
    (ms : List Motion) :
    Cursor.movesFrom n c (m :: ms) =
      match c.move m with
      | some c' => Cursor.movesFrom (n + 1) c' ms
      | none => .error (n, c.whyNot m) := by
  simp only [Cursor.movesFrom, Cursor.trail]
  cases c.move m <;> rfl

/-- **Motions in turn**, numbered from 0. -/
def Cursor.moves {j : S.Judg} (c : Cursor S j) (ms : List Motion) :
    Except (Nat × String) (Cursor S j) := Cursor.movesFrom 0 c ms

/-! ## A motion changes the position and nothing else -/

theorem Cursor.up_some {j : S.Judg} {c c' : Cursor S j} (hc : c.Ok) (h : c.up = some c') :
    c'.toRoot = c.toRoot ∧ c'.Ok := by
  obtain ⟨⟨ds, i, z⟩, l⟩ := c
  cases ds with
  | nil => cases h
  | cons d ds =>
    simp only [Cursor.up, Option.some.injEq] at h
    subst h
    refine ⟨Zip.Deriv.Zipper.toRoot_up z, ?_⟩
    have hg := length_goalsL z
    unfold Cursor.Ok at hc ⊢
    simp only at hc ⊢
    omega

theorem Cursor.down_some {j : S.Judg} {i : Nat} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.down i = some c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  simp only [Cursor.down, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  refine ⟨Zip.Deriv.Zipper.toRoot_down hx, ?_⟩
  have hg := length_goalsL x.2
  have hup : (Path.goalsL x.2.up.2.path).length = (Path.goalsL c.pos.z.path).length :=
    congrArg (fun y : (i : S.Judg) × Zipper S true c.pos.ds i j => (Path.goalsL y.2.path).length)
      (Zip.Deriv.Zipper.up_down hx)
  unfold Cursor.Ok at hc ⊢
  simp only
  omega

/-- **Up undoes down.** -/
theorem Cursor.up_down {j : S.Judg} {i : Nat} {c c' : Cursor S j} (h : c.down i = some c') :
    c'.up = some c := by
  simp only [Cursor.down, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  simp only [Cursor.up, Nat.add_sub_cancel]
  exact congrArg (fun y : (i : S.Judg) × Zipper S true c.pos.ds i j =>
    some (⟨⟨c.pos.ds, y.1, y.2⟩, c.left⟩ : Cursor S j)) (Zip.Deriv.Zipper.up_down hx)

/-- A step to the premise beside the focus keeps the attempt, and the count
of goals stays right. -/
theorem Cursor.sibling_some {j : S.Judg} {r : Bool} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.sibling r = some c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  obtain ⟨⟨ds, i, z⟩, l⟩ := c
  cases ds with
  | nil => cases h
  | cons d ds =>
    simp only [Cursor.sibling, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    have hup : x.2.2.up = z.up := by
      cases r
      · exact Zip.Deriv.Zipper.up_left hx
      · exact Zip.Deriv.Zipper.up_right hx
    refine ⟨?_, ?_⟩
    · show x.2.2.toRoot = z.toRoot
      rw [← Zip.Deriv.Zipper.toRoot_up x.2.2, ← Zip.Deriv.Zipper.toRoot_up z, hup]
    · have hg := length_goalsL x.2.2
      have hg' := length_goalsL z
      rw [hup] at hg
      unfold Cursor.Ok at hc ⊢
      simp only at hc ⊢
      omega

/-- `Cursor.up` on the crumbs: at the root there is no node above. -/
theorem Cursor.up_top {j : S.Judg} (w : Att S true j) (l : Nat) :
    Cursor.up ⟨⟨[], j, ⟨w, .top⟩⟩, l⟩ = none := rfl

/-- `Cursor.up` on the crumbs: the nearest crumb is filled with the focus,
and the open goals of the premises before the focus leave the count. -/
theorem Cursor.up_cons {j i i' : S.Judg} {d : Nat} {ds : List Nat} (w : Att S true i)
    (cr : Crumb S true d i i') (p : Path S true ds i' j) (l : Nat) :
    Cursor.up ⟨⟨d :: ds, i, ⟨w, .cons cr p⟩⟩, l⟩ =
      some ⟨⟨ds, i', ⟨cr.plug w, p⟩⟩, l - cr.left.goalsRev.length⟩ := by
  rw [Atts.length_goalsRev]
  rfl

/-- `Cursor.down` on the crumbs: the node at the focus is opened at premise
`i`, and the open goals of the premises before it join the count. -/
theorem Cursor.down_eq {j : S.Judg} (i : Nat) (c : Cursor S j) :
    c.down i =
      match Att.unplug c.pos.z.focus i with
      | none => none
      | some ⟨p, w, cr⟩ =>
        some ⟨⟨i :: c.pos.ds, p, ⟨w, .cons cr c.pos.z.path⟩⟩, c.left + cr.left.goalsRev.length⟩ := by
  show Option.map _ (Option.map _ (Att.unplug c.pos.z.focus i)) = _
  cases Att.unplug c.pos.z.focus i with
  | none => rfl
  | some x =>
    obtain ⟨p, w, cr⟩ := x
    simp only [Option.map_some, Atts.length_goalsRev]
    rfl

/-- **The step to the premise after the focus is up, then down to the next
premise number**: the one step of the zipper reaches what going up and
opening the node again reaches, with the same count. -/
theorem Cursor.move_right {j : S.Judg} (c : Cursor S j) :
    c.move .right =
      match c.pos.ds with
      | [] => none
      | d :: _ => c.up.bind (·.down (d + 1)) := by
  obtain ⟨⟨ds, i, ⟨w, p⟩⟩, l⟩ := c
  cases p with
  | top => rfl
  | cons cr p =>
    show (Option.map _ (Option.map _ (Option.map _ (cr.stepRight w)))) =
      Option.map _ (Option.map _ (Att.unplug (cr.plug w) _))
    rw [Crumb.unplug_plug_succ]
    cases cr.stepRight w <;> rfl

/-- **The step to the premise before the focus is up, then down to the
premise number before**; there is none before premise 0. -/
theorem Cursor.move_left {j : S.Judg} (c : Cursor S j) :
    c.move .left =
      match c.pos.ds with
      | [] => none
      | 0 :: _ => none
      | (d + 1) :: _ => c.up.bind (·.down d) := by
  obtain ⟨⟨ds, i, ⟨w, p⟩⟩, l⟩ := c
  cases p with
  | top => rfl
  | @cons d ds _ _ _ cr p =>
    cases d with
    | zero => rfl
    | succ d =>
      show _ = Option.map _ (Option.map _ (Att.unplug (cr.plug w) _))
      rw [Crumb.unplug_plug_pred]
      rfl

/-- **(L1), (L2) A motion keeps the attempt, and the count of goals stays
right.** -/
theorem Cursor.move_some {j : S.Judg} {m : Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.move m = some c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  cases m with
  | up => exact Cursor.up_some hc h
  | down i => exact Cursor.down_some hc h
  | left => exact Cursor.sibling_some hc h
  | right => exact Cursor.sibling_some hc h
  | top =>
    simp only [Cursor.move, Option.some.injEq] at h
    subst h
    exact ⟨rfl, Cursor.ok_ofRoot _⟩
  | goal k =>
    obtain ⟨e, _, _, o⟩ := Cursor.seek_some hc h
    exact ⟨e, o⟩

theorem Cursor.movesFrom_ok {j : S.Judg} : ∀ (ms : List Motion) (n : Nat) {c c' : Cursor S j},
    c.Ok → Cursor.movesFrom n c ms = .ok c' → c'.toRoot = c.toRoot ∧ c'.Ok
  | [], _, _, _, hc, h => by
    simp only [Cursor.movesFrom_nil, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, hc⟩
  | m :: ms, n, c, c', hc, h => by
    rw [Cursor.movesFrom_cons] at h
    split at h
    · next c₁ h₁ =>
      obtain ⟨e₁, o₁⟩ := Cursor.move_some hc h₁
      obtain ⟨e₂, o₂⟩ := Cursor.movesFrom_ok ms (n + 1) o₁ h
      exact ⟨e₂.trans e₁, o₂⟩
    · cases h

/-- **Motions in turn keep the attempt, and the count of goals stays
right.** -/
theorem Cursor.moves_ok {j : S.Judg} {ms : List Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.moves ms = .ok c') : c'.toRoot = c.toRoot ∧ c'.Ok :=
  Cursor.movesFrom_ok ms 0 hc h

/-- The cursor at the root of an attempt or of a derivation counts right. -/
theorem Cursor.ok_ofAtt {o : Bool} {j : S.Judg} (d : Att S o j) : (Cursor.ofAtt d).Ok :=
  Cursor.ok_ofRoot _

/-! ## The motions that can be made -/

/-- **The motions that can be made from a position**, in the order they are
offered: `down i` for each premise of the focus; `up`, `left`, `right`;
`top`, unless the focus is the root; `goal k` for each open goal of the
attempt, unless the focus is that goal.  Each is kept only if `Cursor.move`
makes it. -/
def Cursor.motions {j : S.Judg} (c : Cursor S j) : List Motion :=
  let downs := (List.range c.pos.z.focus.premises.length).map Motion.down
  let top := if c.pos.ds.isEmpty then [] else [Motion.top]
  let goals := ((List.range c.toRoot.goals.length).filter fun k =>
    !(c.pos.z.focus.isGoal && k == c.left)).map Motion.goal
  (downs ++ [Motion.up, Motion.left, Motion.right] ++ top ++ goals).filter fun m => (c.move m).isSome

/-- **A motion of `Cursor.motions` can be made.** -/
theorem Cursor.motions_move {j : S.Judg} {m : Motion} {c : Cursor S j} (h : m ∈ c.motions) :
    ∃ c', c.move m = some c' :=
  Option.isSome_iff_exists.mp (List.mem_filter.mp h).2

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
