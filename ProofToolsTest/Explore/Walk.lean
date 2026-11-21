/-
Tests of `ProofTools.Explore.Motion` and `ProofTools.Explore.Walk` on the
example calculus: the view at the root and after motions, on an attempt
with an open goal and on a derivation; a walk written over several lines,
with a view at each; every motion; every way a motion can fail, with its
reason; an attempt named by a term; `walkText` as a function; the laws on
an example; the motions offered after a walk, and the edit a click makes.
Each message is pinned by `#guard_msgs`.
-/
import ProofToolsTest.Explore.Tactic

namespace ProofToolsTest.Explore.WalkTest

open ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.TacticTest

-- The motions offered after a walk have their own section, the last; until
-- then the offer is off, so that a test pins the views alone.
set_option walk.offer false

/-! ## The view

`swapAtt` is an attempt at `(p ∧ q) → (q ∧ p)` with one goal open; `swap`
is a derivation of it. -/

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
-/
#guard_msgs in
#walk swapAtt

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: ? p0, p1, (p0 ∧ p1) ⊢ p1
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
  at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all
-/
#guard_msgs in
#walk swapAtt down 0 down 0

-- a closed premise right of the open goal: the goal is left of the focus
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; open goals: 0 under the focus, 1 left of it, 1 in all
-/
#guard_msgs in
#walk swapAtt down 0 down 0 down 1

/-! ## Every motion

Commas may separate the motions.  `left` and `right` pass between the
premises of one node, `top` goes to the root, `goal k` to an open goal. -/

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
  at 0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
#walk swapAtt down 0, down 0, down 1, left

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; open goals: 0 under the focus, 1 left of it, 1 in all
-/
#guard_msgs in
#walk swapAtt down 0, down 0, down 1, left, right

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
-/
#guard_msgs in
#walk swapAtt down 0, down 0, down 1, up, top

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
  at 0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
#walk swapAtt goal 0

/-! ## A walk over several lines: a view at each line -/

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [closed]
  at the root: 1 premise; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
>   (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      0: p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR   [closed]
  at 0: 1 premise; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: p0, p1, (p0 ∧ p1) ⊢ p1   by ax   [closed]
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
  at 0.0: 2 premises; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: p0, p1, (p0 ∧ p1) ⊢ p1   by ax   [closed]
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
  at 0.0: 2 premises; no open goals
-/
#guard_msgs in
#walk swap
  down 0
  down 0
  down 1
  up

/-! ## A motion that cannot be made

An error at the motion, with the reason; the view before it is shown. -/

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
error: #walk: this motion cannot be made: the focus is the root
-/
#guard_msgs in
#walk swapAtt down 0 up up

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
error: #walk: this motion cannot be made: the focus has no premise 3: its premises are numbered 0 to 0
-/
#guard_msgs in
#walk swapAtt down 3

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
  at 0.0.0: open goal 0; 1 open in all
---
error: #walk: this motion cannot be made: the focus is an open goal: it has no premises
-/
#guard_msgs in
#walk swapAtt goal 0 down 0

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; open goals: 0 under the focus, 1 left of it, 1 in all
---
error: #walk: this motion cannot be made: the move at the focus has no premises
-/
#guard_msgs in
#walk swapAtt down 0 down 0 down 1 down 0

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
error: #walk: this motion cannot be made: there is no goal 4
-/
#guard_msgs in
#walk swapAtt goal 4

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
  at 0.0.0: open goal 0; 1 open in all
---
error: #walk: this motion cannot be made: the focus is the first premise of its node
-/
#guard_msgs in
#walk swapAtt down 0 down 0 down 0 left

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; open goals: 0 under the focus, 1 left of it, 1 in all
---
error: #walk: this motion cannot be made: the focus is the last premise of its node
-/
#guard_msgs in
#walk swapAtt down 0 down 0 down 1 right

/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
error: #walk: this motion cannot be made: the focus is the root
-/
#guard_msgs in
#walk swapAtt left

/-! ## An attempt named by a term: what a script built -/

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
>   ? (p0 ∧ p1) ⊢ (p1 ∧ p0)
  at 0: open goal 0; 1 open in all
-/
#guard_msgs in
#walk (run IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) [⟨0, .impR⟩]).att goal 0

/-! ## As functions -/

#guard (walkText swap [.down 0, .down 0, .down 1]).toOption.isSome
#guard (walkText swap [.down 0, .up, .up]) matches .error (2, _)
#guard ((Cursor.ofAtt swap).moves [.down 0, .down 0, .down 1]).toOption.map (·.addr)
  == some [0, 0, 1]

-- a motion keeps the attempt (`Cursor.move_some`), here by running
#guard ((Cursor.ofAtt swapAtt).moves [.down 0, .down 0, .down 1, .left, .up]).toOption.map
  (·.toRoot.script) == some swapAtt.script
-- the count of goals stays right: at the closed premise, the open goal is left of the focus
#guard ((Cursor.ofAtt swapAtt).moves [.down 0, .down 0, .down 1]).toOption.map (·.left) == some 1
-- up undoes down (`Cursor.up_down`)
#guard (((Cursor.ofAtt swap).down 0).bind (·.up)).map (·.addr) == some []

/-! ## Walking by clicking: the motions offered

After the last view, `#walk` offers the motions that can be made from the
position reached: `down i` for each premise, `up`, `left`, `right`, `top`,
`goal k`.  A click writes the motion after the last one. -/

set_option walk.offer true

-- at the root of an attempt: no `up`, no `top`
/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
info: Motions from here:
  [apply] down 0
  [apply] goal 0
-/
#guard_msgs in
#walk swapAtt

-- at an open goal: that goal is not offered
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
  at 0.0.0: open goal 0; 1 open in all
---
info: Motions from here:
  [apply] up
  [apply] right
  [apply] top
-/
#guard_msgs in
#walk swapAtt goal 0

-- nothing to offer: an open goal at the root
/--
info: > ?  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))
  at the root: open goal 0; 1 open in all
-/
#guard_msgs in
#walk (run IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) []).att

-- a motion that cannot be made: the error, and no offer
/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [1 open]
  at the root: 1 premise; open goals: 1 under the focus, 0 left of it, 1 in all
---
error: #walk: this motion cannot be made: the focus has no premise 3: its premises are numbered 0 to 0
-/
#guard_msgs in
#walk swapAtt down 3

section Edits

open Lean Elab Command

/-- The suggestions recorded in an info tree. -/
partial def editsOf : InfoTree → Array Lean.Meta.Tactic.TryThis.TryThisInfo →
    Array Lean.Meta.Tactic.TryThis.TryThisInfo
  | .context _ t, a => editsOf t a
  | .node i ts, a =>
    let a := match i with
      | .ofCustomInfo ci =>
        match ci.value.get? Lean.Meta.Tactic.TryThis.TryThisInfo with
        | some x => a.push x
        | none => a
      | _ => a
    ts.foldl (fun a t => editsOf t a) a
  | .hole _, a => a

/-- `#edits in cmd`: run `cmd`, then show the edit that each of its
suggestions makes: the line (counted from the first line of `cmd`), the
columns replaced, the text written, and the title among the code actions. -/
elab "#edits " "in" c:command : command => do
  elabCommand c
  let line0 := ((← getFileMap).utf8PosToLspPos (c.raw.getPos?.getD 0)).line
  let infos := (← getInfoTrees).foldl (fun a t => editsOf t a) #[]
  for i in infos do
    let r := i.edit.range
    logInfo m!"line +{r.start.line - line0}, columns {r.start.character} to \
      {r.«end».character}: write {repr i.edit.newText}   [{i.codeActionTitle}]"

end Edits

-- The edit of each offer: nothing is replaced (the two columns are equal),
-- and the motion is written after the last one, on its line.
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: ? p0, p1, (p0 ∧ p1) ⊢ p1
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
  at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all
---
info: Motions from here:
  [apply] down 0
  [apply] down 1
  [apply] up
  [apply] top
  [apply] goal 0
---
info: line +0, columns 27 to 27: write " down 0"   [#walk: down 0]
---
info: line +0, columns 27 to 27: write " down 1"   [#walk: down 1]
---
info: line +0, columns 27 to 27: write " up"   [#walk: up]
---
info: line +0, columns 27 to 27: write " top"   [#walk: top]
---
info: line +0, columns 27 to 27: write " goal 0"   [#walk: goal 0]
-/
#guard_msgs in
#edits in
#walk swapAtt down 0 down 0

-- A walk over several lines: the offer is at its last line, and so is the
-- edit.  A comma after the last motion stays after what is written.
/--
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [closed]
  at the root: 1 premise; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
>   (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      0: p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR   [closed]
  at 0: 1 premise; no open goals
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.1: no premises; no open goals
---
info: Motions from here:
  [apply] up
  [apply] left
  [apply] top
---
info: line +2, columns 16 to 16: write " up"   [#walk: up]
---
info: line +2, columns 16 to 16: write " left"   [#walk: left]
---
info: line +2, columns 16 to 16: write " top"   [#walk: top]
-/
#guard_msgs in
#edits in
#walk swap
  down 0
  down 0, down 1,

-- what is offered, as functions
#guard (Cursor.ofAtt swapAtt).motions == [.down 0, .goal 0]
#guard walkOffers swapAtt [.down 0, .down 0] == ["down 0", "down 1", "up", "top", "goal 0"]
#guard walkOffers swap [.down 0, .down 0, .down 1] == ["up", "left", "top"]
#guard walkOffers swap [.up] == []
-- each motion offered can be made (`Cursor.motions_move`), here by running
#guard ((Cursor.ofAtt swapAtt).moves [.down 0, .down 0]).toOption.map
  (fun c => c.motions.all fun m => (c.move m).isSome) == some true
-- a click and then the view: the walk with the offered motion written after it
#guard (walkText swapAtt [.down 0, .down 0, .down 1]).toOption.isSome

end ProofToolsTest.Explore.WalkTest
