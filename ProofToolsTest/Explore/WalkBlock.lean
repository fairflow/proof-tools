/-
Tests of the walker as a tactic block (`ProofTools.Explore.Walk`): the goal
`Walk d` and the motions as its lines, on the example calculus.  The goal
after each line is the view there, seen here with `trace_state`; every
motion; a motion that cannot be made; a block with no last line; an attempt
named by a term; and that `left` and `right` are still Lean's tactics on any
other goal, with Lean's own errors.  Each message is pinned by
`#guard_msgs`.
-/
import ProofToolsTest.Explore.Tactic

namespace ProofToolsTest.Explore.WalkBlockTest

open ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.TacticTest

/-! ## The goal is the view

`swap` is a derivation of `(p ∧ q) → (q ∧ p)`.  The block ends with a goal
still there, and no error: Lean closes it. -/

/--
trace: ⊢ Walk swap
    >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        0: (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1   [closed]
      at the root: 1 premise; no open goals
---
trace: ⊢ Walk swap
       ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    >     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
            0: p0, p1, (p0 ∧ p1) ⊢ p1   by ax   [closed]
            1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
      at 0.0: 2 premises; no open goals
---
trace: ⊢ Walk swap
       ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
          p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
    >       p0, p1, (p0 ∧ p1) ⊢ p0   by ax
      at 0.0.1: no premises; no open goals
-/
#guard_msgs in
example : Walk swap := by
  trace_state
  down 0
  down 0
  trace_state
  down 1
  trace_state

/-! ## Every motion -/

/--
trace: ⊢ Walk swapAtt
       ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
          p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
    >       ? p0, p1, (p0 ∧ p1) ⊢ p1
      at 0.0.0: open goal 0; 1 open in all
---
trace: ⊢ Walk swapAtt
       ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    >     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
            0: ? p0, p1, (p0 ∧ p1) ⊢ p1
            1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
      at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all
-/
#guard_msgs in
example : Walk swapAtt := by
  down 0
  down 0
  down 1
  left
  trace_state
  right
  up
  trace_state
  top
  goal 0

-- one line, as a script is written
#guard_msgs in
example : Walk swap := by down 0; down 0; up

/-! ## A motion that cannot be made: an error at its line, with the reason -/

/--
error: this motion cannot be made: the focus is the root
-/
#guard_msgs in
example : Walk swap := by
  down 0
  up
  up

/--
error: this motion cannot be made: the focus has no premise 3: its premises are numbered 0 to 0
-/
#guard_msgs in
example : Walk swap := by
  down 3

/--
error: this motion cannot be made: the focus is an open goal: it has no premises
-/
#guard_msgs in
example : Walk swapAtt := by
  goal 0
  down 0

/--
error: this motion cannot be made: the focus is the root
-/
#guard_msgs in
example : Walk swapAtt := by
  left

/--
error: this motion cannot be made: the focus is the last premise of its node
-/
#guard_msgs in
example : Walk swapAtt := by
  goal 0
  right
  right

/-! ## An attempt named by a term -/

/--
trace: ⊢ Walk
       ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    >   ? (p0 ∧ p1) ⊢ (p1 ∧ p0)
      at 0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Walk (run IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) [⟨0, .impR⟩]).att := by
  goal 0
  trace_state

/-! ## On any other goal

`left` and `right` are Lean's, and fail as Lean's do; the other motions say
that the goal is not a walk. -/

#guard_msgs in
example : p = p ∨ p = q := by
  left
  rfl

#guard_msgs in
example : p = q ∨ p = p := by
  right
  rfl

/--
error: Tactic `left` failed: left tactic works for inductive types with exactly 2 constructors

⊢ True
-/
#guard_msgs in
example : True := by
  left

/--
error: down 0: a motion is for a goal `Walk d`, and this goal is not one
-/
#guard_msgs in
example : True := by
  down 0

/--
error: top: a motion is for a goal `Walk d`, and this goal is not one
-/
#guard_msgs in
example : True := by
  top

/-! ## The names of the motions are not taken

A motion's first word is read as a tactic only where a tactic is read. -/

/-- A definition named as a motion is. -/
def top : Nat := 1
/-- Arguments named as motions are. -/
def up (left right : Nat) : Nat := left + right + top

#guard up 1 2 == 4

/-! ## A walk says nothing about what it walks -/

example : Walk swap [.down 0] := inferInstance

end ProofToolsTest.Explore.WalkBlockTest
