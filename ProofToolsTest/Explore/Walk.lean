/-
Tests of `ProofTools.Explore.Motion` and `ProofTools.Explore.Walk` on the
example calculus: the view at the root and after motions, on an attempt
with an open goal and on a derivation; a walk written over several lines,
with a view at each; every motion; every way a motion can fail, with its
reason; an attempt named by a term; `walkText` as a function; the laws on
an example.  Each message is pinned by `#guard_msgs`.
-/
import ProofToolsTest.Explore.Tactic

namespace ProofToolsTest.Explore.WalkTest

open ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.TacticTest

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

end ProofToolsTest.Explore.WalkTest
