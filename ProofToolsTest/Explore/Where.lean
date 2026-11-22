/-
Tests of the query `apply_move where` (the attempt so far, drawn, with the
goal marked), of the option that asks it after every move, and of how a goal
is shown, on the example calculus.  The query is tried in every form of
script in which the attempt has to be found again: plain lines, bullets,
goals put in another order, a part given by `exact`, a block inside a term,
a root that is not an attempt, a `have`.  Each message is pinned by
`#guard_msgs`.
-/
import ProofToolsTest.Explore.Tactic

namespace ProofToolsTest.Explore.WhereTest

open ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.TacticTest

/-! ## The query

`apply_move where` makes no move.  It draws the whole attempt so far, as
`Att.render` does, with the first goal marked `>`; `where at k` marks goal
`k`.  The last line is the last line of a view (`Cursor.viewFoot`). -/

/--
info: > ?  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))
  at the root: open goal 0; 1 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.0: open goal 0; 2 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        ? p0, p1, (p0 ∧ p1) ⊢ p1
>       ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.1: open goal 1; 2 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move where
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move where
  apply_move where at 1
  apply_move ax at 1
  apply_move where
  apply_move ax

/-! ## The attempt is found again from the goal

Under a bullet the goal list is one goal; the attempt drawn is still the
whole one. -/

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        p0, p1, (p0 ∧ p1) ⊢ p1   by ax
>       ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.1: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  · apply_move ax
  · apply_move where
    apply_move ax

-- The goals in another order: the goal marked is the first of the tactic's
-- goals, which is open goal 1 of the attempt.
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        ? p0, p1, (p0 ∧ p1) ⊢ p1
>       ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.1: open goal 1; 2 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  rotate_left
  apply_move where
  all_goals apply_move ax

/-- A derivation made before, to be given with `exact`. -/
def part : Der IPC ([p, q, p ⋏ q] ⊢ q) := by apply_move ax

-- A part that no move of this script built is drawn all the same.
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        p0, p1, (p0 ∧ p1) ⊢ p1   by ax
>       ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.1: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  exact part
  apply_move where
  apply_move ax

-- The root of the proof is a pair: the attempt is the one the goal is in.
/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     ? p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)
  at 0.0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([p] ⊢ p) × Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  constructor
  · apply_move ax
  · apply_move impR
    apply_move andL p q
    apply_move where
    apply_move andR <;> apply_move ax

-- A block inside a term is an attempt of its own: the term around it is not
-- yet the value of anything when the block runs.
/--
info: > ? p0, p1, (p0 ∧ p1) ⊢ p1
  at the root: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  exact .node Move.andR _ rfl
    (.cons (by apply_move where; apply_move ax) (.cons (by apply_move ax) .nil))

-- Inside a `have`, the attempt drawn is the one the `have` states, and the
-- message says that there is more around it.  After it, the goal is drawn
-- alone.
/--
info:   (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>     ? p0, p1, (p0 ∧ p1) ⊢ p1
      ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0: open goal 0; 2 open in all
  (an attempt around this one is not drawn: a part of it is not built by moves)
---
info: > ? (p0 ∧ p1) ⊢ (p1 ∧ p0)
  at the root: open goal 0; 1 open in all
-/
#guard_msgs in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  have d : Der IPC ([p ⋏ q] ⊢ (q ⋏ p)) := by
    apply_move andL p q
    apply_move andR
    apply_move where
    all_goals apply_move ax
  apply_move where
  exact d

/-! ## After every move

With `apply_move.showWhere` each line that makes a move shows where the
proof is after it, and the last one shows the derivation. -/

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
>   ? (p0 ∧ p1) ⊢ (p1 ∧ p0)
  at 0: open goal 0; 1 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     ? p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)
  at 0.0: open goal 0; 1 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.0: open goal 0; 2 open in all
---
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.0: open goal 0; 1 open in all
---
info: >  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        p0, p1, (p0 ∧ p1) ⊢ p1   by ax
        p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at the root: 1 premise; no open goals
-/
#guard_msgs in
set_option apply_move.showWhere true in
example : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move ax at 1
  apply_move ax

/-! ## A tactic fixed to its calculus, and the errors -/

/--
info:   (p0 ∧ p1) ⊢ p0   by andL p0 p1
>   ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ p) := by
  ipc andL p q
  ipc where
  leave_open

/--
error: there is no goal 3: the open goals are 0 to 0
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ p) := by
  apply_move where at 3

/--
error: apply_move: the goal is not an attempt `Att S o j` or a derivation `Der S j`
-/
#guard_msgs in
example : True := by
  apply_move where

-- With no goal left there is no goal to start from.
/--
error: apply_move: there are no goals
-/
#guard_msgs in
example : Der IPC ([p] ⊢ p) := by
  apply_move ax
  apply_move where

-- A `where` of Lean after a block that ends in a query is still Lean's.
/-- The number six. -/
def six : Nat := by
  exact three + three
  where three : Nat := 3

#guard six == 6

/-! ## As functions

`Att.whereText d (some k)` is what the query shows; its lines are the lines
of `Att.render`, two columns in, and the last line of the view. -/

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        p0, p1, (p0 ∧ p1) ⊢ p0   by ax
  at 0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
#eval IO.println (swapAtt.whereText (some 0))

/-- The lines of `Cursor.viewAll` without their first two columns. -/
def allLines (c : Cursor IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p))) : List String :=
  (c.viewAll.splitOn "\n").map (·.drop 2 |>.toString)

#guard ((Cursor.ofAtt swapAtt).moves [.goal 0]).toOption.map allLines
  == some (swapAtt.render.splitOn "\n" ++ ["at 0.0.0: open goal 0; 1 open in all"])
#guard ((Cursor.ofAtt swap).moves [.down 0, .down 0]).toOption.map allLines
  == some (swap.render.splitOn "\n" ++ ["at 0.0: 2 premises; no open goals"])
#guard ((Cursor.ofAtt swap).moves [.down 0, .down 0, .down 1]).toOption.map (·.viewAll)
  != ((Cursor.ofAtt swap).moves [.down 0, .down 0, .down 0]).toOption.map (·.viewAll)

-- The one loop over motions (`Cursor.trail`): every position, the last, and
-- the motion that cannot be made.
#guard ((Cursor.trail 0 (Cursor.ofAtt swap) [.down 0, .down 0, .up]).passed.map (·.addr))
  == [[], [0], [0, 0]]
#guard (Cursor.trail 0 (Cursor.ofAtt swap) [.down 0, .down 0, .up]).last.addr == [0]
#guard (Cursor.trail 0 (Cursor.ofAtt swap) [.down 0, .up, .up, .down 0]).failed
  == some (2, "the focus is the root")
#guard (Cursor.trail 0 (Cursor.ofAtt swap) [.down 0, .up, .up, .down 0]).last.addr == []

/-! ## How a goal is shown

A goal `Att S o j` is shown as its judgment, drawn by the instance's
`showJudg`: beside the head if it is one line, below it if it is more.
`Att` where open goals are allowed, `Der` where they are not. -/

/--
trace: ⊢ Att IPC   (p0 ∧ p1) ⊢ p0
---
trace: ⊢ Att IPC   p0, p1, (p0 ∧ p1) ⊢ p0
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ p) := by
  trace_state
  apply_move andL p q
  trace_state
  leave_open

-- A goal stated with `Der` is printed by Lean until a move is made.
/--
trace: ⊢ Der IPC ([p ⋏ q] ⊢ p)
---
trace: ⊢ Der IPC   p0, p1, (p0 ∧ p1) ⊢ p0
-/
#guard_msgs in
example : Der IPC ([p ⋏ q] ⊢ p) := by
  trace_state
  apply_move andL p q
  trace_state
  apply_move ax

-- A judgment that is not a closed term is printed by Lean.
/--
trace: s : Seq
d : Att IPC true s
⊢ Att IPC true s
-/
#guard_msgs in
example (s : Seq) (d : Att IPC true s) : Att IPC true s := by
  trace_state
  exact d

/-- A calculus whose judgments are drawn on two lines. -/
abbrev Tall : ProofSystem where
  Judg := Nat
  Move := Unit
  step _ n := if n < 2 then .ok [n + 1, n + 2] else .ok []

instance : Explorable Tall where
  candidates _ := [()]
  showJudg n := s!"the number {n}\nand no more"
  showMove _ := "up"
  quoteJudg := inferInstanceAs (Lean.ToExpr Nat)
  quoteMove := inferInstanceAs (Lean.ToExpr Unit)

/--
info:   the number 0
  and no more
     by up
    the number 1
    and no more
       by up
      ? the number 2
        and no more
>     ? the number 3
        and no more
    ? the number 2
      and no more
  at 0.1: open goal 1; 3 open in all
---
trace: ⊢ Att Tall
    the number 0
    and no more
-/
#guard_msgs in
example : Att Tall true (0 : Nat) := by
  trace_state
  apply_move ()
  apply_move ()
  apply_move where at 1
  all_goals leave_open

end ProofToolsTest.Explore.WhereTest
