/-
Tests of the tactics of `ProofTools.Explore.Tactic` on the example calculus
(`ProofToolsTest/Explore/Calculus.lean`), each behaviour watched and pinned
by `#guard_msgs`: moves, patterns, queries, the errors, `apply_script`,
`leave_open`, an alias, and an instance that quotes wrongly.
-/
import ProofToolsTest.Explore.Calculus

namespace ProofToolsTest.Explore.TacticTest

open ProofTools.Explore ProofToolsTest.Explore

/-- The atom `p`. -/
abbrev p : Form := .atom 0
/-- The atom `q`. -/
abbrev q : Form := .atom 1
/-- The atom `r`. -/
abbrev r : Form := .atom 2

/-! ## Moves

A move's name may be written in full, with a dot, or bare.  The lines of the
proof are the lines of the script read back from the derivation. -/

/-- A derivation of `(p ∧ q) → (q ∧ p)`. -/
def swap : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move Move.impR
  apply_move .andL p q
  apply_move andR
  apply_move ax
  apply_move ax

#guard swap.script == [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]
#guard derives IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) swap.script

/-- The same, the second premise first: `at 1`. -/
def swap' : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move ax at 1
  apply_move ax

#guard swap'.script == swap.script

/-- The kernel checked the equations of the nodes by evaluating `step`. -/
theorem swap_valid : Valid ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := Der.sound sound swap

/-! ## Patterns

Arguments left out, or holes, are matched against the candidates that
apply.  One match is made, and shown. -/

/--
info: Try this:
  [apply] apply_move andL (Form.atom 0) (Form.atom 1)
-/
#guard_msgs in
example : Der IPC ([p ⋏ q] ⊢ p) := by
  apply_move andL
  apply_move ax

/--
info: Try this:
  [apply] apply_move andL (Form.atom 1) (Form.atom 2)
---
info: Try this:
  [apply] apply_move andL (Form.atom 0) (Form.atom 1)
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q, q ⋏ r] ⊢ r) := by
  apply_move andL ?_ r
  apply_move andL p _
  apply_move ax

-- Several matches are offered, and no move is made.
/--
info: apply_move: 2 moves of this form apply at goal 0; no move is made. Try these:
  [apply] apply_move andL (Form.atom 0) (Form.atom 1)
  [apply] apply_move andL (Form.atom 1) (Form.atom 2)
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q, q ⋏ r] ⊢ r) := by
  apply_move andL
  leave_open

-- No match is an error.
/--
error: apply_move: no candidate move of this form applies at goal 0; write its arguments out, or `apply_move` alone to see the moves that apply
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move orL

-- With the option off the line made is not shown.
#guard_msgs in
set_option apply_move.tryThis false in
example : Der IPC ([p ⋏ q] ⊢ p) := by
  apply_move andL
  apply_move ax

/-! ## Queries

A line that does not settle its move makes none. -/

/--
info: apply_move: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] apply_move andR
  [apply] apply_move andL (Form.atom 0) (Form.atom 1)
  [apply] apply_move andL (Form.atom 1) (Form.atom 2)
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q, q ⋏ r] ⊢ r ⋏ p) := by
  apply_move
  leave_open

/--
info: apply_move: at goal 1, 2 moves whose names begin with `a` apply; no move is made. Try these:
  [apply] apply_move andL (Form.atom 0) (Form.atom 1) at 1
  [apply] apply_move andL (Form.atom 1) (Form.atom 2) at 1
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q, q ⋏ r] ⊢ r ⋏ p) := by
  apply_move andR
  apply_move a at 1
  leave_open
  leave_open

-- A move whose premise adds nothing is set aside while another applies:
-- here `andL p q` has been made, and is offered again only because nothing
-- else applies.
/--
info: apply_move: at goal 0, 1 move applies; no move is made. Try these:
  [apply] apply_move andL (Form.atom 0) (Form.atom 1)
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move andL p q
  apply_move
  leave_open

/--
error: apply_move: no move whose name begins with `or` applies at goal 0
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move or

/-! ## Errors -/

/--
error: the move does not apply to goal 0: the conclusion is not an implication
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move impR

/--
error: there is no goal 3: the open goals are 0 to 0
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move ax at 3

/--
error: Unknown identifier `foo`
-/
#guard_msgs in
example : Att IPC true ([p ⋏ q] ⊢ r) := by
  apply_move foo

/--
error: apply_move: the goal is not an attempt `Att S o j` or a derivation `Der S j`
-/
#guard_msgs in
example : True := by
  apply_move ax

/--
error: apply_move: the goal's judgment is not a closed term
-/
#guard_msgs in
example (s : Seq) : Att IPC true s := by
  apply_move ax

/-! ## Scripts and open goals -/

/-- A stored script, continued by hand. -/
def swapAtt : Att IPC true ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_script [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩]
  apply_move ax at 1
  leave_open

#guard swapAtt.goals == [[p, q, p ⋏ q] ⊢ q]
#guard swapAtt.script == [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩, ⟨1, .ax⟩]

/--
error: apply_script: line 1: the move does not apply to goal 0: the conclusion is not an implication
-/
#guard_msgs in
example : Att IPC true ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_script [⟨0, .impR⟩, ⟨0, .impR⟩, ⟨0, .andR⟩]

/--
error: apply_script: line 1: there is no goal 4: the open goals are 0 to 0
-/
#guard_msgs in
example : Att IPC true ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_script [⟨0, .impR⟩, ⟨4, .impR⟩]

/--
error: leave_open: the goal is a derivation, which has no open goals
-/
#guard_msgs in
example : Der IPC ([p] ⊢ p) := by
  leave_open

/--
info:  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
  (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
      ? p0, p1, (p0 ∧ p1) ⊢ p1
      p0, p1, (p0 ∧ p1) ⊢ p0   by ax
-/
#guard_msgs in
#eval IO.println swapAtt.render

/-! ## An alias, fixed to its calculus -/

declare_move_tactic ipc for IPC

/--
info: Try this:
  [apply] ipc andL (Form.atom 0) (Form.atom 1)
-/
#guard_msgs in
example : Der IPC ([p ⋏ q] ⊢ p) := by
  ipc andL
  ipc ax

/-- A second calculus: from `n < 3` the one move goes up to `n + 1`. -/
abbrev Up : ProofSystem where
  Judg := Nat
  Move := Unit
  step _ n := if n < 3 then .ok [n + 1] else .ok []

/-- Its instance quotes judgments wrongly, on purpose: `n` as `n + 1`. -/
instance : Explorable Up where
  candidates _ := [()]
  showJudg := toString
  showMove _ := "up"
  quoteJudg := ⟨fun n => Lean.mkNatLit (n + 1), Lean.mkConst ``Nat⟩
  quoteMove := inferInstanceAs (Lean.ToExpr Unit)
  moveSource _ := some "() -- up"

/--
error: ipc: the goal is not an attempt in `ProofToolsTest.Explore.IPC`
-/
#guard_msgs in
example : Att Up true (0 : Nat) := by
  ipc ()

-- A suggested line is written with the instance's source text
-- (`moveSource`), where it gives one.
/--
info: apply_move: at goal 0, 1 move applies; no move is made. Try these:
  [apply] apply_move () -- up
-/
#guard_msgs in
example : Att Up true (5 : Nat) := by
  apply_move
  leave_open

/-! ## Nothing an instance supplies is trusted

The tactic believes the wrong quotation, and writes the premise of the move
at `1` as `3`.  The kernel evaluates `step` and refuses the node. -/

/--
error: (kernel) application type mismatch
  Att.node () [3] ⋯
argument has type
  Except.ok [3] = Except.ok [3]
but function has type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
example : Att Up true (1 : Nat) := by
  apply_move ()
  leave_open

end ProofToolsTest.Explore.TacticTest
