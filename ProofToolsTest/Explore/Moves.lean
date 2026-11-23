/-
Tests of the cursor's motions as moves of the generic zipper
(`ProofTools/Zipper.lean`): `Cursor.up` and `Cursor.down` are its `up` and
`down`, the motions `left` and `right` its one-step `left` and `right`
(`Zip.Deriv.Sibling`), and the cursor's count of open goals is kept from
the nearest crumb (`Zip.Deriv.Zipper.crumb`).

What is checked here by running: the one step to a sibling on an attempt,
against `sibling` (up, then down); the cursor's count across the premises
of a node whose premises have two, one and no open goals; the motions in
the kernel.  What the motions were defined as before is PROVED of them now
(`Cursor.up_cons`, `Cursor.down_eq`, `Cursor.move_left`,
`Cursor.move_right`); the statements are pinned here.
-/
import ProofTools.Audit
import ProofToolsTest.Explore.Run
import ProofToolsTest.Explore.Count

namespace ProofToolsTest.Explore.MovesTest

open ProofTools ProofTools.Explore ProofToolsTest.Explore

/-! ## The zipper's one step to a sibling, on an attempt -/

section Zipper

open Zip.Deriv RunTest

/-- The zipper of `att₄` at an address, if there is a node there. -/
def zipAt (a : List Nat) :=
  (Zipper.ofRoot (L := attDeriv IPC true) att₄).descend a

/-- A zipper one step from the address `[0, 0, i]`, as its premise number,
its judgment and the script of the whole attempt. -/
def beside (i : Nat) (right : Bool) : Option (Nat × String × Bool) :=
  (zipAt [0, 0, i]).bind fun x =>
    (if right then x.2.right else x.2.left).map fun y =>
      (y.1, y.2.1.show, y.2.2.toRoot.script == att₄.script)

-- from the second premise of `andR` to the first, and no further
#guard beside 1 false == some (0, "p0, p1, (p0 ∧ p1) ⊢ p1", true)
#guard beside 1 true == none
-- from the first to the second, and none before it
#guard beside 0 true == some (1, "p0, p1, (p0 ∧ p1) ⊢ p0", true)
#guard beside 0 false == none

-- the one step is `sibling` at the premise number reached (`sibling_of_left`,
-- `sibling_of_right`, PROVED for canonical paths)
#guard ((zipAt [0, 0, 1]).bind fun x => x.2.left.map fun y => y.2.1.show) ==
  ((zipAt [0, 0, 1]).bind fun x => (x.2.sibling 0).map fun y => y.1.show)
#guard ((zipAt [0, 0, 0]).bind fun x => x.2.right.map fun y => y.2.1.show) ==
  ((zipAt [0, 0, 0]).bind fun x => (x.2.sibling 1).map fun y => y.1.show)

-- left, then right, returns (`right_left`, PROVED)
#guard ((zipAt [0, 0, 1]).bind fun x => x.2.left.bind fun y => y.2.2.right.map fun z =>
  (z.1, z.2.1.show)) == some (1, "p0, p1, (p0 ∧ p1) ⊢ p0")

-- the nearest crumb: the move of the node above, and the premises beside the hole
#guard ((zipAt [0, 0, 1]).map fun x => (x.2.crumb.move == .andR, x.2.crumb.lsr.length, x.2.crumb.rs.length))
  == some (true, 1, 0)

end Zipper

/-! ## The cursor's count across the premises of a node -/

section Count

open Count

/-- At `2`: three premises at `1`; the first has two open goals, the second
is an open goal, the third is closed. -/
def three : Att Count true 2 :=
  (run Count 2 [L 0 (.split 3), L 0 (.split 2), L 3 (.split 0)]).att

#guard three.goals == [0, 0, 1]

/-- The address and the count of open goals left of the focus, after
motions from the root. -/
def after (ms : List Motion) : Option (List Nat × Nat) :=
  ((Cursor.ofRoot three).moves ms).toOption.map fun c => (c.addr, c.left)

#guard after [.down 0] == some ([0], 0)
#guard after [.down 0, .right] == some ([1], 2)
#guard after [.down 0, .right, .right] == some ([2], 3)
#guard after [.down 0, .right, .right, .right] == none
#guard after [.down 2, .left] == some ([1], 2)
#guard after [.down 2, .left, .left] == some ([0], 0)
#guard after [.down 2, .left, .left, .left] == none
#guard after [.down 1, .up] == some ([], 0)
#guard after [.down 0, .down 1, .right] == none
#guard after [.down 0, .down 1] == some ([0, 1], 1)
#guard after [.left] == none
#guard after [.right] == none

/-- The same position by going up and down again. -/
def afterUpDown (ms : List Motion) (d : Nat) : Option (List Nat × Nat) :=
  (((Cursor.ofRoot three).moves ms).toOption.bind fun c => c.up.bind (·.down d)).map fun c =>
    (c.addr, c.left)

-- `Cursor.move_right`, `Cursor.move_left` (PROVED), here by running
#guard after [.down 0, .right] == afterUpDown [.down 0] 1
#guard after [.down 1, .right] == afterUpDown [.down 1] 2
#guard after [.down 2, .left] == afterUpDown [.down 2] 1
#guard afterUpDown [.down 2] 3 == none

/-! ## In the kernel

Across the hundred premises of a node and back: 198 steps to a sibling. -/

/-- One node with `k` premises, all open. -/
def wide (k : Nat) : Att Count true 1 := (run Count 1 [L 0 (.split k)]).att

/-- Down to the first premise, to the last by `right`, and back by `left`. -/
def across (k : Nat) : List Motion :=
  .down 0 :: (List.replicate (k - 1) .right ++ List.replicate (k - 1) .left)

example : ((Cursor.ofRoot (wide 100)).moves (across 100)).toOption.map (·.addr) = some [0] := by
  decide +kernel

example : ((Cursor.ofRoot (wide 100)).moves (across 100 |>.take 100)).toOption.map
    (fun c => (c.addr, c.left)) = some ([99], 99) := by
  decide +kernel

end Count

/-! ## What the motions were defined as, PROVED of them -/

section Statements

variable {S : ProofSystem} {j : S.Judg}

example (w : Att S true j) (l : Nat) : Cursor.up ⟨⟨[], j, ⟨w, .top⟩⟩, l⟩ = none :=
  Cursor.up_top w l

example {i i' : S.Judg} {d : Nat} {ds : List Nat} (w : Att S true i) (cr : Crumb S true d i i')
    (p : Path S true ds i' j) (l : Nat) :
    Cursor.up ⟨⟨d :: ds, i, ⟨w, .cons cr p⟩⟩, l⟩ =
      some ⟨⟨ds, i', ⟨cr.plug w, p⟩⟩, l - cr.left.goalsRev.length⟩ :=
  Cursor.up_cons w cr p l

example (i : Nat) (c : Cursor S j) :
    c.down i =
      match Att.unplug c.pos.z.focus i with
      | none => none
      | some ⟨p, w, cr⟩ =>
        some ⟨⟨i :: c.pos.ds, p, ⟨w, .cons cr c.pos.z.path⟩⟩, c.left + cr.left.goalsRev.length⟩ :=
  Cursor.down_eq i c

example (c : Cursor S j) :
    c.move .left =
      match c.pos.ds with
      | [] => none
      | 0 :: _ => none
      | (d + 1) :: _ => c.up.bind (·.down d) :=
  Cursor.move_left c

example (c : Cursor S j) :
    c.move .right =
      match c.pos.ds with
      | [] => none
      | d :: _ => c.up.bind (·.down (d + 1)) :=
  Cursor.move_right c

end Statements

end ProofToolsTest.Explore.MovesTest

/-! ## Axioms -/

open ProofTools ProofTools.Explore in
#axioms_within Zip.Deriv.Zipper.up_left [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Zip.Deriv.Zipper.right_left [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Zip.Deriv.Zipper.sibling_of_right [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Zip.Deriv.Zipper.path_eq_cons [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Crumb.unplug_plug_succ [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.sibling_some [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.move_left [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.move_right [propext, Quot.sound]
