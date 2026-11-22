/-
Tests of `ProofTools.Explore` on the example calculus
(`ProofToolsTest/Explore/Calculus.lean`): running scripts, the messages of
a failing line, reading a script back, running in two parts, the zipper's
moves on an attempt, both checkers in the kernel, the engine with its
producer, and the combinators on tactics.
-/
import ProofToolsTest.Explore.Calculus

namespace ProofToolsTest.Explore.RunTest

open ProofTools ProofTools.Explore ProofToolsTest.Explore

/-- The atom `p`. -/
abbrev p : Form := .atom 0
/-- The atom `q`. -/
abbrev q : Form := .atom 1
/-- The atom `r`. -/
abbrev r : Form := .atom 2

/-- `⊢ (p ∧ q) → (q ∧ p)`. -/
def swap : Seq := [] ⊢ (p ⋏ q) ⟶ (q ⋏ p)

/-- A script for it. -/
def swapScript : Script IPC := [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]

/-! ## Running a script -/

#guard derives IPC swap swapScript
#guard (run IPC swap swapScript).att.goals == []
#guard (run IPC swap (swapScript.take 3)).att.goals == [[p, q, p ⋏ q] ⊢ q, [p, q, p ⋏ q] ⊢ p]
#guard !derives IPC swap (swapScript.take 3)

/--
info:  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
  (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
      ? p0, p1, (p0 ∧ p1) ⊢ p1
      ? p0, p1, (p0 ∧ p1) ⊢ p0
-/
#guard_msgs in
#eval IO.println (run IPC swap (swapScript.take 3)).att.render

-- the second premise first: the cursor goes right, then left
#guard derives IPC swap (swapScript.take 3 ++ [⟨1, .ax⟩, ⟨0, .ax⟩])

/-! ## A failing line: its number and the reason; the attempt is as it was -/

#guard (run IPC swap (swapScript.take 3 ++ [⟨2, .ax⟩])).failed == some (3, "there is no goal 2")
#guard (run IPC swap (swapScript.take 3 ++ [⟨0, .impR⟩])).failed ==
  some (3, "the move does not apply to goal 0: the conclusion is not an implication")
#guard (run IPC swap (swapScript.take 3 ++ [⟨0, .impR⟩, ⟨0, .ax⟩])).att.script == swapScript.take 3

/-! ## `run` and the run by steps (PROVED equal: `Att.run_eq_runBySteps`) -/

#guard (List.range 6).all fun n =>
  let a := run IPC swap (swapScript.take n)
  let b := Att.runBySteps (S := IPC) (j := swap) .goal (swapScript.take n)
  a.att.script == b.att.script && a.failed == b.failed

/-! ## A script read back (PROVED: `run_script`) -/

#guard (run IPC swap swapScript).att.script == swapScript
#guard (run IPC swap (swapScript.take 3 ++ [⟨1, .ax⟩])).att.script ==
  swapScript.take 3 ++ [⟨1, .ax⟩]

/-! ## A script run in two parts

PROVED (`Att.runFrom_append`): if the first part does not fail, running the
whole is running the second part on what the first leaves, *its lines
numbered after the first's*.  Without the numbering the statement is
REFUTED: the two sides differ in the number of the failing line. -/

/-- The first part. -/
def part₁ : Script IPC := swapScript.take 3
/-- A second part whose first line fails. -/
def part₂ : Script IPC := [⟨0, .impR⟩]

#guard (run IPC swap part₁).failed == none
-- the statement without the numbering fails here:
#guard (run IPC swap (part₁ ++ part₂)).failed.map (·.1) == some 3
#guard ((run IPC swap part₁).att.run part₂).failed.map (·.1) == some 0
-- with it, the two sides agree:
#guard ((run IPC swap part₁).att.runFrom 3 part₂).failed == (run IPC swap (part₁ ++ part₂)).failed

/-! ## The zipper's moves on an attempt -/

section Zipper

open Zip.Deriv

/-- The attempt after four lines: the first premise of `andR` closed. -/
def att₄ : Att IPC true swap := (run IPC swap (swapScript.take 4)).att

/-- The judgment and the open goals at the end of a descent from the root. -/
def at? (a : List Nat) : Option (String × List String) :=
  ((Zipper.ofRoot (L := attDeriv IPC true) att₄).descend a).map fun x =>
    (x.1.show, x.2.focus.goals.map Seq.show)

#guard at? [0, 0, 0] == some ("p0, p1, (p0 ∧ p1) ⊢ p1", [])
#guard at? [0, 0, 1] == some ("p0, p1, (p0 ∧ p1) ⊢ p0", ["p0, p1, (p0 ∧ p1) ⊢ p0"])
#guard at? [0, 0, 2] == none
#guard at? [1] == none

-- down, then up, returns; so does a sibling's sibling
#guard (((Zipper.ofRoot (L := attDeriv IPC true) att₄).descend [0, 0, 1]).map fun x =>
  x.2.up.2.toRoot.script == att₄.script) == some true
#guard (((Zipper.ofRoot (L := attDeriv IPC true) att₄).descend [0, 0, 1]).bind fun x =>
  (x.2.sibling 0).map fun y => y.1.show) == some "p0, p1, (p0 ∧ p1) ⊢ p1"

end Zipper

/-! ## Both checkers, in the kernel -/

/-- Level 1: a script, checked. -/
example : Valid swap := (certifier sound.soundT).verdict swap swapScript

/-- A sequent that does not hold. -/
def notValid : Seq := [] ⊢ (p ⋎ q) ⟶ p

/-- Level 2: a valuation that refutes it, checked. -/
example : ¬ Valid notValid := ipcEngine.no.verdict notValid [1]

/-- A derivation, from a script that `derives` accepts. -/
example : Der IPC swap := Der.ofScript swap swapScript (by decide +kernel)

/-! ## The engine: `pass`, `fail`, `flag` -/

/-- Peirce's law: it holds, and the calculus does not derive it. -/
def peirce : Seq := [] ⊢ ((p ⟶ q) ⟶ p) ⟶ p

/-- Distribution: derivable, but not by a producer that never goes back. -/
def distr : Seq := [] ⊢ (p ⋏ (q ⋎ r)) ⟶ ((p ⋏ q) ⋎ (p ⋏ r))

/-- A verdict, as text. -/
def verdict (s : Seq) : String :=
  match ipcEngine.produce s 12 with
  | .pass ls => s!"pass: a script of {ls.length} lines"
  | .fail M => s!"fail: true atoms {M}"
  | .flag => "flag"

#guard verdict swap == "pass: a script of 6 lines"
#guard verdict ([p ⟶ q, p] ⊢ q) == "pass: a script of 3 lines"
#guard verdict notValid == "fail: true atoms [1]"
#guard verdict peirce == "flag"
#guard verdict distr == "flag"

-- what the producer passes, the first checker accepts; what it fails, the second
#guard match ipcEngine.produce swap 12 with
  | .pass ls => ipcEngine.yes.check swap ls
  | _ => false
#guard match ipcEngine.produce notValid 12 with
  | .fail M => ipcEngine.no.check notValid M
  | _ => false

/-- By hand, where the producer flags: the right disjunct in the second branch. -/
def distrScript : Script IPC :=
  [⟨0, .impR⟩, ⟨0, .andL p (q ⋎ r)⟩, ⟨0, .orL q r⟩,
   ⟨0, .orR1⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩,
   ⟨0, .orR2⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]

example : Valid distr := (certifier sound.soundT).verdict distr distrScript

/-! ## Scripts as programs -/

#guard (Script.shift 3 swapScript).map (·.goal) == [3, 3, 3, 3, 3]

-- one move, where it applies
#guard (Tac.move (S := IPC) .impR swap) == some [⟨0, .impR⟩]
#guard (Tac.move (S := IPC) .andR swap) == none

-- `orElse`
#guard ((Tac.move (S := IPC) .andR).orElse (Tac.move .impR) swap) == some [⟨0, .impR⟩]

-- `andThen`: the second tactic at every goal the first leaves, each at its number
#guard ((Tac.move (S := IPC) .andR).andThen (Tac.move .ax) ([p, q] ⊢ q ⋏ p)) ==
  some [⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]
#guard ((Tac.move (S := IPC) .andR).andThen ((Tac.move (S := IPC) .ax).orElse Tac.skip) ([p] ⊢ q ⋏ p)) ==
  some [⟨0, .andR⟩, ⟨1, .ax⟩]
#guard ((Tac.move (S := IPC) .andR).andThen (Tac.move .ax) ([p] ⊢ q ⋏ p)) == none

-- `iterate`: leaves open what it cannot close, and its script runs
#guard (auto 12 swap).map (derives IPC swap) == some true
#guard ((auto 12 peirce).map fun ls => (run IPC peirce ls).failed.isNone) == some true
#guard ((auto 12 peirce).map fun ls => (run IPC peirce ls).att.goals.map Seq.show) ==
  some ["p0, ((p0 → p1) → p0) ⊢ p1"]

end ProofToolsTest.Explore.RunTest
