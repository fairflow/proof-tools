/-
A second proof system for the tests of `ProofTools.Explore`, with moves of
every number of premises: the judgments are the natural numbers, `done`
closes `0`, and `split k` takes `n + 1` to `k` copies of `n`.

It is used to compare `run` (a zipper kept from line to line) with
`Att.runBySteps` (a step from the root at every line) on many scripts, in
orders that send the cursor left as well as right.  The two are PROVED
equal (`Att.run_eq_runBySteps`); these tests were written first, and are
kept.
-/
import ProofTools.Explore

namespace ProofToolsTest.Explore.Count

open ProofTools.Explore

/-- The moves. -/
inductive CMove where
  | done
  | split (k : Nat)
  deriving DecidableEq, Repr

/-- **The system**: `done` at `0`; `split k` from `n + 1` to `k` copies of `n`. -/
abbrev Count : ProofSystem where
  Judg := Nat
  Move := CMove
  step
    | .done, 0 => .ok []
    | .done, _ + 1 => .error "not zero"
    | .split _, 0 => .error "zero"
    | .split k, n + 1 => .ok (List.replicate k n)

/-- A line. -/
abbrev L (g : Nat) (m : CMove) : Line Count := ⟨g, m⟩

/-- Do the two runs agree: the attempt (by its script and its goals), the
failing line and the message? -/
def agree (j : Nat) (ls : Script Count) : Bool :=
  let a := run Count j ls
  let b := Att.runBySteps (S := Count) (j := j) .goal ls
  a.att.script == b.att.script && a.failed == b.failed && a.att.goals == b.att.goals

/-- Lines that apply at various goals, and lines that do not. -/
def alphabet : List (Line Count) :=
  [L 0 .done, L 1 .done, L 2 .done, L 0 (.split 0), L 0 (.split 1), L 0 (.split 2), L 1 (.split 2),
   L 2 (.split 1), L 3 (.split 3), L 4 .done, L 1 (.split 3), L 5 (.split 1)]

/-- Every script over the alphabet of length `n`. -/
def scriptsOfLength : Nat → List (Script Count)
  | 0 => [[]]
  | n + 1 => (scriptsOfLength n).flatMap fun s => alphabet.map fun l => s ++ [l]

/-- Every script over the alphabet of length at most `n`. -/
def scripts (n : Nat) : List (Script Count) := (List.range (n + 1)).flatMap scriptsOfLength

#guard (scripts 4).length == 22621

/-! ## The two runs agree, on every script of length at most 4 -/

#guard (scripts 4).all (agree 2)
#guard (scripts 4).all (agree 3)

-- of them, these run without a failing line
#guard ((scripts 4).filter fun s => (run Count 3 s).failed.isNone).length == 210

/-! ## The rightmost goal first: the cursor goes left at every closed branch -/

/-- The script that always works on the last open goal. -/
def rightFirst (fuel : Nat) (j : Nat) : Script Count := Id.run do
  let mut ls : Script Count := []
  let mut r := run Count j []
  for _ in [0:fuel] do
    match r.att.goals.reverse with
    | [] => break
    | g :: _ =>
      let k := r.att.goals.length - 1
      ls := ls ++ [if g == 0 then L k .done else L k (.split 2)]
      r := run Count j ls
  return ls

#guard (rightFirst 100 4).length == 31
#guard (run Count 4 (rightFirst 100 4)).att.goals == []
#guard (List.range 32).all fun n => agree 4 ((rightFirst 100 4).take n)

/-! ## A script read back rebuilds its attempt (`run_script`, PROVED) -/

#guard (scripts 4).all fun s =>
  let d := (run Count 3 s).att
  let r := run Count 3 d.script
  r.failed.isNone && r.att.script == d.script && r.att.goals == d.goals

/-! ## Long derivations

`chain n`: from `n`, `split 1` down to `0`, then `done`: `n + 1` lines, and
the derivation is as deep. -/

/-- The script of the chain from `n`. -/
def chain (n : Nat) : Script Count := List.replicate n (L 0 (.split 1)) ++ [L 0 .done]

#guard derives Count 2000 (chain 2000)
#guard !derives Count 2001 (chain 2000)

-- in the kernel
example : derives Count 300 (chain 300) = true := by decide +kernel

end ProofToolsTest.Explore.Count
