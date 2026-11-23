/-
Tests of `BrunnlerK/Explore.lean`: a sequent drawn as its tree, and the
tactics of the calculus.
-/
import BrunnlerK.Explore
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq ProofTools ProofTools.Explore

-- A node on each line; the boxes of a node below it, one step in, in
-- their order; `∅` for a node with no formula.
#guard (seq[◇(∼a ⋏ ∼b), ◇b, [a, [b], []], [∼a ⋏ ∼b, a]]).tree
    == "◇(ā ∧ b̄), ◇b\n  a\n    b\n    ∅\n  ā ∧ b̄, a"
#guard (seq[]).tree == "∅"

-- The routine steps: `∨`, `∧`, and `□` twice; two goals are left.
#guard (routine 20 seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).map (·.length) == some 4
#guard (routine 20 seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).map (derives S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)])
    == some false

-- The search as a tactic: a script that runs to the end, or nothing.
#guard (found seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).map (derives S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)])
    == some true
#guard (found seq[□a ⊃ □□a]).isNone

-- The blind search does not close this one: it takes the first move
-- that adds something and never goes back.
#guard (auto 20 seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).map (derives S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)])
    == some false

end BrunnlerK.Test
