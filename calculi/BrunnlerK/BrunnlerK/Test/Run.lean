/-
Tests of the Run stage (`BrunnlerK/Run.lean`): each certifier rejects a
certificate that is wrong, in the kernel; the producers agree with the
certifiers; facts stated with a certificate are within the axioms
allowed.
-/
import BrunnlerK.Run
import BrunnlerK.Tactic
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq ProofTools ProofTools.Explore

/-! ## A certificate that is right -/

/-- The tree of moves of Example 2.3, as the search gives it. -/
def ex23Tree : Cert S :=
  .mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] (∼a) (∼b))
    [.mk (.ax [0] 4) [], .mk (.dia [] 0 b) [.mk (.ax [0] 5) []]]]]

/-- Example 2.3, by its tree of moves: the kernel checks the tree. -/
def ex23Fact : K seq[◇(∼a ⋏ ∼b), □a, ◇b] := treeCert.verdict _ ex23Tree

/-- Axiom 4 is not valid: the kernel computes that its formula is not
true at the root of the chain. -/
theorem axiom4Fact : ¬ Valid seq[□a ⊃ □□a] :=
  noValid.verdict _ (.node [] [.node [4] [.node [] []]])

#certify_axioms BrunnlerK.Test.ex23Fact
#certify_axioms BrunnlerK.Test.axiom4Fact

/-! ## Certificates that are wrong, rejected in the kernel (R9) -/

-- A tree with a wrong move: `∧` on a formula the box does not have.
theorem bad_tree_rejected' : treeCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    (.mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] a b) []]]) = false := by
  decide +kernel

-- A tree that stops early: the right branch is not closed.
theorem short_tree_rejected' : treeCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    (.mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] (∼a) (∼b))
      [.mk (.ax [0] 4) []]]]) = false := by
  decide +kernel

-- A tree that does not refute axiom 4: `a` is true at the third state too.
theorem bad_model_rejected : noValid.check seq[□a ⊃ □□a]
    (.node [] [.node [4] [.node [4] []]]) = false := by
  decide +kernel

-- A tree offered against a valid sequent.
theorem model_of_valid_rejected : noValid.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    (.node [] [.node [] []]) = false := by
  decide +kernel

-- And as the gate reports it: the verdict does not typecheck.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  noValid.check (leaf [□a ⊃ □□a]) (Tree.node [] [Tree.node [4] [Tree.node [4] []]]) = true
is false
-/
#guard_msgs in
example : ¬ Valid seq[□a ⊃ □□a] :=
  noValid.verdict _ (.node [] [.node [4] [.node [4] []]])

/-! ## The producers and the certifiers agree -/

#guard (prove? seq[◇(∼a ⋏ ∼b), □a, ◇b]).map (treeCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]) == some true
#guard (refute? seq[□a ⊃ □□a]).map (noValid.check seq[□a ⊃ □□a]) == some true
#guard (prove? seq[□a ⊃ □□a]).isNone
#guard (refute? seq[◇(∼a ⋏ ∼b), □a, ◇b]).isNone
#guard match produce seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] 0 with
  | .pass ls => scriptCert.check seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] ls
  | _ => false
#guard match kEngine.produce seq[□a ⊃ □□a] 0 with
  | .fail t => kEngine.no.check seq[□a ⊃ □□a] t
  | _ => false

end BrunnlerK.Test
