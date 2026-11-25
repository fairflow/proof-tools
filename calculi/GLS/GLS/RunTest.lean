/-
Tests of the Run stage: a fact by each certifier, and a corrupted
certificate for each, rejected in the kernel (rule R9 of `lean-certify`:
a gate never watched failing does not count).
-/
import GLS.Run
import GLS.Tactic

namespace GLS.RunTest

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-! ## Against validity and derivability: a tree -/

/-- `⇒ (□p → □q) → □(p → q)` is false at the root of a tree with two
children, as the search returns it. -/
theorem converseK_not_derivable : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (.node [] [.node [] [], .node [0] []])

theorem converseK_not_valid : ¬ Valid ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noValid.verdict _ (.node [] [.node [] [], .node [0] []])

/-- A corrupted tree: `q` made true at the second child, where it must be
false.  Rejected. -/
theorem bad_tree_rejected :
    noDerivable.check ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) (.node [] [.node [] [], .node [0, 1] []])
      = false := by
  decide +kernel

/-- A tree that stops early: the second child left out.  Rejected. -/
theorem short_tree_rejected :
    noValid.check ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) (.node [] [.node [] []]) = false := by
  decide +kernel

/-- No tree is accepted against a derivable sequent: here, each of three
against Löb's axiom. -/
theorem lob_tree_rejected :
    ([Tree.node [] [], .node [] [.node [] []], .node [0] [.node [] [.node [] []], .node [0] []]].all
      fun t => !noValid.check ([] ⇒ [□(□p ⟶ p) ⟶ □p]) t) = true := by
  decide +kernel

/-! ## For a derivation: a tree of moves, and a script -/

/-- Löb's axiom, by the tree of moves the search returns. -/
def lob : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) :=
  treeCert.verdict _ (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr p) [.mk (.impL □p p)
    [.mk (.glr p) [.mk (.idP 0) []], .mk (.idP 0) []]]])

/-- The producer's own tree for it is that tree. -/
example : (prove? ([] ⇒ [□(□p ⟶ p) ⟶ □p]) == some (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr p)
    [.mk (.impL □p p) [.mk (.glr p) [.mk (.idP 0) []], .mk (.idP 0) []]]])) = true := by
  decide +kernel

/-- A wrong move in the tree: GLR on `q`.  Rejected. -/
theorem bad_cert_rejected :
    treeCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p]) (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr q)
      [.mk (.impL □p p) [.mk (.glr p) [.mk (.idP 0) []], .mk (.idP 0) []]]]) = false := by
  decide +kernel

/-- A tree of moves that stops early.  Rejected. -/
theorem short_cert_rejected :
    treeCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p]) (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr p) []])
      = false := by
  decide +kernel

/-- A script with a wrong line, and one that stops early.  Rejected. -/
theorem bad_script_rejected :
    scriptCert.check ([] ⇒ [□p ⟶ □□p])
      [⟨0, .impR □p □□p⟩, ⟨0, .glr □p⟩, ⟨0, .glr q⟩, ⟨0, .idP 0⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check ([] ⇒ [□p ⟶ □□p]) [⟨0, .impR □p □□p⟩, ⟨0, .glr □p⟩, ⟨0, .glr p⟩] = false := by
  decide +kernel

/-! ## The axioms of the facts -/

/-- info: R4 passes: converseK_not_derivable depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms GLS.RunTest.converseK_not_derivable

/-- info: R4 passes: lob depends on [propext] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms GLS.RunTest.lob

/-! ## The engine, and a decision -/

/-- info: true -/
#guard_msgs in
#eval match glsEngine.produce ([] ⇒ [□(□p ⟶ p) ⟶ □p]) 0 with
  | .pass _ => true | _ => false

/-- info: true -/
#guard_msgs in
#eval match glsEngine.produce ([] ⇒ [□p ⟶ p]) 0 with
  | .fail _ => true | _ => false

end GLS.RunTest
