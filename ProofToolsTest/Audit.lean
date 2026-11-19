/-
Tests of the audit commands (`ProofTools/Audit/`), each watched passing and
failing and pinned by `#guard_msgs`.  Written 2026-11-19, when the commands
were carried in from lax-logic-in-lean; `#slime` has its own file,
`ProofToolsTest/Slime.lean`.

The subject is `ProofToolsTest/Estate.lean`.  The paths pinned here pass
through that file's declarations only, so they do not depend on how core
Lean proves its own theorems.
-/
import ProofTools.Audit
import ProofToolsTest.Estate

namespace ProofToolsTest.Audit

open ProofToolsTest.Estate

/-! ## Where an axiom enters -/

/-- info: 'ProofToolsTest.Estate.clean' does not depend on 'Classical.choice' -/
#guard_msgs in
#choice_path clean

/--
info: 'ProofToolsTest.Estate.indirect' reaches 'ProofToolsTest.Estate.testAx' by:
  0. indirect    [ProofToolsTest.Estate]
  1. direct    [ProofToolsTest.Estate]
  2. testAx    [ProofToolsTest.Estate]

Read the modules: where they stop being yours is where the axiom enters from the library.
-/
#guard_msgs in
#axiom_path ProofToolsTest.Estate.testAx indirect

/--
info: 'ProofToolsTest.Estate.viaEm2' is tainted through 1 direct dependencies:
  viaEm
-/
#guard_msgs in
#choice_sources viaEm2

/-- info: 'ProofToolsTest.Estate.clean' is choice-free -/
#guard_msgs in
#choice_sources clean

/-! ## Pins, generated

`#axiom_pin` prints a `#guard_msgs` block to paste; the block is itself a
comment, nested in the comment that pins it here. -/

/--
info: /-- info: 'ProofToolsTest.Estate.indirect' depends on axioms: [ProofToolsTest.Estate.testAx] -/
#guard_msgs in
#print axioms ProofToolsTest.Estate.indirect
-/
#guard_msgs in
#axiom_pin indirect

/-- info: #axioms_within ProofToolsTest.Estate.indirect [ProofToolsTest.Estate.testAx] -/
#guard_msgs in
#axioms_within_pin indirect

/-! ## A bound on one declaration

The list says what is allowed, not what is used: a declaration that uses
fewer axioms passes. -/

#guard_msgs in
#axioms_within clean []

#guard_msgs in
#axioms_within clean [propext, Quot.sound]

#guard_msgs in
#axioms_within indirect [ProofToolsTest.Estate.testAx]

#guard_msgs in
#axioms_within viaEm [propext, Classical.choice, Quot.sound]

/--
error: 'ProofToolsTest.Estate.viaEm' depends on Classical.choice, which the bound does not allow.
  declared: [propext, Quot.sound]
Locate the entry with:  #axiom_path Classical.choice ProofToolsTest.Estate.viaEm
-/
#guard_msgs in
#axioms_within viaEm [propext, Quot.sound]

/-! ## The same bound on every declaration of a library -/

/--
info: axiom sweep: 6 declarations, all within [propext, Classical.choice, Quot.sound, ProofToolsTest.Estate.testAx]
-/
#guard_msgs in
#axiom_sweep [ProofToolsTest.Estate]
  allowing [propext, Classical.choice, Quot.sound, ProofToolsTest.Estate.testAx]

/--
error: axiom sweep: 2 of 6 declarations escape the allowance [ProofToolsTest.Estate.testAx]:
  ProofToolsTest.Estate.viaEm2  [ProofToolsTest.Estate]  → propext, Classical.choice, Quot.sound
  ProofToolsTest.Estate.viaEm  [ProofToolsTest.Estate]  → propext, Classical.choice, Quot.sound
-/
#guard_msgs in
#axiom_sweep [ProofToolsTest.Estate] allowing [ProofToolsTest.Estate.testAx]

/-! A sweep that matches no module is an error, never a pass. -/

/--
error: sweep matched no modules; prefixes were [ProofToolsTest.Nowhere].  Is the estate imported by this file?
-/
#guard_msgs in
#axiom_sweep [ProofToolsTest.Nowhere] allowing [propext]

/-! ## Library constants free of `Classical.choice` -/

/-- info: 0 choice-free matches (2 tainted suppressed): -/
#guard_msgs in
#cf_search "ProofToolsTest.Estate" "viaEm"

/--
info: 1 choice-free matches (0 tainted suppressed):
  clean    [ProofToolsTest.Estate]
-/
#guard_msgs in
#cf_search "ProofToolsTest.Estate.clean"

/-! ## An inductive family as inference figures -/

/-- Implication-free natural deduction over numbered atoms: a hypothesis rule
and a cut, enough to show a side condition and two premises. -/
inductive ND : List Nat → Nat → Prop
  | hyp {Γ : List Nat} {a : Nat} (h : a ∈ Γ) : ND Γ a
  | cut {Γ : List Nat} {a b : Nat} (d₁ : ND Γ a) (d₂ : ND (a :: Γ) b) : ND Γ b

/--
info: ProofToolsTest.Audit.ND — 2 rules
hyp
    ────────
    ND Γ a
    if   a ∈ Γ

cut
    ND Γ a      ND (a :: Γ) b
    ───────────────────────────
    ND Γ b
-/
#guard_msgs in
#rules ND

/--
info: ProofToolsTest.Audit.ND — 2 indices, 2 constructors, 0 carrying green slime

  clean: hyp, cut
-/
#guard_msgs in
#slime ND

end ProofToolsTest.Audit
