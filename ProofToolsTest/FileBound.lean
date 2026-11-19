/-
Tests of `#axioms_within_file` (`ProofTools/Audit/FileBound.lean`), pinned by
`#guard_msgs`.  The command checks the file it stands in, so this file is
its own subject: the first test must come before any declaration.

Only axioms and theorems are declared here, so that nothing Lean generates
enters the lists; generated declarations are the subject of
`ProofToolsTest/FileBoundGenerated.lean`.
-/
import ProofTools.Audit.FileBound

/-! ## With nothing above it, an error, never a pass -/

/--
error: #axioms_within_file checks the declarations of this file that precede it, and there are none.  Put it at the end of the file.
-/
#guard_msgs in
#axioms_within_file [propext, Quot.sound]

namespace ProofToolsTest.FileBound

/-- An axiom of the test's own, harmless. -/
axiom testAx : True

/-- Uses no axiom. -/
theorem clean : 1 + 1 = 2 := rfl

/-- Uses `testAx`. -/
theorem direct : True := testAx

/-- Depends on `Classical.choice`, through `Classical.em`. -/
theorem viaEm (p : Prop) : p ∨ ¬p := Classical.em p

/-- Depends on it through `viaEm`. -/
theorem viaEm2 (p : Prop) : ¬p ∨ p := (viaEm p).symm

/-! ## The bound holds: silence

The list says what is allowed, not what is used. -/

#guard_msgs in
#axioms_within_file [propext, Classical.choice, Quot.sound, testAx]

/-! ## The bound fails: each declaration outside it, with the axioms that are

`testAx` is reported too: an axiom the file declares must be in its bound. -/

/--
error: 4 declarations of this file depend on axioms outside the bound [propext, Quot.sound]:
  ProofToolsTest.FileBound.direct  → ProofToolsTest.FileBound.testAx
  ProofToolsTest.FileBound.testAx  → ProofToolsTest.FileBound.testAx
  ProofToolsTest.FileBound.viaEm  → Classical.choice
  ProofToolsTest.FileBound.viaEm2  → Classical.choice
Locate an entry with `#axiom_path`; hold a declaration out with `except [name]`.
-/
#guard_msgs in
#axioms_within_file [propext, Quot.sound]

/-! ## Exceptions

Held out by name; the rest is still checked. -/

#guard_msgs in
#axioms_within_file [propext, Quot.sound] except [testAx, direct, viaEm, viaEm2]

/-! The axioms of a held-out declaration reach what uses it: with `testAx`
held out, `direct` is reported. -/

/--
error: 1 declaration of this file depends on axioms outside the bound [propext, Classical.choice, Quot.sound]:
  ProofToolsTest.FileBound.direct  → ProofToolsTest.FileBound.testAx
Locate an entry with `#axiom_path`; hold a declaration out with `except [name]`.
-/
#guard_msgs in
#axioms_within_file [propext, Classical.choice, Quot.sound] except [testAx]

/-! An exception must be a declaration of this file. -/

/--
error: 'Nat.add_comm' is not a declaration of this file, so it cannot be held out of this file's bound.
-/
#guard_msgs in
#axioms_within_file [propext, Quot.sound] except [viaEm, Nat.add_comm]

end ProofToolsTest.FileBound
