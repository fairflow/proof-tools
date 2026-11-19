/-
A small estate for `ProofToolsTest/Audit.lean` to audit: `#axiom_sweep` reads
imported modules only, so its subject is a module of its own.  The axiom
`testAx` is declared here so that the paths pinned in the tests pass through
this file's declarations only, and do not depend on how core Lean proves
`Classical.em`.
-/

namespace ProofToolsTest.Estate

/-- An axiom of the test's own, harmless. -/
axiom testAx : True

/-- Uses no axiom. -/
theorem clean : 1 + 1 = 2 := rfl

/-- Uses `testAx` directly. -/
theorem direct : True := testAx

/-- Reaches `testAx` through `direct`. -/
theorem indirect : True ∧ True := ⟨direct, direct⟩

/-- Depends on `Classical.choice`, through `Classical.em`. -/
theorem viaEm (p : Prop) : p ∨ ¬p := Classical.em p

/-- Depends on it through `viaEm`. -/
theorem viaEm2 (p : Prop) : ¬p ∨ p := (viaEm p).symm

end ProofToolsTest.Estate
