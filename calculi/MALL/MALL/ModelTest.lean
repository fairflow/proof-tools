/-
Tests of the certifier of finite phase structures: facts with their
structures, and negative tests, rejected in the kernel.
-/
import MALL.ModelRun
import MALL.Corpus.Basic

namespace MALL.ModelTest

open MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1

/-- `⊢ 1, 1` is refuted in ℤ/2 with the antiphases {1}: there `1` is {0},
its dual is {1}, and `1 ⅋ 1` is the dual of {1 + 1} = {0}, which is {1}:
the unit 0 is not in it. -/
theorem one_one : ¬ Derivable [𝟏, 𝟏] := noDerivableBy.verdict _ ⟨1, [false, true], []⟩

theorem one_one_not_valid : ¬ Valid [𝟏, 𝟏] := noValidBy.verdict _ ⟨1, [false, true], []⟩

/-- "A ⊸ A ⊗ A is not derivable" (Girard, p. 5): in ℤ/2 with the
antiphases {0} and `p` = {1}, a letter counts 1, and `p⊥ ⅋ (p ⊗ p)` counts
1 + 1 + 1. -/
theorem p5 : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
  noDerivableBy.verdict _ ⟨1, [true, false], [[false, true]]⟩

/-- Contraction: `⊢ p ⊕ p⊥`, in the same structure. -/
theorem contraction : ¬ Derivable [p ⊕ pᗮ] :=
  noDerivableBy.verdict _ ⟨1, [true, false], [[false, true]]⟩

/-- A member of a family that neither search settles within its deadline
(`campaign/measurements.md`): `chainBad 16`, 18 formulas.  In ℤ/2 with the
antiphases {0}, the last letter counts 1 and the others 0. -/
theorem chainBad16 : ¬ Derivable (Corpus.chainBad 16) :=
  noDerivableBy.verdict _ ⟨1, [true, false], List.replicate 17 [true, false] ++ [[false, true]]⟩

-- The producer finds another: the letter before the last counts 1 (it
-- too occurs once).  The value is Lean's output.  (Compiled evaluation:
-- the producer is code, and is not run by the kernel.)
#guard refuteBy (Corpus.chainBad 16) ==
  some ⟨1, [true, false], List.replicate 16 [true, false] ++ [[false, true], [true, false]]⟩

/-- A structure that does not refute the sequent: ℤ/2 with the antiphases
{0}, where `1 ⅋ 1` holds.  Rejected. -/
theorem bad_model_rejected : noDerivableBy.check [𝟏, 𝟏] ⟨1, [true, false], []⟩ = false := by
  decide +kernel

/-- No structure is accepted against a derivable sequent: here, every
structure on ℤ/1, ℤ/2, ℤ/3 for two letters (584 of them), against four
sequents. -/
theorem derivable_never_refuted :
    ([[p, pᗮ], [𝟏], [pᗮ ⅋ (p & p)], [(p ⊗ q)ᗮ, q ⊗ p]].all fun Γ =>
      ([1, 2, 3].flatMap fun m => allOn m 2).all fun z => !noDerivableBy.check Γ z) = true := by
  decide +kernel

#guard ([1, 2, 3].flatMap fun m => allOn m 2).length == 584

#certify_axioms MALL.ModelTest.one_one
#certify_axioms MALL.ModelTest.one_one_not_valid
#certify_axioms MALL.ModelTest.p5
#certify_axioms MALL.ModelTest.chainBad16

end MALL.ModelTest
