/-
Tests of the certifier of saturated sets: facts with their sets, negative
tests rejected in the kernel, an instance of the completeness theorem run
by the kernel, and the producer and the computed structure on the corpus.
-/
import MALL.Refute
import MALL.Corpus.Basic

namespace MALL.SatTest

open MALL

abbrev a : Form := .atom 0

/-! ## Facts, each with its set -/

/-- `⊢ 1, 1`: the set of that one sequent.  The rule 1 does not conclude
it, and it is the conclusion of no other rule. -/
theorem one_one : ¬ Derivable [𝟏, 𝟏] := noDerivableBySet.verdict _ [[𝟏, 𝟏]]

/-- Contraction: `⊢ a ⊕ a⊥`, with the premises of its two rules. -/
theorem contraction : ¬ Derivable [a ⊕ aᗮ] :=
  noDerivableBySet.verdict _ [[aᗮ], [a ⊕ aᗮ], [a]]

/-- "A ⊸ A ⊗ A is not derivable" (Girard, p. 5). -/
theorem p5 : ¬ Derivable [aᗮ ⅋ (a ⊗ a)] :=
  noDerivableBySet.verdict _ [[aᗮ, a ⊗ a], [a], [aᗮ ⅋ (a ⊗ a)]]

theorem p5_not_valid : ¬ Valid [aᗮ ⅋ (a ⊗ a)] :=
  noValidBySet.verdict _ [[aᗮ, a ⊗ a], [a], [aᗮ ⅋ (a ⊗ a)]]

/-- The countermodel itself: a finite phase structure in which the
sequent does not hold. -/
theorem contraction_countermodel : ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat [a ⊕ aᗮ] :=
  countermodel_of_refutedBy (D := [[aᗮ], [a ⊕ aᗮ], [a]]) (by decide +kernel)

/-! ## Sets that are not certificates, rejected -/

/-- The premise of 2⊕ is missing. -/
theorem missing_premise_rejected : refutedBy [[a ⊕ aᗮ], [a]] [a ⊕ aᗮ] = false := by
  decide +kernel

/-- A member is a logical axiom. -/
theorem axiom_rejected : refutedBy [[a, aᗮ]] [a, aᗮ] = false := by decide +kernel

/-- A member is the conclusion of the rule 1. -/
theorem one_rejected : refutedBy [[𝟏]] [𝟏] = false := by decide +kernel

/-- A member has ⊤. -/
theorem top_rejected : refutedBy [[⊤, a]] [⊤, a] = false := by decide +kernel

/-- The sequent is not a member of the set, which is saturated. -/
theorem not_member_rejected : refutedBy [[𝟏, 𝟏]] [𝟏] = false := by decide +kernel

/-- A ⊗ with a context of one formula: `⊢ a ⊗ a, a⊥`, with `⊢ a`.  Each of
the two ways to divide the context leaves `⊢ a` as one premise, so the two
sequents are a saturated set. -/
theorem tensor_accepted : refutedBy [[a ⊗ a, aᗮ], [a]] [a ⊗ a, aᗮ] = true := by decide +kernel

/-- The same without `⊢ a`: rejected. -/
theorem tensor_rejected : refutedBy [[a ⊗ a, aᗮ]] [a ⊗ a, aᗮ] = false := by decide +kernel

/-! ## The completeness theorem, at an instance, run by the kernel -/

/-- The full refutation of `⊢ 1, 1` (the small sequents with no
derivation) is a certificate. -/
theorem full_one_one : refutedBy (fullRefutation [𝟏, 𝟏]) [𝟏, 𝟏] = true := by decide +kernel

/-! ## The producer and the computed structure, on the corpus

Compiled evaluation: the producer is code, and is not run by the kernel. -/

-- For every entry of the corpus with no derivation, the producer gives a
-- set that the check accepts.
#guard (Corpus.entries.filter (!·.derivable)).all fun e =>
  match refuteSet e.seq with
  | some D => refutedBy D e.seq
  | none => false

-- For every entry with a derivation, it gives none.
#guard (Corpus.entries.filter (·.derivable)).all fun e => (refuteSet e.seq).isNone

-- In the phase structure that each such set presents, computed by tables
-- (`Table`, which is not proved): no member of the set holds, as
-- `satModel_refutes` proves; and every derivable entry of the corpus holds,
-- as soundness proves.
#guard (Corpus.entries.filter (!·.derivable)).all fun e =>
  match refuteSet e.seq with
  | some D =>
    let T := Table.ofSet D
    D.all (fun d => !T.holds d) && (Corpus.entries.filter (·.derivable)).all fun f => T.holds f.seq
  | none => false

-- The structure of the set for contraction: five phases; the antiphases
-- are the unit and ∞; the fact of `a` is every phase but the unit, and so
-- is the interpretation of `a ⊕ a⊥`.  The values are Lean's output.
#guard
  let T := Table.ofSet [[a ⊕ aᗮ], [a], [aᗮ]]
  (T.card, T.showSet T.bot, T.showSet (T.val 0), T.showSet (T.interp (a ⊕ aᗮ))) ==
    (5, "{⊢, ∞}", "{⊢ p ⊕ p⊥, ⊢ p, ⊢ p⊥, ∞}", "{⊢ p ⊕ p⊥, ⊢ p, ⊢ p⊥, ∞}")

#certify_axioms MALL.SatTest.one_one
#certify_axioms MALL.SatTest.contraction
#certify_axioms MALL.SatTest.p5
#certify_axioms MALL.SatTest.contraction_countermodel
#certify_axioms MALL.certified

end MALL.SatTest
