/-
Tests of the certifier of saturated sets: facts with their sets, sets
that are not certificates rejected in the kernel, and the producer run
on small sequents and compared with the proved search.

Every set in a fact is the producer's output, pasted
(`Refute.srcSet` of `Refute.outcome j`, evaluated 2026-11-26); every
value in a `#guard` is Lean's output.
-/
import DILL.SatRun
import DILL.Refute

namespace DILL.SatTest

open DILL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## The plan's known non-theorems, each with its set -/

/-- `· ; · ⟹ 0` (Pfenning 3.11): the set of that one sequent, which is
the conclusion of no rule. -/
theorem zero : ¬ Nonempty (CF ([] ⨾ [] ⟹ 𝟎)) := noCFBySet.verdict _ [[] ⨾ [] ⟹ 𝟎]

/-- No linear weakening: `· ; p ⟹ 1`. -/
theorem weak_one : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) := noCFBySet.verdict _ [[] ⨾ [p] ⟹ 𝟏]

/-- No linear weakening: `· ; p, q ⟹ p`. -/
theorem weak_init : ¬ Nonempty (CF ([] ⨾ [p, q] ⟹ p)) := noCFBySet.verdict _ [[] ⨾ [p, q] ⟹ p]

/-- No linear contraction: `· ; p ⟹ p ⊗ p`.  Each of the two divisions
of the zone leaves `· ; · ⟹ p` as one premise. -/
theorem contr : ¬ Nonempty (CF ([] ⨾ [p] ⟹ p ⊗ p)) :=
  noCFBySet.verdict _ [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]

/-- Pfenning p. 60: `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)`. -/
theorem pfenning60 : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))) :=
  noCFBySet.verdict _
    [[] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r), [] ⨾ [p ⊸ (q ⊗ r)] ⟹ p ⊸ q, [] ⨾ [] ⟹ p ⊸ q,
      [] ⨾ [] ⟹ p, [] ⨾ [p, p ⊸ (q ⊗ r)] ⟹ q, [] ⨾ [q ⊗ r] ⟹ q, [] ⨾ [q, r] ⟹ q,
      [] ⨾ [p] ⟹ q]

/-- `!` on the right: `· ; p ⟹ !p`.  !R asks for an empty linear zone,
so the sequent is the conclusion of no rule. -/
theorem bang_right : ¬ Nonempty (CF ([] ⨾ [p] ⟹ (!p))) :=
  noCFBySet.verdict _ [[] ⨾ [p] ⟹ (!p)]

/-- The additives: `· ; p ⊕ q ⟹ p`. -/
theorem plus_left : ¬ Nonempty (CF ([] ⨾ [(p ⊕ q)] ⟹ p)) :=
  noCFBySet.verdict _ [[] ⨾ [(p ⊕ q)] ⟹ p, [] ⨾ [q] ⟹ p]

/-- The additives: `· ; p ⟹ p & q`. -/
theorem with_right : ¬ Nonempty (CF ([] ⨾ [p] ⟹ p & q)) :=
  noCFBySet.verdict _ [[] ⨾ [p] ⟹ p & q, [] ⨾ [p] ⟹ q]

/-! ## The same against the calculus with the cuts -/

theorem contr_derivable : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) :=
  noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]

theorem pfenning60_derivable : ¬ Derivable ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) :=
  noDerivableBySet.verdict _
    [[] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r), [] ⨾ [p ⊸ (q ⊗ r)] ⟹ p ⊸ q, [] ⨾ [] ⟹ p ⊸ q,
      [] ⨾ [] ⟹ p, [] ⨾ [p, p ⊸ (q ⊗ r)] ⟹ q, [] ⨾ [q ⊗ r] ⟹ q, [] ⨾ [q, r] ⟹ q,
      [] ⨾ [p] ⟹ q]

theorem bang_right_derivable : ¬ Derivable ([] ⨾ [p] ⟹ (!p)) :=
  noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ (!p)]

/-! ## Sequents with `!` that have a set all the same

The plan lists `· ; !p ⊸ q ⟹ p ⊸ q` among the sequents "with `!` on the
left", for which the search was expected to answer `flag`.  Its `!p` is
never in a linear zone: ⊸L puts it on the right of its first premise.
So it has a saturated set, and the kernel checks it. -/

theorem bang_lolli : ¬ Derivable ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) :=
  noDerivableBySet.verdict _
    [[] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q, [] ⨾ [p, (!p) ⊸ q] ⟹ q, [] ⨾ [] ⟹ (!p), [] ⨾ [p] ⟹ (!p),
      [] ⨾ [] ⟹ p]

/-- A `!` inside a formula of the linear zone, in a branch of ⊕L that the
set does not need. -/
theorem bang_in_plus : ¬ Derivable ([] ⨾ [((!p) ⊕ q)] ⟹ r) :=
  noDerivableBySet.verdict _ [[] ⨾ [((!p) ⊕ q)] ⟹ r, [] ⨾ [q] ⟹ r]

/-! ## A member is counted up to the equivalence -/

/-- The linear zone in another order. -/
theorem perm_accepted : refutedBy [[] ⨾ [p, q] ⟹ p] ([] ⨾ [q, p] ⟹ p) = true := by
  decide +kernel

/-- A ⊗R with a zone of two formulas: four divisions, each with a premise
in the set. -/
theorem tensor_accepted :
    refutedBy [[] ⨾ [p, q] ⟹ p ⊗ r, [] ⨾ [p, q] ⟹ p, [] ⨾ [q] ⟹ r, [] ⨾ [q] ⟹ p, [] ⨾ [] ⟹ p]
      ([] ⨾ [p, q] ⟹ p ⊗ r) = true := by decide +kernel

/-! ## Sets that are not certificates, rejected in the kernel -/

/-- A member is missing: ⊕L at `p ⊕ q` asks for `· ; q ⟹ p` (its other
premise, `· ; p ⟹ p`, is an instance of init). -/
theorem missing_member_rejected :
    refutedBy [[] ⨾ [(p ⊕ q)] ⟹ p] ([] ⨾ [(p ⊕ q)] ⟹ p) = false := by decide +kernel

/-- A member is an instance of init. -/
theorem init_rejected : refutedBy [[] ⨾ [p] ⟹ p] ([] ⨾ [p] ⟹ p) = false := by decide +kernel

/-- A member is the conclusion of 1R. -/
theorem oneR_rejected : refutedBy [[] ⨾ [] ⟹ 𝟏] ([] ⨾ [] ⟹ 𝟏) = false := by decide +kernel

/-- A member is a conclusion of ⊤R. -/
theorem topR_rejected : refutedBy [[] ⨾ [p] ⟹ ⊤] ([] ⨾ [p] ⟹ ⊤) = false := by decide +kernel

/-- A member is a conclusion of 0L. -/
theorem zeroL_rejected : refutedBy [[] ⨾ [p, 𝟎] ⟹ q] ([] ⨾ [p, 𝟎] ⟹ q) = false := by
  decide +kernel

/-- A member has a derivation: `· ; p, p ⊸ q ⟹ q`, with `· ; · ⟹ p` for
the division that gives ⊸L nothing.  The other division has the premises
`· ; p ⟹ p` and `· ; q ⟹ q`, which no set can have. -/
theorem derivable_member_rejected :
    refutedBy [[] ⨾ [p, p ⊸ q] ⟹ q, [] ⨾ [] ⟹ p] ([] ⨾ [p, p ⊸ q] ⟹ q) = false := by
  decide +kernel

/-- The same with the two axioms put in. -/
theorem derivable_member_rejected' :
    refutedBy [[] ⨾ [p, p ⊸ q] ⟹ q, [] ⨾ [] ⟹ p, [] ⨾ [p] ⟹ p, [] ⨾ [q] ⟹ q]
      ([] ⨾ [p, p ⊸ q] ⟹ q) = false := by decide +kernel

/-- The sequent is not a member of the set, which is saturated. -/
theorem not_member_rejected : refutedBy [[] ⨾ [p] ⟹ 𝟏] ([] ⨾ [] ⟹ 𝟏) = false := by
  decide +kernel

/-- The same conclusion and linear zone, another unrestricted zone: not a
member. -/
theorem other_zone_rejected : refutedBy [[] ⨾ [p] ⟹ 𝟏] ([q] ⨾ [p] ⟹ 𝟏) = false := by
  decide +kernel

/-- One division of ⊗R is not covered: `tensor_accepted` without
`· ; q ⟹ r`, the premise for the division of `p, q` into `p` and `q`. -/
theorem tensor_division_rejected :
    refutedBy [[] ⨾ [p, q] ⟹ p ⊗ r, [] ⨾ [p, q] ⟹ p, [] ⨾ [q] ⟹ p, [] ⨾ [] ⟹ p]
      ([] ⨾ [p, q] ⟹ p ⊗ r) = false := by decide +kernel

/-- Contraction without `· ; · ⟹ p`: no division of ⊗R is covered. -/
theorem contr_rejected : refutedBy [[] ⨾ [p] ⟹ p ⊗ p] ([] ⨾ [p] ⟹ p ⊗ p) = false := by
  decide +kernel

/-- One division of ⊸L is not covered: `· ; p ⊸ q ⟹ q` without
`· ; · ⟹ p`. -/
theorem lolli_division_rejected :
    refutedBy [[] ⨾ [p ⊸ q] ⟹ q] ([] ⨾ [p ⊸ q] ⟹ q) = false := by decide +kernel

/-- A formula in the unrestricted zone: the premise of copy is asked for,
and it is not there. -/
theorem copy_rejected : refutedBy [[p] ⨾ [] ⟹ q] ([p] ⨾ [] ⟹ q) = false := by decide +kernel

/-- With that premise, the next one is asked for. -/
theorem copy_rejected' :
    refutedBy [[p] ⨾ [] ⟹ q, [p] ⨾ [p] ⟹ q] ([p] ⨾ [] ⟹ q) = false := by decide +kernel

/-- `!` in the linear zone: the premise of !L is asked for. -/
theorem bangL_rejected : refutedBy [[] ⨾ [(!p)] ⟹ q] ([] ⨾ [(!p)] ⟹ q) = false := by
  decide +kernel

/-- A set for `· ; !p ⟹ p`, which has a derivation (!L, copy, init): the
premise of !L, `p ; · ⟹ p`, asks for the premise of copy, an instance of
init. -/
theorem bangL_rejected' :
    refutedBy [[] ⨾ [(!p)] ⟹ p, [p] ⨾ [] ⟹ p] ([] ⨾ [(!p)] ⟹ p) = false := by decide +kernel

/-! ## The producer

Compiled evaluation: the producer is code, and is not run by the kernel. -/

def isRefuted (j : Seq) : Bool :=
  match Refute.outcome j with
  | .refuted _ => true
  | _ => false

def isDerivable (j : Seq) : Bool :=
  match Refute.outcome j with
  | .derivable => true
  | _ => false

def isNoSet (j : Seq) : Bool :=
  match Refute.outcome j with
  | .noSet _ => true
  | _ => false

-- The sets of the facts above are the producer's.
#guard refuteSet ([] ⨾ [p] ⟹ p ⊗ p) == some [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]
#guard refuteSet ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) == some
  [[] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q, [] ⨾ [p, (!p) ⊸ q] ⟹ q, [] ⨾ [] ⟹ (!p), [] ⨾ [p] ⟹ (!p), [] ⨾ [] ⟹ p]
#guard (refuteSet ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))).map (·.length) == some 8

-- Sequents with a derivation: no set, and the producer says why.
#guard isDerivable ([] ⨾ [p ⊸ q] ⟹ p ⊸ q)
#guard isDerivable ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard isDerivable ([] ⨾ [p & q] ⟹ p)
#guard isDerivable ([] ⨾ [] ⟹ (!⊤))

-- No set: the unrestricted zone is not empty; `!` is met in a linear zone
-- (the first of the three has a derivation, the other two have none).
#guard isNoSet ([p] ⨾ [] ⟹ q)
#guard isNoSet ([] ⨾ [(!p)] ⟹ p)
#guard isNoSet ([] ⨾ [(!p)] ⟹ q)
#guard isNoSet ([] ⨾ [] ⟹ (p ⊸ q) ⊸ (!p) ⊸ r)

/-- Small formulas without `!`. -/
def forms : List Form :=
  [p, q, 𝟏, ⊤, 𝟎, p ⊗ q, p ⊸ q, p & q, (p ⊕ q), p ⊸ p, q ⊗ p, 𝟏 ⊸ p, p ⊸ 𝟎, (p ⊸ q) ⊸ q, p ⊗ p]

/-- The sequents `· ; Δ ⟹ C` with `Δ` of at most two of them and `C` one
of them. -/
def smallSeqs : List Seq :=
  ([[]] ++ forms.map (fun a => [a]) ++ forms.flatMap fun a => forms.map fun b => [a, b]).flatMap
    fun Δ => forms.map fun C => ([] ⨾ Δ ⟹ C)

-- On each of these 3615 sequents the producer gives a set that the check
-- accepts exactly where the proved search for the fragment without `!`
-- (`Dec.searchCF`, `DILL/Decide.lean`) finds no derivation: 2557 of them.
-- It never makes a set that the check rejects.
#guard smallSeqs.length == 3615
#guard smallSeqs.all fun j => (refuteSet j).isSome == (Dec.searchCF j.lin j.goal).isNone
#guard (smallSeqs.filter fun j => (refuteSet j).isSome).length == 2557
#guard smallSeqs.all fun j => isRefuted j || isDerivable j

-- R1: the producer counts no domain.
#certify_domain DILL.refuteSet

#certify_axioms DILL.SatTest.zero
#certify_axioms DILL.SatTest.contr
#certify_axioms DILL.SatTest.pfenning60
#certify_axioms DILL.SatTest.bang_right
#certify_axioms DILL.SatTest.pfenning60_derivable
#certify_axioms DILL.SatTest.bang_lolli
#certify_axioms DILL.SatTest.bang_in_plus
#certify_structural DILL.SatTest.pfenning60

end DILL.SatTest
