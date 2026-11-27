/-
Saturated sets of sequents as certificates: the certifiers.

* `noCFBySet.verdict j D : Nonempty (CF j) → False`: the kernel checks
  that `j` is a member of `D` and that `D` is saturated
  (`DILL/Saturated.lean`); then `j` has no derivation without cut
  (`not_cf_of_refutedBy`, proved by induction on such a derivation, with
  no semantics and no cut).  The check that is run is `refutedFast`
  (`DILL/SatFast.lean`): the same questions, asked of the set kept in a
  tree, and proved sound for the definition (`refutedFast_sound`).
* `noDerivableBySet.verdict j D : Derivable j → False`: the same check;
  the theorem goes through cut elimination (`cutElimination`,
  `DILL/Cut.lean`): a derivation with the cuts gives one without.

The certificate is a list of sequents, written as literal data.  It is
for the sequents that have a saturated set: those with an empty
unrestricted zone whose failed search needs no sequent with `!` in a
linear zone (`DILL/Saturated.lean`, the header).  The producer is
`refuteSet` (`DILL/Refute.lean`), which this file does not import.

Theory file: it ends with its bound on axioms.
-/
import LeanCertify
import DILL.SatFast
import DILL.Cut

namespace DILL

/-- **Saturated sets, checked against a derivation without cut.** -/
def noCFBySet : Certify.Certifier Seq (List Seq) (fun j => Nonempty (CF j) → False) where
  check j D := refutedFast D j
  sound j D h := not_cf_of_refutedFast D j h

/-- **Saturated sets, checked against a derivation** of the calculus with
the two cuts: by cut elimination. -/
def noDerivableBySet : Certify.Certifier Seq (List Seq) (fun j => Derivable j → False) where
  check j D := refutedFast D j
  sound j D h := fun ⟨d⟩ => not_cf_of_refutedFast D j h ⟨cutElimination j d⟩

/-- The check of `noCFBySet` from its parts (`Sat.headOk`, `Sat.restOk`):
for a set whose check in one run of the kernel would keep too much in
memory, `dillrun prove` states the parts as theorems of their own and
joins them with this.  Stated of the certifier's check, so that the
facts take it as it is. -/
theorem noCFBySet_check_of_parts {D : List Seq} {j : Seq} (h₀ : Sat.headOk D j = true)
    (h : Sat.restOk D (D.map Sat.canon) = true) : noCFBySet.check j D = true :=
  refutedFast_of_parts h₀ h

#certify_structural DILL.noCFBySet
#certify_statement DILL.noCFBySet
#certify_structural DILL.noDerivableBySet
#certify_statement DILL.noDerivableBySet

end DILL

#axioms_within_file [propext, Quot.sound]
