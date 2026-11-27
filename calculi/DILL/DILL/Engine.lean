/-
Both sides of the Run stage and the producer, as one engine: level 2.

* **For a derivation**: a script (or a tree of moves), checked by running
  `step`; its soundness is S1 (`DILL/Run.lean`).
* **Against a derivation**: a saturated set of sequents, checked by
  `refutedFast` (`DILL/SatFast.lean`: the check of the definition
  `refutedBy`, as it is run, proved sound for it); its soundness is
  `not_cf_of_refutedBy` with cut elimination (`DILL/SatRun.lean`).
* **The producer**: the search with a budget on copy; where it finds
  nothing at the budget, the producer of saturated sets; where that gives
  no set, `flag`.  Each answer is checked before it is handed on.

There is no theorem that one side always answers, and there cannot be
one: with `!` derivability is undecidable (Lincoln, Mitchell, Scedrov,
Shankar 1992, Corollary 3.8), and a sound check on each side with a
complete pair of producers would decide it.  What is proved instead is
that one side always answers on the fragment where derivability is
decided: an empty unrestricted zone and no `!` (`decidedBangFree`, by
the search of `DILL/Decide.lean`; its "no" is the kernel running that
search, with no certificate written).

Theory file: it ends with its bound on axioms.
-/
import DILL.Run
import DILL.SatRun
import DILL.Refute
import DILL.Goals

namespace DILL

open ProofTools ProofTools.Explore

/-- **The producer of the engine**: at the budget `n` of copies along a
branch, `pass` with the script of a checked tree; otherwise `fail` with a
saturated set that the check accepts; otherwise `flag`. -/
def produce (j : Seq) (n : Nat) : Certify.Verdict (Script S) (List Seq) :=
  match Run.produce j n with
  | .pass ls => .pass ls
  | _ =>
    match refuteSet j with
    | some D => if noDerivableBySet.check j D then .fail D else .flag
    | none => .flag

/-- **Both sides and the producer, as one engine**, for derivability with
the cuts. -/
def dillEngine : Certify.Engine Seq (Script S) (List Seq) Derivable :=
  engine step_sound_derivable noDerivableBySet produce

#certify_domain DILL.produce

/-- The decision of the fragment with an empty unrestricted zone and no
`!`, as a value: `some b` in the fragment, with `b` whether there is a
derivation; `none` outside it. -/
def decBF (j : Seq) : Option Bool :=
  if h : j.unr = [] ∧ ∀ A ∈ j.goal :: j.lin, A.bangFree = true then
    some (@decide _ (bangFreeDecidable j.lin j.goal h.2))
  else none

theorem decBF_false {j : Seq} (h : decBF j = some false) : ¬ Derivable j := by
  obtain ⟨Γ, Δ, C⟩ := j
  unfold decBF at h
  split at h
  · next hfrag =>
    injection h with h'
    intro hd
    exact (@of_decide_eq_false _ (bangFreeDecidable _ _ hfrag.2) h') (hfrag.1 ▸ hd)
  · cases h

/-- **Against a derivation, where derivability is decided**: the check is
the decision procedure of the fragment with an empty unrestricted zone
and no `!`, and the certificate carries nothing.  Outside the fragment
the check refuses. -/
def noDerivableDec : Certify.Certifier Seq Unit (fun j => Derivable j → False) where
  check j _ := decBF j == some false
  sound _ _ hc := decBF_false (eq_of_beq hc)

/-- **One side always answers where `!` does not occur and the
unrestricted zone is empty**: a tree of moves that checks, or the
decision against a derivation. -/
theorem decidedBangFree (Δ : List Form) (C : Form) (hb : ∀ A ∈ C :: Δ, A.bangFree = true) :
    (∃ c, treeCert.check ([] ⨾ Δ ⟹ C) c = true) ∨
      noDerivableDec.check ([] ⨾ Δ ⟹ C) () = true := by
  cases hdec : @decide _ (bangFreeDecidable Δ C hb) with
  | true =>
    have hd : Derivable ([] ⨾ Δ ⟹ C) := @of_decide_eq_true _ (_) hdec
    obtain ⟨d⟩ := hd
    obtain ⟨der⟩ := famToDer _ d
    exact .inl ⟨der.cert, Att.check_cert der⟩
  | false =>
    refine .inr ?_
    have h : decBF ([] ⨾ Δ ⟹ C) = some false := by
      unfold decBF
      rw [dif_pos (⟨rfl, hb⟩ : ([] : List Form) = [] ∧ ∀ A ∈ C :: Δ, A.bangFree = true)]
      exact congrArg some hdec
    show (decBF ([] ⨾ Δ ⟹ C) == some false) = true
    rw [h]
    rfl

#certify_structural DILL.noDerivableDec
#certify_statement DILL.noDerivableDec

end DILL

#axioms_within_file [propext, Quot.sound]
