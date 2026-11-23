/-
Completeness of system K, decidability of validity, and cut elimination.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Theorem 2.23
(completeness), p. 17; Corollary 2.25 (decidability), p. 19; Theorem 2.35
(cut elimination), p. 27, by the route of p. 19: "cut admissibility is an
easy corollary of the completeness theorem".  All at `X = ∅`.  Theory
file: it ends with its bound on axioms.
-/
import BrunnlerK.Search

namespace BrunnlerK

/-- **A proof or a countermodel** (Theorem 2.23, at `X = ∅`): the search. -/
def proofOrRefutation : ProofOrRefutation := search

/-- A proof in system K of a valid sequent, as data: the search's, since
a refutation would be a state of a two-valued model where the sequent is
not true. -/
def complete {Γ : NSeq} (h : Valid Γ) : K Γ :=
  match search Γ with
  | .inl d => d
  | .inr r => absurd (h treeModel treeModel_twoValued r.tree) r.refutes

/-- **Completeness** (Theorem 2.23 (i), at `X = ∅`): `Valid Γ → K ⊢ Γ`. -/
theorem completeness : Completeness := fun _ h => ⟨complete h⟩

/-- **Validity is decidable** (Corollary 2.25, at `X = ∅`). -/
@[reducible] def validDecidable : ValidDecidable := fun Γ =>
  match search Γ with
  | .inl d => isTrue (soundness Γ d)
  | .inr r => isFalse fun h => r.refutes (h treeModel treeModel_twoValued r.tree)

instance (Γ : NSeq) : Decidable (Valid Γ) := validDecidable Γ

/-- A proof in system K from a proof in K with cut, as data: the search's
proof of the sequent, which is valid because K with cut is sound.  The
cuts are not removed one by one: the proof with cuts is used only to know
that the search cannot end in a refutation. -/
def cutElim {Γ : NSeq} (d : Kcut Γ) : K Γ := complete (soundnessCut Γ d)

/-- **Cut elimination** (Theorem 2.35, at `X = ∅`), as "`cut` is
admissible": `K + cut ⊢ Γ → K ⊢ Γ`. -/
theorem cutElimination : CutElimination := fun _ d => ⟨cutElim d⟩

/-- A sequent is valid exactly if system K proves it. -/
theorem valid_iff_derivable (Γ : NSeq) : Valid Γ ↔ Nonempty (K Γ) :=
  ⟨completeness Γ, fun ⟨d⟩ => soundness Γ d⟩

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
