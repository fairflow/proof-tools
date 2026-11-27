/-
A certifier and a search over sets.

The premise of GLR holds `B, □B` for every boxed formula of the
antecedent, with repetitions, so the sequents of a derivation in GLS can
double from one GLR to the next (`campaign/measurements.md`).  For the
proposition "there is a derivation in GLS" that size is not needed: a
sequent less its repeated formulas is derivable only if the sequent is
(weakening).  Here: the proof system `SS`, whose `step` is that of GLS
with the repeated formulas of each premise removed; that its moves are
sound for derivability in GLS; and the search as a producer.  (The
decisions of derivability and of validity by that search are in
`GLS/Run.lean`.)

Theory file: it ends with its bound on axioms.
-/
import GLS.Run
import GLS.Structural

namespace GLS

open ProofTools ProofTools.Explore

/-! ## Removing repeated formulas

`dedup`, `Seq.dedup` and their lemmas are in `GLS/Decide.lean`. -/

/-- **A sequent is derivable if it is so less its repeated formulas**:
weakening. -/
theorem derivable_of_dedup {s : Seq} (h : Derivable s.dedup) : Derivable s :=
  let ⟨d⟩ := h
  ⟨(d.wk (dropped s.ant) (dropped s.suc) s.ant s.suc (dedup_perm _) (dedup_perm _)).1⟩

/-! ## The proof system over sets, and its certifier -/

/-- One step over sets: the step of GLS, with the repeated formulas of
each premise removed. -/
def stepSet (m : Move) (j : Seq) : Except String (List Seq) :=
  if (m.rule j).ok then .ok ((m.rule j).prems.map Seq.dedup) else .error (m.rule j).why

/-- **GLS over sets, as a proof system**: the moves of GLS, the step
`stepSet`. -/
abbrev SS : ProofSystem where
  Judg := Seq
  Move := Move
  step := stepSet

/-- **The moves over sets are sound for derivability in GLS.** -/
theorem stepSet_sound : SS.Sound Derivable := by
  intro m j ps h hps
  have h' : stepSet m j = .ok ps := h
  unfold stepSet at h'
  split at h'
  · next hok =>
    have e : ps = (m.rule j).prems.map Seq.dedup := (Except.ok.inj h').symm
    apply step_sound_derivable m j (m.rule j).prems (step_of hok)
    intro q hq
    exact derivable_of_dedup (hps _ (e ▸ List.mem_map_of_mem hq))
  · cases h'

/-- **Trees of moves over sets, checked**: a tree that `Cert.check`
accepts for `s` in `SS` shows that `s` is derivable in GLS. -/
def setCert : Certify.Certifier Seq (Cert SS) Derivable := Cert.certifier stepSet_sound.soundT

#certify_structural GLS.setCert
#certify_statement GLS.setCert

/-! ## The search over sets, and the decisions by it

The search is `searchD` of `GLS/Decide.lean`, which is proved: it ends,
and what it returns is a tree of moves that replays at the sequent, or a
tree at whose root the sequent is false (S28, `certOrRef`).  Until
2026-11-27 a search of the same steps stood here that was not proved,
with its answers checked and the search over multisets behind it. -/

/-- **The producer over sets**: the answer of `certOrRef`, without its
proof.  (It always answers; the type is the one the callers had.) -/
def produceSet (s : Seq) : Option (Cert SS ⊕ Tree) :=
  some (match certOrRef s with
    | .inl c => .inl c.1
    | .inr r => .inr r.1)

end GLS

#axioms_within_file [propext, Quot.sound]
