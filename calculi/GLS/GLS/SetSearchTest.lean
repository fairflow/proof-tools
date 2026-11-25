/-
Tests of the certifier and the search over sets (`GLS/SetSearch.lean`):
the screen of its one obligation, its answers against the first search's,
a corrupted certificate rejected, and the kernel running the decision.
-/
import GLS.SetSearch
import GLS.Screen
import GLS.Corpus.Basic

namespace GLS.SetSearchTest

open ProofTools ProofTools.Explore GLS GLS.Screen

/-! ## The screen of `SS.Sound Derivable`, before its proof was used

For each small sequent and each move that applies: if the bounded search
derives every premise less its repeated formulas, it derives the
conclusion. -/

#guard seqsSmall.all fun s =>
  (candidates s).all fun m =>
    match (SS.step m s).toOption with
    | some ps => !(ps.all (within 7)) || within 8 s
    | none => true

-- the screen can say no: with "some premise" for "every premise" it fails
#guard !(seqsSmall.all fun s =>
  (candidates s).all fun m =>
    match (SS.step m s).toOption with
    | some ps => !(ps.any (within 7)) || within 8 s
    | none => true)

/-! ## The search over sets answers as the first search does -/

/-- The two searches agree on a sequent: both a derivation, or both a
tree; and what the search over sets returns is accepted by its checker. -/
def agree (s : Seq) : Bool :=
  match produceSet s, proofOrRef s with
  | some (.inl c), .inl _ => setCert.check s c
  | some (.inr t), .inr _ => noDerivable.check s t
  | _, _ => false

#guard seqsSmall.all agree
#guard Corpus.entries.all fun e => agree e.seq
#guard [2, 5, 9].all fun n => agree (Corpus.boxChain n) && agree (Corpus.kChain n) &&
  agree (Corpus.consis n)
#guard agree (Corpus.binTree 3)

/-! ## A fact by the certifier, and corrupted certificates rejected -/

/-- `⇒ □p → □□□p`, by a tree of moves over sets. -/
theorem box3 : Derivable ([] ⇒ [□p ⟶ □□□p]) :=
  setCert.verdict _ (.mk (.impR □p □□□p) [.mk (.glr □□p) [.mk (.glr □p) [.mk (.glr p)
    [.mk (.idP 0) []]]]])

/-- info: R4 passes: box3 depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms GLS.SetSearchTest.box3

/-- A wrong move: the last GLR on `q`.  Rejected. -/
theorem bad_set_cert_rejected :
    setCert.check ([] ⇒ [□p ⟶ □□□p]) (.mk (.impR □p □□□p) [.mk (.glr □□p) [.mk (.glr □p)
      [.mk (.glr q) [.mk (.idP 0) []]]]]) = false := by
  decide +kernel

/-- A tree that stops early.  Rejected. -/
theorem short_set_cert_rejected :
    setCert.check ([] ⇒ [□p ⟶ □□□p]) (.mk (.impR □p □□□p) [.mk (.glr □□p) [.mk (.glr □p) []]])
      = false := by
  decide +kernel

/-- No tree of moves is accepted for a sequent that is not derivable:
here the identity's tree, and two others, for `⇒ □p → p`. -/
theorem underivable_set_cert_rejected :
    ([idCert (□p ⟶ p), .mk (.impR □p p) [], .mk (.impR □p p) [.mk (.glr p) [.mk (.idP 0) []]]].all
      fun c => !setCert.check ([] ⇒ [□p ⟶ p]) c) = true := by
  decide +kernel

/-! ## The kernel running the decision over sets -/

instance (s : Seq) : Decidable (Derivable s) := derivableDecidableFast s

example : Derivable (Corpus.boxChain 24) := by decide +kernel
example : ¬ Derivable (Corpus.consis 24) := by decide +kernel

end GLS.SetSearchTest
