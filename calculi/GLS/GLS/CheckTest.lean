/-
Screens and guards of the two checks that the program and the kernel
run: truth at the root of a tree by the marks (`GLS/Table.lean`), and the
replay of a tree of moves by counts (`GLS/Counts.lean`), each beside the
definition it is proved equal to.

Code, not theory: nothing here is trusted, and the file has no bound on
axioms.  A screen that fails is a `#guard` that fails the build.  The
statements are S25 to S27 of `campaign/statements.md`.
-/
import GLS.Table
import GLS.Counts
import GLS.Corpus.Basic
import GLS.SetSearch
import GLS.Screen

namespace GLS.CheckTest

open ProofTools ProofTools.Explore GLS GLS.Corpus
open GLS.Screen (seqsSmall worlds trees2 forms2)

/-! ## S25, S26: truth by the marks -/

-- S25: on 19 formulas and 200 worlds
#guard forms2.all fun A => ((worlds trees2).take 200).all fun w => A.holdsT w == A.holds w

-- S26: on 1 024 sequents and 200 worlds; both answers occur
#guard seqsSmall.length == 1024
#guard seqsSmall.all fun j => ((worlds trees2).take 200).all fun w => j.refutedT w == j.refutedAt w
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => j.refutedT w
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => !j.refutedT w

/-- The tree of the search over sets, where it finds one. -/
def treeOf (j : Seq) : Option Tree :=
  match produceSet j with
  | some (.inr t) => some t
  | _ => none

-- on the trees that the search returns, for the entries of the corpus
-- and for members of the families: accepted by both
#guard (entries.map (·.seq) ++ [consis 3, consis 8, consis 12, binTree 2, binTree 3]).all fun j =>
  match treeOf j with
  | some t => j.refutedT t && j.refutedAt t
  | none => true
-- a tree too short is refused by both
#guard (treeOf (consis 3)).all fun t => !(consis 4).refutedT t && !(consis 4).refutedAt t
-- where the definition, run as it is written, does not end: 65 worlds,
-- 64 nested boxes
#guard (treeOf (consis 64)).all fun t => (consis 64).refutedT t
#guard (treeOf (consis 63)).all fun t => !(consis 64).refutedT t

/-! ## S27: the replay by counts -/

/-- The tree of moves of the search over sets, where it finds one. -/
def movesOf (j : Seq) : Option (Cert S) :=
  match produceSet j with
  | some (.inl c) => some c
  | _ => none

/-- The two replays agree on a sequent and a tree of moves. -/
def agree (j : Seq) (c : Cert S) : Bool := j.countCheck c == Cert.check j c

/-- A sequent with each side written twice: every count is 2 or more. -/
def twice (j : Seq) : Seq := j.ant ++ j.ant ⇒ j.suc ++ j.suc

/-- The trees of moves of the search for the small sequents. -/
def smallMoves : List (Seq × Cert S) :=
  seqsSmall.filterMap fun j => (movesOf j).map fun c => (j, c)

#guard smallMoves.length == 385
-- each tree at its own sequent: the two replays agree, and both accept
-- some and refuse none of what the other accepts
#guard smallMoves.all fun (j, c) => agree j c
#guard smallMoves.any fun (j, c) => j.countCheck c
-- each tree at its sequent written twice (counts of 2 and more)
#guard smallMoves.all fun (j, c) => agree (twice j) c
-- each tree at other sequents: 385 trees, each at 40 sequents; both
-- answers occur
#guard smallMoves.all fun (_, c) => ((seqsSmall.drop 500).take 40).all fun j => agree j c
#guard smallMoves.any fun (_, c) => ((seqsSmall.drop 500).take 40).any fun j => !j.countCheck c
#guard smallMoves.any fun (_, c) => ((seqsSmall.drop 500).take 40).any fun j => j.countCheck c
-- the trees of the proved search
#guard seqsSmall.all fun j => (prove? j).all fun c => agree j c && j.countCheck c
-- the corpus and members of the families, where the list replay is small
#guard (entries.map (·.seq) ++ [boxChain 3, boxChain 8, boxChain 12, kChain 4, kChain 8]).all fun j =>
  (movesOf j).all fun c => agree j c
-- where the list replay is not run: its sequents have 2³², 2⁶⁴ formulas
#guard (movesOf (boxChain 32)).any fun c => (boxChain 32).countCheck c
#guard (movesOf (boxChain 64)).any fun c => (boxChain 64).countCheck c
-- an altered tree is refused: a move that does not apply, a child too
-- many, a child too few
#guard !(([] ⇒ [p ⟶ p] : Seq)).countCheck (.mk (.impR p p) [.mk (.idP 1) []])
#guard (([] ⇒ [p ⟶ p] : Seq)).countCheck (.mk (.impR p p) [.mk (.idP 0) []])
#guard !(([] ⇒ [p ⟶ p] : Seq)).countCheck (.mk (.impR p p) [.mk (.idP 0) [], .mk (.idP 0) []])
#guard !(([] ⇒ [p ⟶ p] : Seq)).countCheck (.mk (.impR p p) [])
-- a formula used once more than it occurs: ImpL twice on one occurrence
#guard !(([p ⟶ ⊥, p] ⇒ [] : Seq)).countCheck
  (.mk (.impL p ⊥) [.mk (.impL p ⊥) [.mk (.idP 0) [], .mk .botL []], .mk .botL []])
#guard agree ([p ⟶ ⊥, p] ⇒ [])
  (.mk (.impL p ⊥) [.mk (.impL p ⊥) [.mk (.idP 0) [], .mk .botL []], .mk .botL []])
#guard (([p ⟶ ⊥, p ⟶ ⊥, p] ⇒ [] : Seq)).countCheck
  (.mk (.impL p ⊥) [.mk (.impL p ⊥) [.mk (.idP 0) [], .mk .botL []], .mk .botL []])

end GLS.CheckTest
