/-
Screens and guards of the two checks that the program and the kernel
run: truth at the root of a tree by the marks (`GLS/Table.lean`), and the
replay of a tree of moves by counts (`GLS/Counts.lean`), each beside the
definition it is proved equal to.

Code, not theory: nothing here is trusted, and the file has no bound on
axioms.  A screen that fails is a `#guard` that fails the build.  The
statements are S25 to S30 of `campaign/statements.md`.
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

/-- The tree of worlds of the search, where the sequent has none of
moves. -/
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

/-- The tree of moves of the search, where there is one. -/
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

/-! ## S30: truth by the marks, with a table over the different subformulas

The screens of the statement, run before its proof. -/

-- on 1 024 sequents and 200 worlds; both answers occur
#guard seqsSmall.all fun j => ((worlds trees2).take 200).all fun w => j.refutedM w == j.refutedAt w
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => j.refutedM w
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => !j.refutedM w

/-- Sequents whose formulas share subformulas, and repeat on both sides. -/
def shared : List Seq :=
  (forms2.flatMap fun A => forms2.map fun B => [A ⟶ B, A, □(A ⟶ B)] ⇒ [B, □A ⟶ □B, A ⟶ B]) ++
  (forms2.map fun A => [(A ⟶ A) ⟶ (A ⟶ A), □(A ⟶ A)] ⇒ [□□(A ⟶ A) ⟶ A, A])

#guard shared.length == 380
#guard shared.all fun j => ((worlds trees2).take 100).all fun w => j.refutedM w == j.refutedAt w
#guard shared.any fun j => ((worlds trees2).take 100).any fun w => j.refutedM w
-- a formula with a subformula twice at each level: on the tree that
-- refutes it, and at every world of that tree
#guard [1, 2, 3, 4, 5].all fun n => (treeOf (binTree n)).all fun t =>
  (binTree n).refutedM t && (binTree n).refutedAt t &&
  (t :: t.desc).all fun u => (binTree n).refutedM u == (binTree n).refutedAt u
-- a tree too short is refused
#guard [3, 8, 12].all fun n => (treeOf (consis n)).all fun t =>
  (consis n).refutedM t && !(consis (n + 1)).refutedM t
-- where the marks without a table take seconds: 8 191 worlds
#guard (treeOf (binTree 12)).all fun t => (binTree 12).refutedM t

/-! ## S28: the search at sequents without repeated formulas

`certOrRef` is proved; these were the screens of its statement and of the
lemma under it, run with the search that was not proved before the proof
was written, and they are kept as guards. -/

-- on the 1 024 small sequents one side answers, and its certificate
-- passes the certifier's check
#guard seqsSmall.all fun j => match certOrRef j with
  | .inl c => j.countCheck c.1
  | .inr r => j.refutedT r.1

/-- Sequents that have the formulas of a sequent, and more. -/
def more (j : Seq) : List Seq :=
  [twice j, j.ant ++ [□p, q] ⇒ j.suc, j.ant ⇒ j.suc ++ [□□p, p ⟶ q],
    [p ⟶ q] ++ j.ant ++ j.ant ⇒ [□p] ++ j.suc ++ j.suc]

-- a tree found for a sequent replays at every sequent with its formulas
#guard smallMoves.all fun (j, c) => (more j).all fun j' => j'.countCheck c
-- a sequent with repeats at the root: the tree of the sequent less its
-- repeats replays at it, and a tree of worlds refutes it
#guard (seqsSmall.take 300).all fun j => match certOrRef j.dedup with
  | .inl c => (twice j).countCheck c.1 && j.countCheck c.1
  | .inr r => (twice j).refutedT r.1
-- a control: a tree does not replay at a sequent that lacks a formula
#guard smallMoves.any fun (j, c) => !(([] ⇒ j.suc : Seq)).countCheck c
-- where the search over multisets is cut off: 64 nested boxes
#guard (certOrRef (boxChain 64)).isLeft && (certOrRef (lastChain 64)).isLeft
#guard (certOrRef (consis 64)).isRight

/-! ## S29: a script with its goals by counts -/

/-- The two replays of a script agree. -/
def agreeS (j : Seq) (ls : Script S) : Bool := j.scriptCheck ls == derives S j ls

-- the script of each tree at its own sequent: both accept
#guard smallMoves.all fun (j, c) => agreeS j (certScript c) && j.scriptCheck (certScript c)
-- at its sequent written twice, and at 40 other sequents; both answers occur
#guard smallMoves.all fun (j, c) => agreeS (twice j) (certScript c)
#guard smallMoves.all fun (_, c) => ((seqsSmall.drop 500).take 40).all fun j => agreeS j (certScript c)
#guard smallMoves.any fun (_, c) => ((seqsSmall.drop 500).take 40).any fun j => !j.scriptCheck (certScript c)
-- a script cut short leaves a goal, a line too many has no goal, a goal
-- that is not there: refused by both
#guard smallMoves.all fun (j, c) =>
  let ls := certScript c
  agreeS j ls.dropLast && !j.scriptCheck ls.dropLast &&
  agreeS j (ls ++ ls.take 1) && !j.scriptCheck (ls ++ ls.take 1) &&
  agreeS j (ls.map fun l => { l with goal := l.goal + 1 }) &&
  !j.scriptCheck (ls.map fun l => { l with goal := l.goal + 1 })
-- lines in another order: the second premise of ImpL first (goal 1)
#guard agreeS ([p ⟶ ⊥, p] ⇒ []) [⟨0, .impL p ⊥⟩, ⟨1, .botL⟩, ⟨0, .idP 0⟩] &&
  (([p ⟶ ⊥, p] ⇒ [] : Seq)).scriptCheck [⟨0, .impL p ⊥⟩, ⟨1, .botL⟩, ⟨0, .idP 0⟩]
#guard agreeS ([p ⟶ ⊥, p] ⇒ []) [⟨0, .impL p ⊥⟩, ⟨1, .idP 0⟩, ⟨0, .botL⟩] &&
  !(([p ⟶ ⊥, p] ⇒ [] : Seq)).scriptCheck [⟨0, .impL p ⊥⟩, ⟨1, .idP 0⟩, ⟨0, .botL⟩]
-- the script of a tree is the script of the derivation the tree is
#guard smallMoves.all fun (j, c) =>
  if h : Cert.check j c = true then
    toString (repr (certScript c)) == toString (repr (Der.ofCert j c h).script)
  else false
-- where the library's replay is not run: 64 nested boxes
#guard (movesOf (boxChain 64)).any fun c => (boxChain 64).scriptCheck (certScript c)
#guard (movesOf (lastChain 64)).any fun c => (lastChain 64).scriptCheck (certScript c)

end GLS.CheckTest
