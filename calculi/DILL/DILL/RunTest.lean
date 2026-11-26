/-
Tests of the Run stage, "yes" side: for entries of the corpus a
derivation by the tree of moves that the search returned, pasted from
`dillrun tree <entry>` (and `dillrun cert` for the member of a family);
that the search returns that tree, and what it answers at a budget too
small; and for each certifier of derivations negative tests, rejected in
the kernel (rule R9 of `lean-certify`: a gate never watched failing does
not count).
-/
import DILL.Run
import DILL.Corpus.Basic

namespace DILL.RunTest

open ProofTools ProofTools.Explore DILL DILL.Run DILL.Corpus

/-! ## For a derivation: trees of moves from the search -/

/-- `· ; p, p ⊸ q ⟹ q` (CCP p. 16): ⊸L names the division, `p` to the
first premise. -/
def modusPonens : Fam true ([] ⨾ [p, p ⊸ q] ⟹ q) :=
  treeCert.verdict _ (.mk (.lolliL p q [p]) [.mk .init [], .mk .init []])

#guard proveLazy ([] ⨾ [p, p ⊸ q] ⟹ q) 0 ==
  some (.mk (.lolliL p q [p]) [.mk .init [], .mk .init []])

/-- `· ; !p, !(p ⊸ q) ⟹ !q` (the plan's Q4): two copies along the branch
of the first premise of ⊸L, whose linear zone is empty. -/
def bangMap : Fam true ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) :=
  treeCert.verdict _ (.mk (.bangL p) [.mk (.bangL (p ⊸ q)) [.mk (.bangR q)
    [.mk (.copy (p ⊸ q)) [.mk (.lolliL p q []) [.mk (.copy p) [.mk .init []], .mk .init []]]]]])

#guard proveLazy ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 2 ==
  some (.mk (.bangL p) [.mk (.bangL (p ⊸ q)) [.mk (.bangR q)
    [.mk (.copy (p ⊸ q)) [.mk (.lolliL p q []) [.mk (.copy p) [.mk .init []], .mk .init []]]]]])

-- At a budget of one copy the search finds nothing: a flag, not a "no".
#guard proveLazy ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 1 == none
#guard (Lazy.proveWith {} ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 1).2.cuts == 1

/-- `· ; !(p & q) ⟹ !p ⊗ !q` (the plan's Q4): ⊗R divides an empty zone,
and each premise copies `p & q`. -/
def bangWithTensor : Fam true ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) :=
  treeCert.verdict _ (.mk (.bangL (p & q)) [.mk (.tensorR (!p) (!q) [])
    [.mk (.bangR p) [.mk (.copy (p & q)) [.mk (.withL₁ p q) [.mk .init []]]],
     .mk (.bangR q) [.mk (.copy (p & q)) [.mk (.withL₂ p q) [.mk .init []]]]]])

#guard proveLazy ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) 1 ==
  some (.mk (.bangL (p & q)) [.mk (.tensorR (!p) (!q) [])
    [.mk (.bangR p) [.mk (.copy (p & q)) [.mk (.withL₁ p q) [.mk .init []]]],
     .mk (.bangR q) [.mk (.copy (p & q)) [.mk (.withL₂ p q) [.mk .init []]]]]])

/-- `· ; p, q, r ⟹ p ⊗ ⊤`: the ⊤R of the second premise has `q, r`, which
it took back; the move names only `p` for the first. -/
def topSlack : Fam true ([] ⨾ [p, q, r] ⟹ p ⊗ ⊤) :=
  treeCert.verdict _ (.mk (.tensorR p ⊤ [p]) [.mk .init [], .mk .topR []])

#guard proveLazy ([] ⨾ [p, q, r] ⟹ p ⊗ ⊤) 0 ==
  some (.mk (.tensorR p ⊤ [p]) [.mk .init [], .mk .topR []])

/-- `· ; p, q ⊸ 0, q ⟹ r ⊗ s`: the 0L of the second premise of ⊸L takes
`p`. -/
def zeroSlack : Fam true ([] ⨾ [p, q ⊸ 𝟎, q] ⟹ r ⊗ s) :=
  treeCert.verdict _ (.mk (.lolliL q 𝟎 [q]) [.mk .init [], .mk .zeroL []])

#guard proveLazy ([] ⨾ [p, q ⊸ 𝟎, q] ⟹ r ⊗ s) 0 ==
  some (.mk (.lolliL q 𝟎 [q]) [.mk .init [], .mk .zeroL []])

/-- `· ; (p ⊗ q) ⊸ r ⟹ p ⊸ q ⊸ r`: ⊸L gives `q, p` to its first premise,
where ⊗R divides them. -/
def curry : Fam true ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ q ⊸ r) :=
  treeCert.verdict _ (.mk (.lolliR p (q ⊸ r)) [.mk (.lolliR q r) [.mk (.lolliL (p ⊗ q) r [q, p])
    [.mk (.tensorR p q [p]) [.mk .init [], .mk .init []], .mk .init []]]])

#guard proveLazy ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ q ⊸ r) 0 ==
  some (.mk (.lolliR p (q ⊸ r)) [.mk (.lolliR q r) [.mk (.lolliL (p ⊗ q) r [q, p])
    [.mk (.tensorR p q [p]) [.mk .init [], .mk .init []], .mk .init []]]])

/-- A member of a family: `p ⊸ q, q ⊸ r, r ⊸ s ; p ⟹ s`, with three
copies along a branch. -/
def chainU3 : Fam true (Corpus.chainU 3) :=
  treeCert.verdict _ (.mk (.copy (r ⊸ s)) [.mk (.lolliL r s [p]) [.mk (.copy (q ⊸ r))
    [.mk (.lolliL q r [p]) [.mk (.copy (p ⊸ q)) [.mk (.lolliL p q [p])
      [.mk .init [], .mk .init []]], .mk .init []]], .mk .init []]])

#guard proveLazy (Corpus.chainU 3) 3 ==
  some (.mk (.copy (r ⊸ s)) [.mk (.lolliL r s [p]) [.mk (.copy (q ⊸ r))
    [.mk (.lolliL q r [p]) [.mk (.copy (p ⊸ q)) [.mk (.lolliL p q [p])
      [.mk .init [], .mk .init []]], .mk .init []]], .mk .init []]])
#guard proveLazy (Corpus.chainU 3) 2 == none

/-- The same derivation by its script. -/
def chainU3' : Fam true (Corpus.chainU 3) :=
  scriptCert.verdict _ [⟨0, .copy (r ⊸ s)⟩, ⟨0, .lolliL r s [p]⟩, ⟨0, .copy (q ⊸ r)⟩,
    ⟨0, .lolliL q r [p]⟩, ⟨0, .copy (p ⊸ q)⟩, ⟨0, .lolliL p q [p]⟩, ⟨0, .init⟩, ⟨0, .init⟩,
    ⟨0, .init⟩, ⟨0, .init⟩]

-- The search with the left rules as the figure has them returns a tree
-- that checks too (here the same one).
#guard (proveLazyWith { focus := false } ([] ⨾ [p, p ⊸ q] ⟹ q) 0).1 ==
  some (.mk (.lolliL p q [p]) [.mk .init [], .mk .init []])

/-! ## Negative tests: trees and scripts that are refused, in the kernel -/

/-- A wrong division: ⊸L gives nothing to its first premise, which then
has no `p`.  Rejected. -/
theorem bad_division_rejected :
    treeCert.check ([] ⨾ [p, p ⊸ q] ⟹ q) (.mk (.lolliL p q []) [.mk .init [], .mk .init []])
      = false := by
  decide +kernel

/-- A division that names a formula the zone does not have twice (a
linear contraction).  Rejected. -/
theorem contraction_rejected :
    treeCert.check ([] ⨾ [p] ⟹ p ⊗ p) (.mk (.tensorR p p [p]) [.mk .init [], .mk .init []])
      = false := by
  decide +kernel

/-- init with a formula left over (a linear weakening).  Rejected. -/
theorem weakening_rejected :
    treeCert.check ([] ⨾ [p, q] ⟹ p) (.mk .init []) = false := by
  decide +kernel

/-- A copy of a formula that is not in the unrestricted zone.  Rejected. -/
theorem bad_copy_rejected :
    treeCert.check ([q] ⨾ [] ⟹ p) (.mk (.copy p) [.mk .init []]) = false := by
  decide +kernel

/-- !R where the linear zone is not empty.  Rejected. -/
theorem bad_bangR_rejected :
    treeCert.check ([] ⨾ [p] ⟹ !p) (.mk (.bangR p) [.mk .init []]) = false := by
  decide +kernel

/-- A wrong move: &L₂ where the derivation has &L₁.  Rejected. -/
theorem wrong_move_rejected :
    treeCert.check ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) (.mk (.bangL (p & q)) [.mk (.tensorR (!p) (!q) [])
      [.mk (.bangR p) [.mk (.copy (p & q)) [.mk (.withL₂ p q) [.mk .init []]]],
       .mk (.bangR q) [.mk (.copy (p & q)) [.mk (.withL₂ p q) [.mk .init []]]]]]) = false := by
  decide +kernel

/-- A tree that stops early: the second premise of ⊸L has no tree.
Rejected. -/
theorem short_tree_rejected :
    treeCert.check ([] ⨾ [p, p ⊸ q] ⟹ q) (.mk (.lolliL p q [p]) [.mk .init []]) = false := by
  decide +kernel

/-- A tree with one copy too few along a branch.  Rejected. -/
theorem missing_copy_rejected :
    treeCert.check (Corpus.chainU 3) (.mk (.copy (r ⊸ s)) [.mk (.lolliL r s [p])
      [.mk (.lolliL q r [p]) [.mk (.copy (p ⊸ q)) [.mk (.lolliL p q [p])
        [.mk .init [], .mk .init []]], .mk .init []], .mk .init []]]) = false := by
  decide +kernel

/-- A script with a wrong line (the division of the first ⊸L), and one
that stops early.  Rejected. -/
theorem bad_script_rejected :
    scriptCert.check (Corpus.chainU 3) [⟨0, .copy (r ⊸ s)⟩, ⟨0, .lolliL r s []⟩, ⟨0, .copy (q ⊸ r)⟩,
      ⟨0, .lolliL q r [p]⟩, ⟨0, .copy (p ⊸ q)⟩, ⟨0, .lolliL p q [p]⟩, ⟨0, .init⟩, ⟨0, .init⟩,
      ⟨0, .init⟩, ⟨0, .init⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check (Corpus.chainU 3) [⟨0, .copy (r ⊸ s)⟩, ⟨0, .lolliL r s [p]⟩, ⟨0, .copy (q ⊸ r)⟩,
      ⟨0, .lolliL q r [p]⟩, ⟨0, .copy (p ⊸ q)⟩, ⟨0, .lolliL p q [p]⟩, ⟨0, .init⟩, ⟨0, .init⟩,
      ⟨0, .init⟩] = false := by
  decide +kernel

/-! ## The axioms of the facts -/

#certify_axioms DILL.RunTest.modusPonens
#certify_axioms DILL.RunTest.bangMap
#certify_axioms DILL.RunTest.bangWithTensor
#certify_axioms DILL.RunTest.topSlack
#certify_axioms DILL.RunTest.zeroSlack
#certify_axioms DILL.RunTest.curry
#certify_axioms DILL.RunTest.chainU3
#certify_axioms DILL.RunTest.chainU3'

/-! ## The producer: `pass` or `flag`, never `fail` -/

#guard (produce ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 2 matches .pass _)
#guard (produce ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 1 matches .flag)
-- A sequent with no derivation, where a copy can always be made: `flag`
-- at every budget.
#guard (produce ([] ⨾ [!(p ⊸ p)] ⟹ p) 5 matches .flag)
-- A sequent with no derivation and no copy to make: `flag` too.  The
-- search is for the "yes" side only.
#guard (produce ([] ⨾ [p] ⟹ p ⊗ p) 5 matches .flag)
#guard (produceTree ([] ⨾ [p, q, r] ⟹ p ⊗ ⊤) 0 matches .pass _)

-- On the corpus: the search derives each entry whose status is
-- "derivable", at a budget of two copies, and none of the others.
#guard entries.all fun e => (proveLazy e.seq 2).isSome == e.derivable

end DILL.RunTest
