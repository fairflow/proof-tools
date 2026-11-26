/-
# `Play/MALLTutorial.lean`: the linear sequent calculus (MALL), a tour

A file to read in the editor, with the infoview open, a line at a time.
Unlike `Play/MALL.lean` (the exercises) it explains each step and shows
the answers.  It is in no library: build the instance first (`lake build`,
in `calculi/MALL/`).  Every line is elaborated, and what each step is said
to show is pinned in `MALL/ExploreTest.lean`.

MALL is the propositional linear logic of ⊗, ⅋, 1, ⊥ (the multiplicatives)
and &, ⊕, ⊤, 0 (the additives), in Girard's one-sided sequent calculus
(*Linear logic*, 1987, Definition 1.15; `campaign/rule-table.md` has each
rule beside its source).  A sequent `⊢ A₁, …, Aₙ` is a list of formulas
read as a multiset: the order never matters, and every formula is used
exactly once.  Negation is a function: `(p ⊗ q)ᗮ` is `pᗮ ⅋ qᗮ`.

    ax A            ⊢ A, A⊥ and nothing else              no premise
    cut A [Γ]       ⊢ Γ, Δ                                ⊢ A, Γ   and   ⊢ A⊥, Δ
    top             ⊢ ⊤, Γ                                no premise
    wth A B         ⊢ A & B, Γ                            ⊢ A, Γ   and   ⊢ B, Γ
    plus₁ A B       ⊢ A ⊕ B, Γ                            ⊢ A, Γ
    plus₂ A B       ⊢ A ⊕ B, Γ                            ⊢ B, Γ
    one             ⊢ 1 and nothing else                  no premise
    bot             ⊢ ⊥, Γ                                ⊢ Γ
    tensor A B [Γ]  ⊢ A ⊗ B, Γ, Δ                         ⊢ A, Γ   and   ⊢ B, Δ
    par A B         ⊢ A ⅋ B, Γ                            ⊢ A, B, Γ
-/
import MALL.Explore

open ProofTools ProofTools.Explore MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## 1. Building a derivation

A goal is a sequent still to be derived.  `mallmove m` makes the move `m`
at the first goal, and the premises of the rule are the new goals.  When
none is left the derivation is done.  Here, half of "⊗ distributes over
⊕" (Girard, 1.13(i)): `p ⊗ (q ⊕ r) ⊸ (p ⊗ q) ⊕ (p ⊗ r)`, as the sequent
of the negation of the left side and the right side. -/

def distrib : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  -- the first formula is  p⊥ ⅋ (q⊥ & r⊥).  ⅋: the goal becomes
  --   ⊢ p⊥, q⊥ & r⊥, (p ⊗ q) ⊕ (p ⊗ r)
  mallmove par pᗮ (qᗮ & rᗮ)
  -- &: two goals, with the same context,
  --   ⊢ q⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   and   ⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)
  mallmove wth qᗮ rᗮ
  -- in the first, the left side of ⊕ is the one to take:  ⊢ p ⊗ q, q⊥, p⊥
  mallmove plus₁ (p ⊗ q) (p ⊗ r)
  -- ⊗ splits the context: p⊥ goes with p, and what is left, q⊥, with q
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  -- the second goal of &, in the same way with the right side of ⊕
  mallmove plus₂ (p ⊗ q) (p ⊗ r)
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

/-! ## 2. Asking what applies

`mallmove` alone makes no move: it lists the moves that apply at goal 0.
Click one in the infoview to write it.  For ⊗ it lists every way to split
the context.  `mallmove where` draws the attempt so far, with goal 0
marked `>`. -/

example : Att S true [(p ⊗ q)ᗮ, q ⊗ p] := by
  -- three moves apply: ⅋ on the first formula, and two splits of ⊗ on the
  -- second, neither of which leads anywhere yet
  mallmove
  mallmove par pᗮ qᗮ
  -- now ⊗ has four splits of the context  p⊥, q⊥
  mallmove
  mallmove tensor q p [qᗮ]
  -- the attempt, drawn; two goals are open:  ⊢ q, q⊥   and   ⊢ p, p⊥
  mallmove where
  -- leave them open, without an error
  all_goals leave_open

/-! ## 3. Patterns

A move's arguments may be left out.  `mallmove par` is made if one ⅋
applies.  `_` stands for any argument.  `mallmove ax` finds the formula.
`mallmove tensor` alone would offer every split: give the context. -/

def tensorComm : Der S [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove par
  mallmove tensor _ _ [qᗮ]
  mallmove ax
  mallmove ax

/-! ## 4. A script

A derivation built by `mallmove` is data.  Its script is the list of its
lines: the goal each acted at, and the move.  `apply_script` runs a
script; what it leaves can be continued by hand. -/

-- 10 lines
#eval distrib.script.length
-- true: the script runs to the end
#eval derives S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] distrib.script

example : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  -- the first two lines: to the two goals of &
  apply_script distrib.script.take 2
  mallmove plus₁ (p ⊗ q) (p ⊗ r)
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove plus₂ (p ⊗ q) (p ⊗ r)
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

/-! ## 5. Tactics of the calculus

A tactic of the calculus is a program that gives a script for a sequent.

* `routine n` does the steps that lose nothing (the axioms, ⅋, ⊥, &)
  wherever they apply.  What it leaves has only ⊗ and ⊕ to try: the two
  rules that ask for a choice.
* `found` is the search by lazy splitting (`MALL/Lazy.lean`): the script
  of a derivation, where there is one.

`apply_script` takes the script as a closed term, so the sequent is
written out again for the tactic. -/

example : Att S true [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  apply_script (routine 20 [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]).getD []
  -- two goals are left, the two premises of &, each a choice of ⊕
  mallmove where
  all_goals leave_open

-- The whole derivation, from the search.
def distribByTheSearch : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  apply_script (found [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]).getD []

-- 10 lines, and they are the lines of section 1: the search finds that derivation
#eval distribByTheSearch.script.length
#eval distribByTheSearch.script == distrib.script

/-! ## 6. A walk

`#walk d` draws a derivation at its root and offers the motions from
there; `#walk d down 0 down 0` goes on from it.  In a block whose goal is
`Walk d`, each line is a motion (`down i`, `up`, `left`, `right`, `top`)
and the infoview shows the view there. -/

#walk distrib
#walk distrib down 0 down 1

example : Walk distrib := by
  -- the premise of ⅋, where the rule is &
  down 0
  -- the second premise of &, where the rule is 2⊕
  down 1
  -- its premise, where the rule is ⊗ with the split [p⊥]
  down 0
  up

/-! ## 7. Sequents with no derivation: no weakening, no contraction

`⊢ 1` is derivable and `⊢ 1, 1` is not: the rule 1 asks for the sequent
`⊢ 1` and nothing else. -/

example : Att S true [𝟏, 𝟏] := by
  -- no move applies here: a query would be the error
  --   mallmove: no move applies at goal 0
  -- and `mallmove one` the error
  --   the move does not apply to goal 0: 1: the sequent is not ⊢ 1
  leave_open

-- "A ⊸ A ⊗ A is not derivable, but A ⊸ A & A is" (Girard, p. 5): after ⅋
-- the one p⊥ can go to one side of ⊗ only.
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove par pᗮ (p ⊗ p)
  mallmove tensor p p [pᗮ]
  mallmove ax p
  -- what is left is  ⊢ p : no move applies
  leave_open

-- What the searches say, with a small phase structure that refutes the
-- sequent, where the enumeration has one.
#eval IO.println (explain [𝟏, 𝟏])
#eval IO.println (explain [pᗮ ⅋ (p ⊗ p)])
#eval IO.println (explain [p ⊕ pᗮ])
-- and of a sequent that has a derivation
#eval IO.println (explain [pᗮ ⅋ (p & p)])

-- As theorems, checked by the kernel, which runs the proved search.
example : ¬ Derivable [𝟏, 𝟏] := by decide +kernel
example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := by decide +kernel
example : Derivable [pᗮ ⅋ (p & p)] := by decide +kernel
-- the same through phase semantics: valid in every phase structure, or not
example : ¬ Valid [𝟏, 𝟏] := by decide +kernel

/-! ## 8. Out to the mathematics

What `mallmove` builds is a derivation of the proof system `S`.
`famOfDer` carries it to a derivation in the calculus as the source states
it, the family `Fam`; the theorems of the campaign are about that
family. -/

-- A derivation of the calculus, as data.
def distribFam : Fam [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := famOfDer distrib

-- its height: 5
#eval distribFam.height

-- So the sequent is valid in every phase structure (soundness, 1.16) …
example : Valid [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := soundness _ ⟨distribFam⟩

-- … and a valid sequent has a derivation without cut (completeness, 1.17).
example : Nonempty (CF [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]) :=
  completeness _ (soundness _ ⟨distribFam⟩)

-- Cut.  From  ⊢ p ⊗ q, p⊥, q⊥  and  ⊢ (p ⊗ q)⊥, q ⊗ p  a derivation of
-- ⊢ p⊥, q⊥, q ⊗ p,  with the cut rule as its last rule.
def withCut : Der S [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  apply_script tensorComm.script

-- Cut elimination is a function on derivations: it pushes the cut up to
-- where p ⊗ q is introduced on both sides, and cuts on p and on q there.
def withoutCut : CF [pᗮ, qᗮ, q ⊗ p] := cutElimination _ (famOfDer withCut)

-- heights: 4 with the cut, 2 without
#eval (famOfDer withCut).height
#eval withoutCut.height

-- The disjunction property: a derivation of ⊢ A ⊕ B gives one of ⊢ A or of ⊢ B.
example : Derivable [𝟏 ⊕ p] → Derivable [𝟏] ∨ Derivable [p] := disjunctionProperty 𝟏 p

-- The finite model property: a sequent that is not derivable is refuted by
-- a finite phase structure.
example : ∃ M : PhaseStructure, M.Finite ∧ ¬ M.Sat [𝟏, 𝟏] :=
  finite_countermodel _ (by decide +kernel)
