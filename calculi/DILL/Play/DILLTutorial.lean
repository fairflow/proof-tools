/-
# `Play/DILLTutorial.lean`: dual intuitionistic linear logic, a tour

A file to read in the editor, with the infoview open, a line at a time.
Unlike `Play/DILLExercises.lean` it explains each step and shows the
answers.  It is in no library: build the instance first (`lake build`, in
`calculi/DILL/`).  Every line is elaborated, and what each step is said to
show is pinned in `DILL/TutorialTest.lean`.

DILL is intuitionistic linear logic with ⊗, 1, ⊸, &, ⊤, ⊕, 0 and `!`, in
the two-zone sequent calculus of Chang, Chaudhuri and Pfenning
(CMU-CS-03-131R, Figure 2; `campaign/rule-table.md` has each rule beside
its source).  A sequent `Γ ; Δ ⟹ C` has valid hypotheses `Γ`, each usable
any number of times, linear hypotheses `Δ`, each used exactly once, and
one conclusion.  It is typed `Γ ⨾ Δ ⟹ C`, with a list for each zone.

    init            Γ ; A ⟹ A, the linear zone exactly A   no premise
    copy A          Γ ; Δ ⟹ C, with A in Γ                 Γ ; A, Δ ⟹ C
    tensorL A B     Γ ; Δ, A ⊗ B ⟹ C                       Γ ; A, B, Δ ⟹ C
    tensorR A B [Δ] Γ ; Δ, Δ′ ⟹ A ⊗ B                      Γ ; Δ ⟹ A   and   Γ ; Δ′ ⟹ B
    oneL            Γ ; Δ, 1 ⟹ C                           Γ ; Δ ⟹ C
    oneR            Γ ; · ⟹ 1, the linear zone empty       no premise
    lolliL A B [Δ]  Γ ; Δ, Δ′, A ⊸ B ⟹ C                   Γ ; Δ ⟹ A   and   Γ ; B, Δ′ ⟹ C
    lolliR A B      Γ ; Δ ⟹ A ⊸ B                          Γ ; A, Δ ⟹ B
    withL₁ A B      Γ ; Δ, A & B ⟹ C                       Γ ; A, Δ ⟹ C
    withL₂ A B      Γ ; Δ, A & B ⟹ C                       Γ ; B, Δ ⟹ C
    withR A B       Γ ; Δ ⟹ A & B                          Γ ; Δ ⟹ A   and   Γ ; Δ ⟹ B
    topR            Γ ; Δ ⟹ ⊤                              no premise
    zeroL           Γ ; Δ, 0 ⟹ C                           no premise
    plusL A B       Γ ; Δ, A ⊕ B ⟹ C                       Γ ; A, Δ ⟹ C   and   Γ ; B, Δ ⟹ C
    plusR₁ A B      Γ ; Δ ⟹ A ⊕ B                          Γ ; Δ ⟹ A
    plusR₂ A B      Γ ; Δ ⟹ A ⊕ B                          Γ ; Δ ⟹ B
    bangL A         Γ ; Δ, !A ⟹ C                          Γ, A ; Δ ⟹ C
    bangR A         Γ ; · ⟹ !A, the linear zone empty      Γ ; · ⟹ A
    cut A [Δ]       Γ ; Δ, Δ′ ⟹ C                          Γ ; Δ ⟹ A   and   Γ ; A, Δ′ ⟹ C
    cutU A          Γ ; Δ ⟹ C                              Γ ; · ⟹ A   and   Γ, A ; Δ ⟹ C

Two traps when typing a formula: write `(!p) ⊗ q` and `(p ⊕ q) ⊸ r`, with
the parentheses.  Lean has its own `!` and its own `⊕`.
-/
import DILL.Goals
import DILL.Invert
import DILL.Translate
import DILL.Tactic
import DILL.Engine

open ProofTools ProofTools.Explore DILL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## 1. Building a derivation

A goal is a sequent still to be derived.  `dillmove m` makes the move `m`
at the first goal, and the premises of the rule are the new goals.  When
none is left the derivation is done.  Here: a formula under `!` can be
had twice, `· ; !p ⟹ !p ⊗ !p`. -/

def bangContract : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  -- !L moves p into the unrestricted zone: the goal becomes
  --   p ; · ⟹ !p ⊗ !p
  dillmove bangL p
  -- ⊗R divides the linear zone.  It is empty: nothing goes to the first
  -- premise, nothing is left for the second.  Two goals, both
  --   p ; · ⟹ !p
  dillmove tensorR (!p) (!p) []
  -- the linear zone is empty, so !R applies:  p ; · ⟹ p
  dillmove bangR p
  -- copy brings a p into the linear zone and keeps p valid:  p ; p ⟹ p
  dillmove copy p
  dillmove init
  -- the second goal of ⊗R, in the same way
  dillmove bangR p
  dillmove copy p
  dillmove init

-- The derivation, drawn: eight lines, one for each rule.
#eval IO.println bangContract.render

/-! ## 2. Asking what applies

`dillmove` alone makes no move: it lists the moves that apply at goal 0,
the rules that lose nothing first, then the choices, then copy.  Click
one in the infoview to write it.  For ⊗R and ⊸L it lists every division
of the linear zone.  `dillmove where` draws the attempt so far, with goal
0 marked `>`. -/

example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  -- three moves apply: !L, which loses nothing, and the two divisions of
  -- ⊗R, either of which loses the derivation here
  dillmove
  dillmove bangL p
  -- now two: ⊗R with its one division, and copy
  dillmove
  dillmove tensorR (!p) (!p) []
  -- the attempt, drawn; two goals are open, both  p ; · ⟹ !p
  dillmove where
  -- leave them open, without an error
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  -- a query by the beginning of a name: the two moves that begin with `te`
  dillmove te
  all_goals leave_open

/-! ## 3. Patterns

A move's arguments may be left out.  `dillmove bangL` is made if one !L
applies, and the line is offered back in full.  `_` stands for any
argument.  `dillmove tensorR` alone would offer both divisions and make
neither: give the division. -/

def bangContractByPatterns : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove bangL
  dillmove tensorR _ _ []
  dillmove bangR
  dillmove copy
  dillmove init
  dillmove bangR
  dillmove copy
  dillmove init

/-! ## 4. A script

A derivation built by `dillmove` is data.  Its script is the list of its
lines: the goal each acted at, and the move.  `apply_script` runs a
script; what it leaves can be continued by hand. -/

-- 8 lines
#eval bangContract.script.length
-- true: the script runs to the end
#eval derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContract.script
-- false: without its last line it leaves a goal
#eval derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) (bangContract.script.take 7)

example : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  -- the first two lines: to the two goals of ⊗R
  apply_script bangContract.script.take 2
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove bangR p
  dillmove copy p
  dillmove init

/-! ## 5. A walk

`#walk d` draws a derivation at its root and offers the motions from
there; `#walk d down 0 down 1` goes on from it.  In a block whose goal is
`Walk d`, each line is a motion (`down i`, `up`, `left`, `right`, `top`)
and the infoview shows the view there. -/

#walk bangContract
#walk bangContract down 0 down 1

example : Walk bangContract := by
  -- the premise of !L, where the rule is ⊗R
  down 0
  -- the second premise of ⊗R, where the rule is !R
  down 1
  -- its premise, where the rule is copy
  down 0
  up

/-! ## 6. A tree of moves, checked by the kernel

A derivation is also a tree of moves: the rules, their formulas and their
divisions, and nothing else.  `Cert.check j c` runs the moves from the
sequent `j`; the kernel evaluates it, with no tactic.  This is the
certificate for a derivation (`treeCert`, in `DILL/Run.lean`). -/

def bangContractCert : Cert S :=
  .mk (.bangL p) [.mk (.tensorR (!p) (!p) [])
    [.mk (.bangR p) [.mk (.copy p) [.mk .init []]],
     .mk (.bangR p) [.mk (.copy p) [.mk .init []]]]]

-- it is the tree of the derivation of section 1
example : bangContract.cert = bangContractCert := rfl
-- the kernel checks it
example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractCert = true := by decide +kernel
-- and the verdict of the certifier is a derivation of the calculus
def bangContractByTree : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  treeCert.verdict _ bangContractCert

-- A tree that begins with ⊗R, before !L, does not check.
def wrongCert : Cert S := .mk (.tensorR (!p) (!p) [!p]) [.mk .init [], .mk (.bangR p) []]

example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) wrongCert = false := by decide +kernel

-- The search finds the tree, with a budget of one copy along a branch;
-- with none it finds nothing, which is not "no".
#eval (Run.proveLazy ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) 1).isSome
#eval (Run.proveLazy ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) 0).isSome

/-! ## 7. A sequent with no derivation

`· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)` (Pfenning's lecture notes, p. 60):
the one hypothesis can be used once, and the conclusion asks for it in
both factors. -/

example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  -- three moves apply: the two divisions of ⊗R, and ⊸L
  dillmove
  dillmove lolliL p (q ⊗ r) []
  -- two goals:  · ; · ⟹ p   and   · ; q ⊗ r ⟹ (p ⊸ q) ⊗ (p ⊸ r)
  dillmove where
  -- at the first no move applies: a query here would be the error
  --   dillmove: no move applies at goal 0
  -- and `dillmove init` the error
  --   the move does not apply to goal 0: init: the linear zone is not exactly the conclusion
  all_goals leave_open

-- As a theorem: the sequent has no `!` and an empty unrestricted zone, so
-- the kernel decides it, by running the search that is proved complete.
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))) := by decide

-- The same by a certificate: a saturated set of sequents, the record of a
-- failed search.  The producer returns one of 8 sequents.
#eval (refuteSet ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))).map (·.length)

-- A smaller one, written by hand and checked by the kernel:
-- `· ; p ⟹ p ⊗ p`, with `· ; · ⟹ p`, which both divisions of ⊗R ask for.
example : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) :=
  noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]

-- With a valid hypothesis there is no such set, and no decision: at
-- `p ; · ⟹ q` the one move offered is copy, again and again.
example : Att S true ([p] ⨾ [] ⟹ q) := by
  dillmove copy p
  dillmove copy p
  -- the goal is  p ; p, p ⟹ q , and copy is the one move offered still
  dillmove
  all_goals leave_open

/-! ## 8. Out to the mathematics

What `dillmove` builds is a derivation of the proof system `S`.
`famOfDer` carries it to a derivation in the calculus as the source
states it, the family `Fam true`; the theorems of the campaign are about
that family. -/

-- A derivation of the calculus, as data.
def bangContractFam : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := famOfDer bangContract

-- its height: 5
#eval bangContractFam.height

-- So the sequent is valid in every phase model (soundness) …
example : Valid ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := soundness _ ⟨bangContractFam⟩

-- … and a valid sequent has a derivation without cut (completeness).
example : Nonempty (CF ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))) :=
  completeness _ (soundness _ ⟨bangContractFam⟩)

-- In the one-zone calculus it is the sequent  !p ⊢ !p ⊗ !p .
example : ILLDerivable [!p] ((!p) ⊗ (!p)) := (illEquivalence [] [!p] _).1 ⟨bangContractFam⟩

-- Cut.  A lemma, p ⊸ p, derived once and used twice by the cut on a valid
-- hypothesis.
def withCutU : Der S ([] ⨾ [] ⟹ (p ⊸ p) ⊗ (p ⊸ p)) := by
  dillmove cutU (p ⊸ p)
  dillmove lolliR p p
  dillmove init
  dillmove tensorR (p ⊸ p) (p ⊸ p) []
  dillmove copy (p ⊸ p)
  dillmove init
  dillmove copy (p ⊸ p)
  dillmove init

-- Cut elimination is a function on derivations: at each copy of the lemma
-- it puts the lemma's derivation.
def withoutCut : CF ([] ⨾ [] ⟹ (p ⊸ p) ⊗ (p ⊸ p)) := cutElimination _ (famOfDer withCutU)

-- heights: 4 with the cut, 3 without
#eval (famOfDer withCutU).height
#eval withoutCut.height

-- The disjunction property: a derivation of · ; · ⟹ A ⊕ B gives one of
-- · ; · ⟹ A or one of · ; · ⟹ B.
example : Derivable ([] ⨾ [] ⟹ 𝟏 ⊕ p) → Derivable ([] ⨾ [] ⟹ 𝟏) ∨ Derivable ([] ⨾ [] ⟹ p) :=
  disjunctionProperty 𝟏 p
