/-
# `Play/DILLExercises.lean`: the graded exercises of `tutorial.md`

A file to type in.  The tutorial (`tutorial.md`, beside `Play/`) states
each exercise, says what it is for, and has the solutions at its end;
every solution is checked by the build, in `DILL/TutorialTest.lean`.  This
file is in no library: build the instance first (`lake build`, in
`calculi/DILL/`), then open it in the editor with the infoview.

A goal is shown as `Att S   Γ ; Δ ⟹ C`: the valid hypotheses `Γ`, each
usable any number of times; the linear hypotheses `Δ`, each used exactly
once; the conclusion `C`.  `·` is an empty zone.

Parts A and B are derivations and attempts, a move at a time:

    dillmove                     the moves that apply at goal 0; none is made
    dillmove bangL               made if one !L applies, else each is offered
    dillmove tensorR p q [p]     the move, in full: `[p]` goes to the first premise
    dillmove where               the attempt so far, drawn
    all_goals leave_open         at the end: leaves what is not proved open

When a derivation is done, delete `all_goals leave_open` and change
`Att S true` to `Der S`.

A sequent is typed `Γ ⨾ Δ ⟹ C` with a list for each zone:
`([] ⨾ [p, p ⊸ q] ⟹ q)`.  The sign `⨾` is not Lean's `;`: copy it from a
line below.  A formula: letters `p q r`, the constants `𝟏 ⊤ 𝟎`, and
`A ⊗ B`, `A ⊸ B`, `A & B`, `A ⊕ B`, `!A`.  Two traps:

* `!` is Lean's Boolean negation and takes all that follows: write
  `(!p) ⊗ q`, `(!p) ⊸ q`, `(!A) :: Δ`.  `[!p, q]` and `⟹ !p` are read
  rightly.
* `⊕` is Lean's sum of types: write `(p ⊕ q) ⊸ r`, `(A ⊕ B) :: Δ`.

Put a compound formula that is a move's argument in parentheses.

Parts C and D are Lean: each `sorry` is an exercise.  They are the only
`sorry`s of the instance, and nothing imports this file.

Grades: ★ a move or two; ★★ a short derivation, or a small countermodel;
★★★ wants an idea; ★★★★ a proof or a program in Lean.
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

/-! ## Part A: derivations -/

-- A1 ★  The four rules with no premise.
example : Att S true ([] ⨾ [p] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [] ⟹ 𝟏) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [p, q] ⟹ ⊤) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [𝟎, p] ⟹ q) := by
  dillmove
  all_goals leave_open

-- A2 ★  CCP p. 16 and p. 17.  Two divisions are offered in the first.
example : Att S true ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [p & q] ⟹ p) := by
  dillmove
  all_goals leave_open

-- A3 ★  A valid hypothesis, used once and used twice.
example : Att S true ([p] ⨾ [] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([p] ⨾ [] ⟹ p ⊗ p) := by
  dillmove
  all_goals leave_open

-- A4 ★★  Three laws of `!`.
example : Att S true ([] ⨾ [!p] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ 𝟏) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove
  all_goals leave_open

-- A5 ★★  `!(p & q)` and `!p ⊗ !q`, each from the other.
example : Att S true ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) := by
  dillmove
  all_goals leave_open

-- A6 ★★  Currying, both ways.  After ⊸R twice, which division of ⊸L?
example : Att S true ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ (q ⊸ r)) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) := by
  dillmove
  all_goals leave_open

-- A7 ★★★  Three moves apply at the root.  What if the first is &L₁?
example : Att S true ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r)) := by
  dillmove
  all_goals leave_open

-- A8 ★★  With a cut on p ⊗ q as the last rule (a query offers no cut:
-- type `dillmove cut (p ⊗ q) [p, q]`); then without cut.
example : Att S true ([] ⨾ [p, q] ⟹ q ⊗ p) := by
  dillmove
  all_goals leave_open

-- With a cut! on p ⊸ p as the last rule: `dillmove cutU (p ⊸ p)`.
example : Att S true ([] ⨾ [] ⟹ (p ⊸ p) ⊗ (p ⊸ p)) := by
  dillmove
  all_goals leave_open

-- A9 ★★★  The S combinator, with `!A ⊸ B` for the type of functions.
example : Att S true ([] ⨾ [!((!p) ⊸ ((!q) ⊸ r)), !((!p) ⊸ q), !p] ⟹ r) := by
  dillmove
  all_goals leave_open

/-! ## Part B: resources -/

-- B1 ★  No move applies here, so a query is an error and none is written:
-- type `dillmove`, then `dillmove oneR`, and read the two messages.
example : Att S true ([] ⨾ [p] ⟹ 𝟏) := by
  leave_open

example : Att S true ([p] ⨾ [] ⟹ 𝟏) := by
  dillmove
  all_goals leave_open

-- B2 ★★  How many divisions, and what does each leave?
example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ p ⊗ p) := by
  dillmove
  all_goals leave_open

-- B3 ★★  No move applies at the first: type `dillmove`, then
-- `dillmove bangR p`, and read the two messages.
example : Att S true ([] ⨾ [p] ⟹ !p) := by
  leave_open

-- In two ways.
example : Att S true ([] ⨾ [!p] ⟹ !p) := by
  dillmove
  all_goals leave_open

-- Which move is offered after !L, and after that?
example : Att S true ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) := by
  dillmove
  all_goals leave_open

-- B4 ★★  Not derivable (Pfenning's notes, p. 60).  Follow each of the three moves.
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove
  all_goals leave_open

-- With & for ⊗ it is derivable.
example : Att S true ([] ⨾ [p ⊸ (q & r)] ⟹ (p ⊸ q) & (p ⊸ r)) := by
  dillmove
  all_goals leave_open

-- B5 ★★★  One move is offered, and after it one move, and so on.  Why is
-- that no proof that the sequent has no derivation?  Give one (C7 helps).
example : Att S true ([p] ⨾ [] ⟹ q) := by
  dillmove
  all_goals leave_open

/-! ## Part C: the theorems, used -/

-- C1 ★★  One init, of height 1.  Predict the height of its expansion, then
-- evaluate:  #eval (identityExpansion _ c1).1.height
def c1 : CF ([] ⨾ [(!p) ⊗ 𝟏] ⟹ (!p) ⊗ 𝟏) := .init _ (.refl _)

#eval c1.height

-- C2 ★★  Build your two derivations of A8 that end with a cut as
-- `def withCut : Der S …` and `def withCutU : Der S …`; then
--   #eval (cutElimination _ (famOfDer withCut)).height
-- Before you evaluate: which derivations will come back?

-- C3 ★★★★  Modus ponens for ⊸, a derived rule.
def mp {Γ : List Form} {A B : Form} (d₁ : CF (Γ ⨾ [] ⟹ A ⊸ B)) (d₂ : CF (Γ ⨾ [] ⟹ A)) :
    CF (Γ ⨾ [] ⟹ B) :=
  sorry

-- C4 ★★★  `!` is a functor, with no cut.
def bangFunctor {Γ : List Form} {A B : Form} (d : CF (Γ ⨾ [A] ⟹ B)) : CF (Γ ⨾ [!A] ⟹ !B) :=
  sorry

-- C5 ★★★  The disjunction property with a linear hypothesis: refute it.
-- (`open DILL.Dec in` before the theorem lets `decide` settle a sequent
-- without `!` and with an empty unrestricted zone, in the form
-- `Nonempty (CF …)`; `Sem.derivable_iff_cf` goes between that and `Derivable`.)
theorem no_disjunction_in_context :
    ¬ ∀ (A B : Form) (Δ : List Form), Derivable ([] ⨾ Δ ⟹ A ⊕ B) →
      Derivable ([] ⨾ Δ ⟹ A) ∨ Derivable ([] ⨾ Δ ⟹ B) :=
  sorry

-- C6 ★★  From `illEquivalence` alone.
theorem c6 : Derivable ([p] ⨾ [] ⟹ p ⊗ p) ↔ Derivable ([] ⨾ [!p] ⟹ p ⊗ p) :=
  sorry

-- C7 ★★★  The counting model: the natural numbers under addition, every
-- set closed, the letter numbered `a` given the one phase `w a`.  By
-- hand first (the tutorial, 7.1); then, if you like, in Lean.
def countModel (w : Nat → Nat) : PhaseModel where
  M := Nat
  mul := (· + ·)
  one := 0
  one_mul := Nat.zero_add
  mul_comm := Nat.add_comm
  mul_assoc := Nat.add_assoc
  Cl := fun X => X
  cl_ext := fun _ _ h => h
  cl_idem := fun _ _ h => h
  cl_mono := fun _ _ h p hp => h p hp
  cl_mul := fun _ _ _ h => h
  val := fun a n => n = w a
  val_closed := fun _ _ h => h

theorem c7 : ¬ (countModel fun _ => 1).Sat ([] ⨾ [p] ⟹ 𝟏) :=
  sorry

-- C8 ★★★  Validity is closed under the linear cut.
theorem valid_cut (Γ Δ Δ' : List Form) (A C : Form) (h₁ : Valid (Γ ⨾ Δ ⟹ A))
    (h₂ : Valid (Γ ⨾ A :: Δ' ⟹ C)) : Valid (Γ ⨾ Δ ++ Δ' ⟹ C) :=
  sorry

/-! ## Part D: what runs -/

-- D1 ★  By `decide`: a sequent of Part A with a derivation without cut, a
-- sequent of Part B with none.
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p, p ⊸ q] ⟹ q)) :=
  sorry

open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) :=
  sorry

-- D2 ★★  The tree of moves of your derivation of B2, checked by the
-- kernel.  A tree is `.mk move [subtrees]`; here is the tree of
-- `· ; p, p ⊸ q ⟹ q`.
example : Fam true ([] ⨾ [p, p ⊸ q] ⟹ q) :=
  treeCert.verdict _ (.mk (.lolliL p q [p]) [.mk .init [], .mk .init []])

def d2 : Fam true ([] ⨾ [!p] ⟹ p ⊗ p) :=
  sorry

-- D3 ★★  The search with a budget on copy: change the budget, and the sequent.
#eval (Run.proveLazy ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 0).isSome

-- D4 ★★  A saturated set, by hand: replace `sorry` by
-- `noDerivableBySet.verdict _ [ … ]` with your set of sequents.
theorem d4a : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) :=
  sorry

theorem d4b : ¬ Derivable ([] ⨾ [] ⟹ !p) :=
  sorry

-- D5 ★★★  What does the producer answer, and why?
#eval (refuteSet ([p] ⨾ [] ⟹ q)).isSome
#eval (refuteSet ([] ⨾ [!p, q] ⟹ !(p ⊗ q))).isSome
