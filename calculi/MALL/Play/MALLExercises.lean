/-
# `Play/MALLExercises.lean`: the graded exercises of `tutorial.md`

A file to type in.  The tutorial (`tutorial.md`, beside `Play/`) states
each exercise, says what it is for, and has the solutions at its end;
every solution is checked by the build, in `MALL/TutorialTest.lean`.  This
file is in no library: build the instance first (`lake build`, in
`calculi/MALL/`), then open it in the editor with the infoview.

Parts A and B are derivations and attempts, a move at a time:

    mallmove               the moves that apply at goal 0; none is made
    mallmove par           made if one ⅋ applies, else each is offered
    mallmove tensor p q [pᗮ]   the move, in full: `[pᗮ]` goes with `p`
    mallmove where         the attempt so far, drawn
    all_goals leave_open   at the end: leaves what is not proved open

When a derivation is done, delete `all_goals leave_open` and change
`Att S true` to `Der S`.

A formula: letters `p q r`, their duals `pᗮ qᗮ rᗮ`, the constants
`𝟏 ⊥ ⊤ 𝟎`, and `A ⊗ B`, `A ⅋ B`, `A & B`, `A ⊕ B`.  `Aᗮ` is linear
negation, a function: `(p ⊗ q)ᗮ` is `pᗮ ⅋ qᗮ`.  `A ⊸ B` is typed
`Aᗮ ⅋ B`.  Put a compound formula inside another in parentheses, and
write `(A ⊕ B) :: Γ` with parentheses: before `::`, Lean reads `⊕` as a
sum of types.

Part C is countermodels, Parts D and E are Lean: each `sorry` is an
exercise.  They are the only `sorry`s of the instance, and nothing
imports this file.

Grades: ★ a move or two; ★★ a short derivation, or a small countermodel;
★★★ wants an idea; ★★★★ a proof or a program in Lean.
-/
import MALL.Explore
import MALL.ModelRun
import MALL.Refute
import MALL.Craig
import MALL.Uniform

open ProofTools ProofTools.Explore MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## Part A: derivations -/

-- A1 ★  The three rules with no premise.
example : Att S true [p, pᗮ] := by
  mallmove
  all_goals leave_open

example : Att S true [𝟏] := by
  mallmove
  all_goals leave_open

example : Att S true [⊤, p, q] := by
  mallmove
  all_goals leave_open

-- A2 ★  p ⊸ p;  ⊢ ⊥, 1;  0 ⊸ p.
example : Att S true [pᗮ ⅋ p] := by
  mallmove
  all_goals leave_open

example : Att S true [⊥, 𝟏] := by
  mallmove
  all_goals leave_open

example : Att S true [𝟎ᗮ ⅋ p] := by
  mallmove
  all_goals leave_open

-- A3 ★★  The axiom at p ⊗ q, from axioms at letters: do not use `ax (p ⊗ q)`.
example : Att S true [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove
  all_goals leave_open

-- Commutativity.  After ⅋, which of the four splits?
example : Att S true [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove
  all_goals leave_open

-- A4 ★  1 is the unit of ⊗.
example : Att S true [(𝟏 ⊗ p)ᗮ, p] := by
  mallmove
  all_goals leave_open

example : Att S true [pᗮ, 𝟏 ⊗ p] := by
  mallmove
  all_goals leave_open

-- A5 ★★  p ⊸ p & p,  and  p & q ⊸ p.
example : Att S true [pᗮ ⅋ (p & p)] := by
  mallmove
  all_goals leave_open

example : Att S true [(p & q)ᗮ ⅋ p] := by
  mallmove
  all_goals leave_open

-- A6 ★★★  ⅋ over &.  Three rules apply at the root: which goes first?
example : Att S true [((p ⅋ q) & (p ⅋ r))ᗮ, p ⅋ (q & r)] := by
  mallmove
  all_goals leave_open

-- A7 ★★  With a cut on p ⊗ q, and then without.
example : Att S true [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  all_goals leave_open

example : Att S true [pᗮ, qᗮ, q ⊗ p] := by
  mallmove
  all_goals leave_open

/-! ## Part B: resources -/

-- B1 ★  No move applies here, so a query is an error and the file has
-- none.  Type `mallmove` on a line before `all_goals`, read the message,
-- and then type `mallmove one` in its place.
example : Att S true [𝟏, 𝟏] := by
  all_goals leave_open

-- B2 ★★  p ⊸ p ⊗ p.  Go as far as the moves go.
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove
  all_goals leave_open

-- B3 ★★  No contraction.
example : Att S true [p ⊕ pᗮ, p ⊕ pᗮ] := by
  mallmove
  all_goals leave_open

example : Att S true [p ⊕ pᗮ] := by
  mallmove
  all_goals leave_open

-- B4 ★★★  Sixteen moves.  Which begin a derivation?
example : Att S true [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r] := by
  mallmove
  all_goals leave_open

/-! ## Part C: phase semantics, and the two certificates

A structure on ℤ/(k+1) is written `⟨k, bot, val⟩`: the antiphases as a
list of Booleans, one for each phase, and a list of such lists, one for
each letter in the order `p`, `q`, `r`.  The kernel checks it against a
sequent in `noDerivableBy.verdict _ z`.  To compute in a structure `z`:
`z.dualL G`, `z.interpL A`, `z.refutes Γ`.  To see the searches' answer:
`#eval IO.println (explain Γ)`, `#eval refuteBy Γ`.

A saturated set of sequents is a list of lists of formulas.  The kernel
checks it in `noDerivableBySet.verdict _ D`.  The producer is
`refuteSet Γ`, and `#eval IO.println (describeCountermodel Γ)` prints
the set and the structure it presents. -/

-- The worked example of the tutorial.
example : ¬ Derivable [𝟏, 𝟏] := noDerivableBy.verdict _ ⟨1, [false, true], []⟩

-- C1 ★★  ℤ/3 with the antiphases {0}: the dual of a set.
def z30 : ZModel := ⟨2, [true, false, false], []⟩
-- #eval z30.dualL [true, true, false]

-- C2 ★  ℤ/2 with the antiphases {0}.  (This one is wrong: the kernel says so.)
-- example : ¬ Derivable [𝟏, 𝟏] := noDerivableBy.verdict _ ⟨1, [true, false], []⟩

-- C3 ★★  Write the structure.
-- example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := noDerivableBy.verdict _ ⟨1, _, _⟩
-- example : ¬ Derivable [p ⊕ pᗮ] := noDerivableBy.verdict _ ⟨1, _, _⟩

-- C4 ★★★  Not in ℤ/2.
-- example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] := noDerivableBy.verdict _ _

-- The worked example of the second certificate.
example : ¬ Derivable [p ⊕ pᗮ] := noDerivableBySet.verdict _ [[pᗮ], [p ⊕ pᗮ], [p]]

-- C5 ★★  Write the sets.
-- example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := noDerivableBySet.verdict _ [[pᗮ ⅋ (p ⊗ p)]]
-- example : ¬ Derivable [p & q, pᗮ] := noDerivableBySet.verdict _ [[p & q, pᗮ]]

-- C6 ★★★  The sequent of C4, by a set; and what the producer returns.
-- example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] := noDerivableBySet.verdict _ _
-- #eval (refuteSet [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]).map (·.length)

/-! ## Part D: the theorems, used

The functions on derivations (`tutorial.md`, section 5):

    identityExpansion  (Γ : List Form) → CF Γ → { d : CF Γ // d.Atomic }
    cutAdmissible      (A : Form) → (Γ Δ : List Form) → CF (A :: Γ) → CF (Aᗮ :: Δ) → CF (Γ ++ Δ)
    cutElimination     (Γ : List Form) → Fam Γ → CF Γ
    parInversion       (A B : Form) → (Γ : List Form) → CF (A ⅋ B :: Γ) → CF (A :: B :: Γ)
    famOfDer           Der S Γ → Fam Γ
-/

-- D1 ★★  Predict the height before you evaluate.
def d1 : CF [(p ⊗ q) & 𝟏, ((p ⊗ q) & 𝟏)ᗮ] := .ax _ (.refl _)
-- #eval (identityExpansion _ d1).1.height

-- D2 ★★  Eliminate the cut of A7.  Name your derivation, then:
-- #eval (cutElimination _ (famOfDer a7)).height

-- D3 ★★★★  Modus ponens for ⊸ is a derived rule.
def mp {A B : Form} (d₁ : CF [Aᗮ ⅋ B]) (d₂ : CF [A]) : CF [B] :=
  sorry

-- D4 ★★★  Consistency, with no model and no search.
theorem consistent : Fam [] → False :=
  sorry

-- D5 ★★★  The disjunction property, and its failure in a context.
example : Derivable [𝟏 ⊕ p] → Derivable [𝟏] ∨ Derivable [p] := disjunctionProperty 𝟏 p

theorem no_disjunction_in_context :
    ¬ ∀ (A B : Form) (Γ : List Form),
      Derivable ((A ⊕ B) :: Γ) → Derivable (A :: Γ) ∨ Derivable (B :: Γ) :=
  sorry

-- D6 ★★  The interpolant of ⊢ (p & q)⊥, p ⊕ r, divided between its two formulas.
def d6 : CF [(p & q)ᗮ, p ⊕ r] := (searchCF _).get (by decide +kernel)
-- #eval (craigInterpolation [(p & q)ᗮ] [p ⊕ r] d6).C.show

-- D7 ★★  Predict, then evaluate.
-- #eval (existsP 0 (p ⊗ q)).show
-- #eval (existsP 0 (p & q)).show
-- #eval (forallP 0 (p ⅋ pᗮ)).show

-- D8 ★★★  From `ui_spec`, without computing the interpolant.
example : Derivable [forallP 0 ((p ⊗ q) ⅋ pᗮ), qᗮ] :=
  sorry

/-! ## Part E: the semantics, in Lean -/

-- E1 ★  The kernel runs the search.
-- example : Valid [pᗮ ⅋ (p & p)] := by decide +kernel

-- E2 ★★★★  From the definitions.
theorem sub_dual_dual (P : PhaseSpace) (G : P.M → Prop) (m : P.M) (h : G m) :
    P.dual (P.dual G) m :=
  sorry

theorem dual_is_fact (P : PhaseSpace) (G : P.M → Prop) : P.IsFact (P.dual G) :=
  sorry

-- E3 ★★★  Validity is closed under cut.
theorem valid_cut (A : Form) (Γ Δ : List Form) (h₁ : Valid (A :: Γ)) (h₂ : Valid (Aᗮ :: Δ)) :
    Valid (Γ ++ Δ) :=
  sorry
