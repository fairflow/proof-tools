/-
# `Play/GLSExercises.lean`: the graded exercises of `tutorial.md`

A file to type in.  The tutorial (`tutorial.md`, beside `Play/`) states
each exercise, says what it is for, and has the solutions at its end;
every solution is checked by the build, in `GLS/TutorialTest.lean`.  This
file is in no library: build the instance first (`lake build`, in
`calculi/GLS/`), then open it in the editor with the infoview.

Parts A to C are derivations and attempts, a move at a time:

    glsmove              the moves that apply at goal 0; none is made
    glsmove impR         made if one ImpR applies, else each is offered
    glsmove impL p q     the move, in full
    glsmove where        the attempt so far, drawn
    all_goals leave_open at the end: leaves what is not proved open

When a derivation is done, delete `all_goals leave_open` and change
`Att S true` to `Der S`.

Parts D and E are Lean: each `sorry` is an exercise.  They are the only
`sorry`s of the instance, and nothing imports this file.

Grades: ★ a move or two; ★★ a short derivation; ★★★ wants an idea;
★★★★ a proof or a program in Lean.
-/
import GLS.Explore
import GLS.CutRule
import GLS.PS

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1
abbrev r : Form := .var 2

/-- `¬A` is `A → ⊥`. -/
abbrev neg (A : Form) : Form := A ⟶ ⊥

instance (s : Seq) : Decidable (Valid s) := validDecidable s

/-! ## Part A: the propositional rules -/

-- A1 ★  The two axioms.
example : Att S true ([p] ⇒ [p]) := by
  glsmove
  all_goals leave_open

example : Att S true ([⊥] ⇒ [q]) := by
  glsmove
  all_goals leave_open

-- A2 ★
example : Att S true ([] ⇒ [p ⟶ q ⟶ p]) := by
  glsmove
  all_goals leave_open

-- A3 ★★  Peirce's law.  Watch the succedent.
example : Att S true ([] ⇒ [((p ⟶ q) ⟶ p) ⟶ p]) := by
  glsmove
  all_goals leave_open

-- A4 ★★  Double negation.
example : Att S true ([] ⇒ [neg (neg p) ⟶ p]) := by
  glsmove
  all_goals leave_open

-- A5 ★  Not derivable.  Where do the moves stop?  Which world refutes it?
example : Att S true ([] ⇒ [p ⟶ q]) := by
  glsmove
  all_goals leave_open

/-! ## Part B: the modal rule -/

-- B1 ★  The identity on a boxed variable is not an axiom of GLS.
example : Att S true ([□p] ⇒ [□p]) := by
  glsmove
  all_goals leave_open

-- B2 ★  A box on a theorem.
example : Att S true ([] ⇒ [□(p ⟶ p)]) := by
  glsmove
  all_goals leave_open

-- B3 ★★  K.
example : Att S true ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove
  all_goals leave_open

-- B4 ★★  4.  GLS has no rule for transitivity: where does it come from?
example : Att S true ([] ⇒ [□p ⟶ □□p]) := by
  glsmove
  all_goals leave_open

-- B5 ★★
example : Att S true ([] ⇒ [□⊥ ⟶ □p]) := by
  glsmove
  all_goals leave_open

-- B6 ★★★  Löb's axiom.  GLR is used twice.
example : Att S true ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  glsmove
  all_goals leave_open

-- B7 ★★★  The second incompleteness theorem, formalised: ¬□⊥ → ¬□¬□⊥.
example : Att S true ([] ⇒ [neg □⊥ ⟶ neg □(neg □⊥)]) := by
  glsmove
  all_goals leave_open

/-! ## Part C: countermodels

A tree is written `.node [the numbers of the variables true at the root]
[its children]`; a world sees every world below it.  The kernel checks a
tree against a sequent in `noDerivable.verdict _ t`.  To see the search's
answer: `#eval IO.println (explain s)`. -/

-- C1 ★  Go as far as the moves go.  Then replace the tree below by yours.
example : Att S true ([] ⇒ [□p ⟶ p]) := by
  glsmove
  all_goals leave_open

-- C2 ★★  Write the tree.  (This one is wrong: the kernel says so.)
-- example : ¬ Derivable ([] ⇒ [□□p ⟶ □p]) := noDerivable.verdict _ (.node [] [])

-- C3 ★★  The converse of K.
-- example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) := noDerivable.verdict _ (.node [] [])

-- C4 ★★  GL does not derive its own consistency.
-- example : ¬ Derivable ([] ⇒ [neg □⊥]) := noDerivable.verdict _ _

-- C5 ★★  Löb's axiom is about provability, not truth.
-- example : ¬ Derivable ([□(□p ⟶ p)] ⇒ [p]) := noDerivable.verdict _ _

-- C6 ★★★  How many worlds are needed, and why?
-- example : ¬ Derivable ([] ⇒ [□□□⊥ ⟶ □□⊥]) := noDerivable.verdict _ _

/-! ## Part D: the theorems, used

The functions on derivations (`tutorial.md`, section 5):

    Fam.id         A ∈ Γ → A ∈ Δ → Fam (Γ ⇒ Δ)
    weakeningL     Fam (Γ0 ++ Γ1 ⇒ Δ) → { d' : Fam (Γ0 ++ A :: Γ1 ⇒ Δ) // … }
    weakeningR     Fam (Γ ⇒ Δ0 ++ Δ1) → { d' : Fam (Γ ⇒ Δ0 ++ A :: Δ1) // … }
    inversionImpR  Fam (Γ ⇒ Δ) → A ⟶ B ∈ Δ → { d' : Fam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)) // … }
    cutBySource    Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ A :: Δ1) → Fam (Γ0 ++ A :: Γ1 ⇒ Δ0 ++ Δ1)
                     → Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ Δ1)
    cutElimination (s : Seq) → FamCut s → Fam s
-/

-- D1 ★★  Predict the height before you evaluate.
def d1 : Fam ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) := Fam.id (□(p ⟶ q)) (by decide) (by decide)
-- #eval d1.height

-- D2 ★★★  Necessitation is a derived rule.
def nec {A : Form} (d : Fam ([] ⇒ [A])) : Fam ([] ⇒ [□A]) :=
  sorry

-- D3 ★★★★  Modus ponens is a derived rule.
def mp {A B : Form} (d₁ : Fam ([] ⇒ [A ⟶ B])) (d₂ : Fam ([] ⇒ [A])) : Fam ([] ⇒ [B]) :=
  sorry

-- D4 ★★★★  Löb's rule: from ⇒ □A → A to ⇒ A.
def lobRule {A : Form} (d : Fam ([] ⇒ [□A ⟶ A])) : Fam ([] ⇒ [A]) :=
  sorry

-- D5 ★★  Build a derivation with one cut, and eliminate it both ways.
-- (`FamCut.cut`, `Fam.toCut`, `cutElimination`, `cutEliminationBySearch`.)

-- D6 ★★★  Consistency of GLS + (cut), with no model.
theorem consistent : FamCut ([] ⇒ []) → False :=
  sorry

-- D7 ★★★★  GLS does not derive □⊥, with no model.
theorem box_bot_not_derivable : Fam ([] ⇒ [□⊥]) → False := by
  sorry

-- D8 ★★  What GLR does to a multiset.
-- #eval (xbox [□□p, □q, r, p ⟶ q]).map Form.show

/-! ## Part E: the semantics, in Lean -/

-- E1 ★  The kernel runs the search.
-- example : Valid ([] ⇒ [□p ⟶ □□p]) := by decide +kernel

-- E2 ★★★★  No world of a model of GL sees itself.
theorem irrefl (M : Model) (h : M.GL) (w : M.W) : ¬ M.R w w := by
  sorry

-- E3 ★★★★  Löb's axiom is true in every model of GL.
theorem lob_true (M : Model) (h : M.GL) (A : Form) (w : M.W) :
    M.sat w (□(□A ⟶ A) ⟶ □A) := by
  sorry

-- E4 ★★  E3 has no hypothesis that the model is two-valued; `Valid` has
-- one.  Which rule of GLS needs it?  (Read `GLS/Soundness.lean`.)
