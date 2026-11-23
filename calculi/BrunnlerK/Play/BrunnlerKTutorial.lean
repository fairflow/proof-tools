/-
# `Play/BrunnlerKTutorial.lean`: system K in Lean, a tutorial

Prepared by the operator (2026-11-23), at the end of the campaign.  It is
in no library.  Build the instance first (`lake build`, in
`calculi/BrunnlerK/`), then open this file in the editor and put the
cursor on each line in turn: the goal, or the message, is in the
infoview.  Unlike the exercises file (`Play/BrunnlerK.lean`) this one
shows the answers.  Change anything: nothing else depends on this file.

The calculus: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1,
Chapter 2, §2.1.  The user's guide: `campaign/users-guide.md`.

Contents: 1 a sequent; 2 a proof, a move at a time; 3 asking what
applies; 4 patterns; 5 a script; 6 tactics of the calculus; 7 a walk;
8 a sequent with no proof; 9 out to the mathematics.
-/
import BrunnlerK.Explore
import BrunnlerK.Contract

open ProofTools ProofTools.Explore BrunnlerK

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3
abbrev a : Form := .atom 4
abbrev b : Form := .atom 5
abbrev c : Form := .atom 6
abbrev d : Form := .atom 7

/-! ## 1. A sequent

A nested sequent is typed `seq[…]`: formulas, and boxes in square
brackets.  In a formula `⋎` is `∨` (`\curlyvee`), `⋏` is `∧`
(`\curlywedge`), `∼` is the negation (`\sim`), `⊃` is implication
(`\ssup`); `◇` is `\Diamond` and `□` is `\Box`.  Formulas are in negation
normal form: `∼` and `⊃` are functions, and are gone once typed. -/

-- As the source displays it, and as its tree: a node on each line, its
-- boxes below it.
#eval (seq[◇(∼a ⋏ ∼b), ◇b, [a, [b], []], [∼a ⋏ ∼b, a]]).show
#eval IO.println (seq[◇(∼a ⋏ ∼b), ◇b, [a, [b], []], [∼a ⋏ ∼b, a]]).tree

-- `□(a ∨ b) ⊃ (□a ∨ ◇b)` is the formula `◇(ā ∧ b̄) ∨ (□a ∨ ◇b)`.
#eval (seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)]).show

/-! ## 2. A proof, a move at a time

The source's Example 2.3 (pp. 9–10).  A goal is an attempt at a sequent;
each line is one rule, read upwards.  A move says where it acts by a
path: `[]` is the root, `[0]` its first box. -/

def ex23 : Der S seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  -- the rule □ on `□a`, at the root: `□a` goes, a box `[a]` comes
  kmove box [] a
  -- the goal is now  ◇(ā ∧ b̄), ◇b, [a]
  -- the rule ◇k_c on `◇(ā ∧ b̄)`, into box 0: `ā ∧ b̄` is put into the box
  kmove dia [] 0 (∼a ⋏ ∼b)
  -- the goal is now  ◇(ā ∧ b̄), ◇b, [ā ∧ b̄, a]
  -- the rule ∧ inside box 0: two goals, one with `ā`, one with `b̄`
  kmove and [0] (∼a) (∼b)
  -- goal 0:  ◇(ā ∧ b̄), ◇b, [ā, a]   the axiom, on the proposition numbered 4
  kmove ax [0] 4
  -- the goal left:  ◇(ā ∧ b̄), ◇b, [b̄, a]   it needs `b` in the box
  kmove dia [] 0 b
  kmove ax [0] 5

/-! ## 3. Asking what applies

`kmove` alone makes no move: it lists the moves that apply at goal 0.
Click one in the infoview to write it.  `kmove where` draws the attempt
so far, with goal 0 marked `>`. -/

example : Att S true seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  kmove                    -- one move applies: `kmove box [] a`
  kmove box [] a
  kmove                    -- two: a ◇k_c for each diamond
  kmove dia [] 0 (∼a ⋏ ∼b)
  kmove and [0] (∼a) (∼b)
  kmove where              -- the attempt, drawn; two goals are open
  all_goals leave_open     -- leave them open, without an error

/-! ## 4. Patterns

A move's arguments may be left out.  `kmove box` is made if one `□`
applies.  `_` stands for any argument: `kmove dia _ _ (_ ⋏ _)` is the
`◇k_c` whose formula is a conjunction.  `kmove ax` finds the proposition
and the node. -/

example : Der S seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  kmove box
  kmove dia _ _ (_ ⋏ _)
  kmove and
  kmove ax
  kmove dia _ _ b          -- two ◇k_c apply here, so the formula is named
  kmove ax

/-! ## 5. A script

A proof built by `kmove` is data.  Its script is the list of its lines:
the goal each acted at, and the move.  `apply_script` runs a script; what
it leaves can be continued by hand. -/

#eval ex23.script.length                      -- 6
#eval derives S seq[◇(∼a ⋏ ∼b), □a, ◇b] ex23.script   -- true: it runs to the end

example : Der S seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  apply_script ex23.script.take 3      -- the first three lines
  kmove ax
  kmove dia _ _ b
  kmove ax

/-! ## 6. Tactics of the calculus

A tactic of the calculus is a program that gives a script for a sequent.

* `routine n` does the steps that need no choice (the axiom, `∨`, `∧`,
  `□`) wherever they apply.  What it leaves has only `◇k_c` to try.
* `found` is the search of `BrunnlerK/Search.lean`: the script of a proof,
  where there is one.

`apply_script` takes the script as a closed term, so the sequent is
written out again for the tactic. -/

example : Der S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] := by
  apply_script (routine 20 seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).getD []
  -- two goals are left:  ◇(ā ∨ b̄), [a]   and   ◇(ā ∨ b̄), [b]
  kmove dia
  kmove or
  kmove ax
  kmove dia
  kmove or
  kmove ax

-- The whole proof, from the search.
def byTheSearch : Der S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] := by
  apply_script (found seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]).getD []

#eval byTheSearch.script.length              -- 10

/-! ## 7. A walk

`#walk d` draws a derivation at its root and offers the motions from
there; `#walk d down 0 down 0` goes on from it.  In a block whose goal is
`Walk d`, each line is a motion (`down i`, `up`, `left`, `right`, `top`)
and the infoview shows the view there. -/

#walk ex23
#walk ex23 down 0 down 0

example : Walk byTheSearch := by
  down 0        -- the premise of ∨, where the rule is ∧
  down 1        -- the right premise of ∧:  □b, ◇(ā ∨ b̄)
  up

/-! ## 8. A sequent with no proof

The axiom 4, `□a ⊃ □□a`, is not a theorem of K.  The moves go so far and
stop; the open sequent is the countermodel. -/

example : Att S true seq[□a ⊃ □□a] := by
  -- to  ◇ā, □□a
  kmove or
  -- to  ◇ā, [□a]
  kmove box
  -- to  ◇ā, [ā, □a]
  kmove dia
  -- to  ◇ā, [ā, [a]]
  kmove box
  -- one move is offered, and it adds nothing: a ◇k_c that puts `ā` where
  -- it is already
  kmove
  kmove where
  leave_open

-- The search says the same, with the countermodel as a finite tree: a
-- chain of three states, `a` true at the second only.
#eval refute? seq[□a ⊃ □□a]
#eval (found seq[□a ⊃ □□a]).isNone           -- true: no proof

-- As theorems, checked by the kernel.  The first runs the search in the
-- kernel; the second checks the tree given.
example : ¬ Valid seq[□a ⊃ □□a] := by decide +kernel
example : ¬ Valid seq[□a ⊃ □□a] :=
  noValid.verdict _ (.node [] [.node [4] [.node [] []]])

/-! ## 9. Out to the mathematics

What `kmove` builds is a derivation of the proof system `S`.  `famOfDer`
carries it to a proof in system K as the source states it, the family
`K`; the theorems of the campaign are about that family. -/

-- A proof in system K, as data.
def ex23K : K seq[◇(∼a ⋏ ∼b), □a, ◇b] := famOfDer ex23

#eval ex23K.depth                             -- 4

-- So the sequent is valid (soundness) …
example : Valid seq[◇(∼a ⋏ ∼b), □a, ◇b] := soundness _ ex23K

-- … and a valid sequent has a proof (completeness), found by the search.
example : K seq[◇(∼a ⋏ ∼b), □a, ◇b] := complete (soundness _ ex23K)

-- Weakening, with the depth: from this proof, one of the sequent with
-- `c, [d]` added at the root, no deeper.
example : ∃ e : K seq[c, ◇(∼a ⋏ ∼b), □a, ◇b, [d]], e.depth ≤ 4 :=
  wk (Ctx.root seq[◇(∼a ⋏ ∼b), □a, ◇b]) seq[c, [d]] ex23K
