/-
# `Play/BrunnlerK.lean`: Brünnler's nested sequent system K, a move at a time

The reviewer's file.  The operator prepared it (2026-11-23) and does not
edit it again without saying so (`campaign/gates.md`).  It is in no library:
no `lake build` builds it and nothing imports it.  Build the instance first
(`lake build`, in `calculi/BrunnlerK/`), then open this file in the editor
and type.

`kmove` is `apply_move` of proof-tools, fixed to system K (declared in
`BrunnlerK/Tactic.lean`).  A goal is an attempt `Att S true Γ`, shown as
`Att S   ` and the nested sequent `Γ` as the source displays one: its
formulas, then its boxes in square brackets, `ā` for a negated proposition.
For example `◇(ā ∧ b̄), ◇b, [a]`.

**How to type a sequent.**  `seq[◇(∼a ⋏ ∼b), □a, ◇b, [a, [b]], []]`: an item
in square brackets is a box.  In a formula:

    ⋎   \curlyvee      the source's ∨            ◇   \Diamond
    ⋏   \curlywedge    the source's ∧            □   \Box
    ∼   \sim           the negation `Ā`, a function: `∼(a ⋏ b)` is `∼a ⋎ ∼b`
    ⊃   \ssup          `A ⊃ B` is `∼A ⋎ B`

**How a move says where it acts.**  By a path: `[]` is the root, `[0]` its
first box, `[0, 1]` the second box of its first box.  Boxes are counted
from 0, in the order shown.

**How to type a line.**

    kmove                the moves that apply at goal 0; none is made
    kmove an             those whose names begin with `an`
    kmove and            `and` with its arguments left out: made if only one
                         move of that form applies, else each is offered
    kmove dia [] _ b     `_` or `?_` for any argument
    kmove … at 1         the same at goal 1
    kmove where          the attempt so far, drawn, with goal 0 marked `>`;
                         no move is made

Click an offered line to write it in place of yours.  A line that offers
makes no move.  A line that nothing completes is an error, and so is a
query where no move applies.

**The rules** (Figure 2.3 of the source; the table, with each rule's place
in the source, is `campaign/rule-table.md`; keep it and the figure beside
this file).  In each, `a` is the path of a node:

    ax a n        the node has the proposition numbered `n` and its negation;
                  no premise.  (`p q r s a b c d` are numbered 0 to 7: for
                  `a, ā` the move is `ax … 4`.  `kmove ax` finds it.)
    and a A B     the node has `A ∧ B`; two premises: `A` in its place, `B`
                  in its place
    or a A B      the node has `A ∨ B`; one premise: `A, B` in its place
    box a A       the node has `□A`; one premise: a new box `[A]` in its
                  place, after the boxes the node has
    dia a i A     the node has `◇A` and a box at position `i`; one premise:
                  `A` put into that box.  `◇A` stays

A formula a rule adds is put in front of the node's formulas, so the order
within a node is not the source's; the formulas are the same.

A `dia` that would put into a box a formula the box already has is set
aside: it is offered only where no other move applies.

`all_goals leave_open` at the end of an exercise leaves what is not yet
proved open, without an error.  When a proof is done, delete that line and
change `Att S true` to `Der S`: a derivation, which `famOfDer` carries to a
derivation of system K as the source states it (`BrunnlerK.K`).

Reference derivations: `BrunnlerK/Test/Proof.lean`.  They are not in this
file on purpose.
-/
import BrunnlerK.Tactic

open ProofTools ProofTools.Explore BrunnlerK

-- The lines the tactic suggests write a proposition by a name.  Each is
-- declared under that name here, so that a suggested line can be clicked
-- and still parses.
abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3
abbrev a : Form := .atom 4
abbrev b : Form := .atom 5
abbrev c : Form := .atom 6
abbrev d : Form := .atom 7

/-! ## 1. Example 2.3 (pp. 9–10), from the sequent `◇(ā ∧ b̄), □a, ◇b`

The source's one worked derivation in system K.  Upwards: `□`, `◇k_c`, `∧`,
and `◇k_c` once more on the right branch. -/

example : Att S true seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  kmove
  all_goals leave_open

/-! ## 2. Example 2.3, from its formula `□(a ∨ b) ⊃ (□a ∨ ◇b)`

The last line of the source's example is an equation, not a rule: the
formula is `◇(ā ∧ b̄) ∨ (□a ∨ ◇b)`.  The rule `∨` twice, then as in 1. -/

example : Att S true seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)] := by
  kmove
  all_goals leave_open

/-! ## 3. `□(a ∧ b) ⊃ (□a ∧ □b)`

The source has no further derivation in system K: exercises 3 to 6 are the
operator's choice. -/

example : Att S true seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] := by
  kmove
  all_goals leave_open

/-! ## 4. `(□a ∧ □b) ⊃ □(a ∧ b)` -/

example : Att S true seq[(□a ⋏ □b) ⊃ □(a ⋏ b)] := by
  kmove
  all_goals leave_open

/-! ## 5. `□□(a ∨ ā)`: the rules act two boxes deep -/

example : Att S true seq[□□(a ⋎ ∼a)] := by
  kmove
  all_goals leave_open

/-! ## 6. A sequent that is not derivable: `□a ⊃ □□a` (axiom 4)

Go as far as the moves go.  What should happen: after `∨`, `□`, `◇k_c`, `□`
the goal is `◇ā, [ā, [a]]`, and the one move offered is a `◇k_c` that puts
`ā` where it is already.  The open sequent is the countermodel: three states
in a chain, `a` true at the second and not at the third. -/

example : Att S true seq[□a ⊃ □□a] := by
  kmove
  all_goals leave_open

/-! ## 7. Not derivable: `◇p̄, ◇p` (axiom d, `□p ⊃ ◇p`)

Type `kmove` on a line above `all_goals leave_open`.  What should happen:
an error, `kmove: no move applies at goal 0`.  There is no box.  (The query
is not written here, so that the file has no error as it stands.) -/

example : Att S true seq[◇(∼p), ◇p] := by
  all_goals leave_open

/-! ## 8. Not derivable: `◇p̄, p` (axiom t, `□p ⊃ p`)

As 7: the query is an error, no move applies. -/

example : Att S true seq[◇(∼p), p] := by
  all_goals leave_open

/-! ## 9. Not derivable: `p̄, □◇p` (axiom b, `p ⊃ □◇p`)

What should happen: after `□` the goal is `p̄, [◇p]`, and a query there is
an error: no move applies. -/

example : Att S true seq[∼p, □◇p] := by
  kmove
  all_goals leave_open

/-! ## 10. Not derivable: `□p̄, □◇p` (axiom 5, `◇p ⊃ □◇p`)

What should happen: after `□` twice the goal is `[p̄], [◇p]`, and a query
there is an error: no move applies. -/

example : Att S true seq[□(∼p), □◇p] := by
  kmove
  all_goals leave_open

/-! ## 11. Not derivable: `◇(p̄ ∧ q̄), □p, □q` (`□(p ∨ q) ⊃ □p ∨ □q`)

What should happen: after `□` twice, `◇k_c` into each box and `∧` in each,
two branches close by the axiom and one stays open, at
`◇(p̄ ∧ q̄), [q̄, p], [p̄, q]`.  A `◇k_c` still applies there, and after it
`∧` again: in system K the moves do not run out by themselves. -/

example : Att S true seq[◇(∼p ⋏ ∼q), □p, □q] := by
  kmove
  all_goals leave_open

/-! ## To look at a derivation that is built

Name one and walk it.  With `#walk`, a click on an offered motion writes
it.  In a block whose goal is `Walk small`, each line is a motion (`down i`,
`up`, `left`, `right`, `top`, `goal k`) and the goal shows the view there. -/

def small : Der S seq[□(a ⋎ ∼a)] := by
  kmove box [] (a ⋎ ∼a)
  kmove or [0] a (∼a)
  kmove ax [0] 4

#walk small
#walk small down 0

example : Walk small := by
  down 0

-- The derivation of system K itself, as the source states it:
example : K seq[□(a ⋎ ∼a)] := famOfDer small
