/-
Tests of formulas, nested sequents and their functions: the source's own
examples, the printer, and that each function reduces in the kernel.
-/
import BrunnlerK.Show

namespace BrunnlerK.Test

open BrunnlerK NSeq

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev a : Form := .atom 4
abbrev b : Form := .atom 5
abbrev c : Form := .atom 6
abbrev d : Form := .atom 7

/-! ## Formulas

The printer writes a negated proposition as its letter followed by the
combining macron U+0304; the expected texts below spell it `\u0304`, so
that the comparison does not depend on how an editor composes `ā`. -/

-- The negation, clause by clause, and that it is an involution here.
example : ∼p = .natom 0 := rfl
example : ∼(∼p) = p := rfl
example : ∼(□(a ⋎ b)) = ◇(∼a ⋏ ∼b) := rfl
example : ∼(◇(a ⋏ ∼b)) = □(∼a ⋎ b) := rfl

-- The last line of Example 2.3 (p. 9) is an equation, not a rule:
-- `□(a ∨ b) ⊃ (□a ∨ ◇b)` is `◇(ā ∧ b̄) ∨ (□a ∨ ◇b)`.
example : (□(a ⋎ b) ⊃ (□a ⋎ ◇b)) = ◇(∼a ⋏ ∼b) ⋎ (□a ⋎ ◇b) := rfl

-- Left-associative, as the source says.
example : a ⋎ b ⋎ c = (a ⋎ b) ⋎ c := rfl
example : a ⋏ b ⋏ c = (a ⋏ b) ⋏ c := rfl

#guard (□(a ⋎ b) ⊃ (□a ⋎ ◇b)).show == "◇(a\u0304 ∧ b\u0304) ∨ (□a ∨ ◇b)"
#guard (a ⋎ b ⋎ c).show == "a ∨ b ∨ c"
#guard (a ⋎ b ⋏ c).show == "a ∨ b ∧ c"
#guard ((a ⋎ b) ⋏ c).show == "(a ∨ b) ∧ c"
#guard (□◇(∼p)).show == "□◇p\u0304"
#guard (Form.atom 9).show == "p9"

/-! ## Sequents -/

/-- A sequent from its formulas and its boxes, for writing tests. -/
def mk (fs : List Form) : List NSeq → NSeq
  | [] => .leaf fs
  | Δ :: bs => .cons Δ (mk fs bs)

-- The sequents of Example 2.3, as the source displays them (formulas
-- first, then boxes: the source writes the box where `□a` stood).
def ex23a : NSeq := mk [◇(∼a ⋏ ∼b), □a, ◇b] []
def ex23b : NSeq := mk [◇(∼a ⋏ ∼b), ◇b] [mk [a] []]
def ex23c : NSeq := mk [◇(∼a ⋏ ∼b), ◇b] [mk [a, ∼a ⋏ ∼b] []]

#guard ex23a.show == "◇(a\u0304 ∧ b\u0304), □a, ◇b"
#guard ex23b.show == "◇(a\u0304 ∧ b\u0304), ◇b, [a]"
#guard ex23c.show == "◇(a\u0304 ∧ b\u0304), ◇b, [a, a\u0304 ∧ b\u0304]"

-- The example on p. 8: the context `A, [[B], { }]` filled with `C, [D]`
-- is `A, [[B], C, [D]]`.  The hole is at the path `[0]`.
def ctx : NSeq := mk [a] [mk [] [mk [b] []]]
def filled : NSeq := mk [a] [mk [c] [mk [b] [], mk [d] []]]

#guard ctx.show == "a, [[b]]"
#guard filled.show == "a, [c, [b], [d]]"
#guard (ctx.node? [0]).map NSeq.show == some "[b]"
#guard ((ctx.node? [0]).map fun Δ => (ctx.setNode [0] ((Δ.add c).addBox (mk [d] []))).show)
  == some "a, [c, [b], [d]]"

-- The empty sequent, and an empty box, which is something.
#guard (mk [] []).show == "∅"
#guard (mk [a] [mk [] []]).show == "a, [∅]"
#guard mk [a] [mk [] []] != mk [a] []

-- Each function, on `filled`.
#guard filled.forms == [a]
#guard filled.boxes.map NSeq.show == ["c, [b], [d]"]
#guard (filled.node? [0, 1]).map NSeq.show == some "d"
#guard (filled.node? [0, 2]).isNone
#guard (filled.node? [1]).isNone
#guard (filled.setNode [0, 1] (mk [p, q] [])).show == "a, [c, [b], [p, q]]"
#guard filled.setNode [0, 2] (mk [p] []) == filled
#guard ((mk [a, b, a] []).erase a).show == "b, a"
#guard ((mk [a, b] []).erase c).show == "a, b"
#guard ((mk [a] [mk [b] []]).addBox (mk [c] [])).show == "a, [b], [c]"
#guard ((mk [a] [mk [b] [], mk [c] []]).setBox 1 (mk [d] [])).show == "a, [b], [d]"
#guard ((mk [a] [mk [b] [], mk [c] []]).box? 1).map NSeq.show == some "c"

-- In the kernel: the functions the rules use reduce on a small sequent.
example : filled.node? [0, 1] = some (mk [d] []) := by decide +kernel
example : ctx.setNode [0] (mk [c] [mk [b] [], mk [d] []]) = filled := by decide +kernel
example : (mk [a, b, a] []).erase a = mk [b, a] [] := by decide +kernel
example : (mk [b] [mk [c] []]).add a = mk [a, b] [mk [c] []] := by decide +kernel
example : (mk [a] [mk [b] []]).addBox (mk [c] []) = mk [a] [mk [b] [], mk [c] []] := by
  decide +kernel
example : (mk [a] [mk [b] [], mk [c] []]).setBox 1 (mk [d] []) = mk [a] [mk [b] [], mk [d] []] := by
  decide +kernel
example : ◇b ∈ ex23b.forms := by decide +kernel

/-! ## Set sequents (Definition 2.13) -/

-- The same set sequent: order and repetition do not count, at any depth.
example : (mk [a, b, a] [mk [c, c] [], mk [c] []]).sameSet (mk [b, a] [mk [c] []]) = true := by
  decide +kernel
-- Different: a formula more; a box more; an empty box against none.
example : (mk [a, b] []).sameSet (mk [a] []) = false := by decide +kernel
example : (mk [a] [mk [b] []]).sameSet (mk [a] [mk [b] [], mk [c] []]) = false := by
  decide +kernel
example : (mk [a] [mk [] []]).sameSet (mk [a] []) = false := by decide +kernel
-- The set sequent can stay the same when a node's own set changes: of
-- three boxes `[c]`, `[c]`, `[c, d]`, add `d` to the first.  So the
-- proviso of `K°` is about the whole sequent, as the source states it.
example : ((mk [] [mk [c] [], mk [c] [], mk [c, d] []]).setNode [0] (mk [d, c] [])).sameSet
    (mk [] [mk [c] [], mk [c] [], mk [c, d] []]) = true := by decide +kernel
example : (mk [d, c] []).sameSet (mk [c] []) = false := by decide +kernel

end BrunnlerK.Test
