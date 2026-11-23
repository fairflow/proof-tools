/-
# `ProofTools.Explore.View`: an attempt drawn as text

What an instance supplies for the editor (`Explorable`), and every drawing
of an attempt as text, made through its two printers (`showJudg`,
`showMove`).

**All of an attempt** (`Att.render`): each node its judgment and its move,
the premises indented below; an open goal is marked `?`.

     ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
      (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
        p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
          ? p0, p1, (p0 ∧ p1) ⊢ p1
          p0, p1, (p0 ∧ p1) ⊢ p0   by ax

**The view at a position** (`Cursor.view`), for walking an attempt:

      ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR          the nodes from the root
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1      down to the focus
    >     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR    the focus, marked `>`
            0: ? p0, p1, (p0 ∧ p1) ⊢ p1              its premises, numbered:
            1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]    open (`?`), or a node
      at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all

The last line is the address of the focus (the premise numbers from the
root), and where the open goals are.  The premises of the focus are drawn
one line each: `down i` goes to premise `i`.

**The view with every branch drawn** (`Cursor.viewAll`), for seeing where a
position is in the whole attempt: the lines of `Att.render`, the focus
marked `>`, and the last line of the view.

      ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
          p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
    >       ? p0, p1, (p0 ∧ p1) ⊢ p1
            p0, p1, (p0 ∧ p1) ⊢ p0   by ax
      at 0.0.0: open goal 0; 1 open in all

**Each thing is drawn by one function.**  A node, made or open, by
`nodeLines`; a whole attempt by `Att.lines`; what is around a focus (the
nodes on the way from the root, and with them or without them their other
premises) by `Path.linesAround`, which goes up the path of the zipper crumb
by crumb as `Path.plug` does.  The two views differ in one flag.

Code for the editor: nothing here is trusted, and nothing is proved here.

Core Lean only.
-/
import Lean
import ProofTools.Explore.Motion

namespace ProofTools.Explore

open Lean

/-! ## What an instance supplies for the editor -/

/-- **What an instance supplies for the editor.**  None of it is trusted.

To declare an instance, the system must be an `abbrev` (or `@[reducible]`),
so that `S.Judg` unfolds to the instance's own type where Lean looks for
instances and notations. -/
class Explorable (S : ProofSystem) where
  /-- Moves to try at a judgment; those that apply are offered, and
  patterns are matched against them. -/
  candidates : S.Judg → List S.Move
  /-- A judgment as text, for `Att.render`. -/
  showJudg : S.Judg → String
  /-- A move as text, for `Att.render`. -/
  showMove : S.Move → String
  /-- Judgments as terms: the goals the tactic leaves are literals. -/
  quoteJudg : ToExpr S.Judg
  /-- Moves as terms. -/
  quoteMove : ToExpr S.Move
  /-- `within p j`: the premise `p` adds nothing to the conclusion `j`.  A
  move with such a premise is offered only if no other applies. -/
  within : S.Judg → S.Judg → Bool := fun _ _ => false
  /-- A move as Lean source, as `apply_move` is to be given it, for the
  lines the tactic suggests.  Where it gives nothing, the move's term
  (`quoteMove`) is printed by Lean. -/
  moveSource : S.Move → Option String := fun _ => none
  /-- How the tactic proves a node's equation `S.step m j = .ok ps`.  By
  `rfl` (`false`, the default): the premises as quoted must be, by
  definition, what `step` computes.  By deciding the equality (`true`):
  they need only be equal, and an instance of `DecidableEq S.Judg` is
  needed.  An instance whose judgments hold functions needs the second,
  since a function quoted is seldom the function computed. -/
  eqByDecide : Bool := false

variable {S : ProofSystem}

/-! ## A node -/

/-- A judgment's text under an indentation; `mark` goes before its first
line, and as many spaces before the others. -/
def judgLines (ind mark text : String) : List String :=
  match text.splitOn "\n" with
  | [] => [ind ++ mark]
  | l :: ls => (ind ++ mark ++ l) :: ls.map fun x => ind ++ "".pushn ' ' mark.length ++ x

/-- **A node as lines**: its judgment under an indentation and after a
mark.  For a node that is made, its move is beside a judgment of one line
and below a longer one, and `note` comes after the move.  For an open goal
(no move) the sign `?` is before the judgment.  Every drawing of a node is
this one. -/
def nodeLines [E : Explorable S] (ind mark : String) (j : S.Judg) (m : Option S.Move)
    (note : String) : List String :=
  match m with
  | none => judgLines ind (mark ++ "? ") (E.showJudg j)
  | some m =>
    match judgLines ind mark (E.showJudg j) with
    | [l] => [l ++ "   by " ++ E.showMove m ++ note]
    | ls => ls ++ [ind ++ "".pushn ' ' mark.length ++ "   by " ++ E.showMove m ++ note]

/-! ## All of an attempt -/

mutual
/-- The lines of an attempt drawn as text: each node its judgment and its
move, the premises indented below; an open goal is marked `?`.  A judgment
of one line has its move beside it, a longer one below it. -/
def Att.lines [Explorable S] : {o : Bool} → {j : S.Judg} → Att S o j → String → List String
  | _, j, .goal, ind => nodeLines ind "" j none ""
  | _, j, .node m _ _ ds, ind => nodeLines ind "" j (some m) "" ++ ds.lines (ind ++ "  ")
/-- `Att.lines` on a list. -/
def Atts.lines [Explorable S] : {o : Bool} → {ps : List S.Judg} → Atts S o ps → String →
    List String
  | _, _, .nil, _ => []
  | _, _, .cons d ds, ind => d.lines ind ++ ds.lines ind
end

/-- **An attempt drawn as text.** -/
def Att.render [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) : String :=
  "\n".intercalate (d.lines "")

/-! ## The view at a position -/

/-- **What is around a hole, as lines**, given the lines at the hole
(`ls`): the nodes from the root down to the hole, each with its move and
one step further in than the one before.  With `all`, the other premises of
each of these nodes are drawn too, in full and in their order, so that the
lines are those of the whole attempt (`Att.lines`).  Each line added has two
spaces before it, where the lines at the hole may have the mark `>`.  (The
attempts left of a hole are kept nearest first; `Atts.revAppend` puts them
back in the order of the premises.) -/
def Path.linesAround [Explorable S] (all : Bool) {o : Bool} : {ds : List Nat} → {i k : S.Judg} →
    Path S o ds i k → List String → List String
  | _, _, _, .top, ls => ls
  | _ :: ds, _, _, .cons (j := j) ⟨mv, _, _, _, left, right, _⟩ p, ls =>
    let ind := "".pushn ' ' (2 * ds.length + 2)
    Path.linesAround all p
      (nodeLines ind "" j (some mv) "" ++
        (if all then (left.revAppend .nil).lines (ind ++ "  ") else []) ++ ls ++
        (if all then right.lines (ind ++ "  ") else []))

/-- The premises of a node, one after another from number `n`: an open goal
is marked `?`, a node has its move and whether it is closed. -/
def Atts.premiseLines [Explorable S] : {ps : List S.Judg} → Atts S true ps → Nat → String →
    List String
  | _, .nil, _, _ => []
  | p :: _, .cons d ds, n, ind =>
    (match d with
      | .goal => nodeLines ind s!"{n}: " p none ""
      | .node m _ _ _ =>
        nodeLines ind s!"{n}: " p (some m)
          (if d.goals.length = 0 then "   [closed]" else s!"   [{d.goals.length} open]")) ++
      Atts.premiseLines ds (n + 1) ind

/-- The last line of a view: the address of the focus, and where the open
goals are. -/
def Cursor.viewFoot {j : S.Judg} (c : Cursor S j) : String :=
  let addr := if c.pos.ds.isEmpty then "the root" else ".".intercalate (c.addr.map toString)
  let total := c.toRoot.goals.length
  if c.pos.z.focus.isGoal then
    s!"at {addr}: open goal {c.left}; {total} open in all"
  else
    let n := c.pos.z.focus.premises.length
    let prem := if n = 0 then "no premises" else if n = 1 then "1 premise" else s!"{n} premises"
    let goals :=
      if total = 0 then "no open goals"
      else s!"open goals: {c.pos.z.focus.goals.length} under the focus, {c.left} left of it, " ++
        s!"{total} in all"
    s!"at {addr}: {prem}; {goals}"

/-- The two views.  Without `all`: the nodes from the root down to the
focus, and the premises of the focus one line each.  With `all`: every
branch, as `Att.lines` draws it.  In both the focus is marked `>` and the
last line is `Cursor.viewFoot`. -/
def Cursor.viewWith [Explorable S] (all : Bool) {j : S.Judg} (c : Cursor S j) : String :=
  let ind := "".pushn ' ' (2 * c.pos.ds.length)
  let focus :=
    if all then c.pos.z.focus.lines ind
    else
      match c.pos.z.focus with
      | .goal => nodeLines ind "" c.pos.i none ""
      | .node m _ _ ds => nodeLines ind "" c.pos.i (some m) "" ++ Atts.premiseLines ds 0 (ind ++ "  ")
  let marked :=
    match focus with
    | [] => []
    | l :: ls => ("> " ++ l) :: ls.map ("  " ++ ·)
  "\n".intercalate (Path.linesAround all c.pos.z.path marked ++ ["  " ++ c.viewFoot])

/-- **The view at a position**, as text: the nodes from the root down to the
focus, each with its move; the focus, marked `>`; its premises, numbered;
its address, and where the open goals are. -/
def Cursor.view [Explorable S] {j : S.Judg} (c : Cursor S j) : String := c.viewWith false

/-- **The view at a position, with every branch drawn**: the lines of
`Att.render` on the whole attempt, the focus marked `>`; then its address,
and where the open goals are. -/
def Cursor.viewAll [Explorable S] {j : S.Judg} (c : Cursor S j) : String := c.viewWith true

/-- **Where open goal `k` of an attempt is**: the whole attempt drawn, that
goal marked (`Cursor.viewAll` at `goal k`).  With no `k`, or no such goal,
the root is marked. -/
def Att.whereText [Explorable S] {j : S.Judg} (d : Att S true j) (k : Option Nat) : String :=
  let c := Cursor.ofRoot d
  ((k.bind fun k => c.move (.goal k)).getD c).viewAll

end ProofTools.Explore
