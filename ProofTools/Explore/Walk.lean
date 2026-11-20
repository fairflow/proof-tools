/-
# `ProofTools.Explore.Walk`: looking at an attempt that is built

An attempt or a derivation is a value: the term a tactic proof builds,
`(run S j ls).att`, `Der.ofScript j ls h`, what a search returns.  This
file is for looking at one, position by position, with the motions of
`ProofTools.Explore.Motion`.  Nothing here changes the attempt.

**The view** at a position (`Cursor.view`), as text through the instance's
printers (`Explorable`):

      ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR          the nodes from the root
        (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1      down to the focus
    >     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR    the focus, marked `>`
            0: ? p0, p1, (p0 ∧ p1) ⊢ p1              its premises, numbered:
            1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]    open (`?`), or a node
      at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all

The last line is the address of the focus (the premise numbers from the
root), and where the open goals are.  The premises of the focus are drawn
one line each: `down i` goes to premise `i`.

**The command `#walk`** names an attempt and makes motions from its root:

    #walk d                       the view at the root
    #walk d down 0 down 0 up      the view after these motions
    #walk d                       a motion to a line: the view after each line
      down 0                      is a message at that line, so the infoview
      down 0                      follows the editor's cursor
      up

The motions are `up`, `down i`, `left`, `right`, `top`, `goal k`; a comma
may follow one.  A motion that cannot be made is an error at that motion,
saying why; the view before it is shown.

`walkText d ms` is the view after the motions `ms`, as a function, for use
without the command.

Code for the editor: nothing here is trusted, and nothing is proved here.
What a motion does is proved in `Motion.lean`.

Core Lean only.
-/
import Lean
import ProofTools.Explore.Motion
import ProofTools.Explore.Tactic

namespace ProofTools.Explore

open Lean Meta Elab Command

variable {S : ProofSystem}

/-! ## The view -/

/-- The nodes from the focus back to the root, nearest first: the judgment
of each, and its move. -/
def Path.spine {o : Bool} : {ds : List Nat} → {i k : S.Judg} → Path S o ds i k →
    List (S.Judg × S.Move)
  | _, _, _, .top => []
  | _, _, _, .cons (j := j) ⟨mv, _, _, _, _, _, _⟩ p => (j, mv) :: Path.spine p

/-- A node as lines: its judgment under an indentation and after a mark, its
move beside a judgment of one line and below a longer one, a note after the
move. -/
def nodeLines [E : Explorable S] (ind mark : String) (j : S.Judg) (m : S.Move) (note : String) :
    List String :=
  match judgLines ind mark (E.showJudg j) with
  | [l] => [l ++ "   by " ++ E.showMove m ++ note]
  | ls => ls ++ [ind ++ "".pushn ' ' mark.length ++ "   by " ++ E.showMove m ++ note]

/-- The nodes of a spine, root first, each one step further in. -/
def spineLines [Explorable S] : List (S.Judg × S.Move) → String → List String
  | [], _ => []
  | (j, m) :: rest, ind => nodeLines ind "" j m "" ++ spineLines rest (ind ++ "  ")

/-- The premises of a node, one after another from number `n`: an open goal
is marked `?`, a node has its move and whether it is closed. -/
def Atts.premiseLines [E : Explorable S] : {ps : List S.Judg} → Atts S true ps → Nat → String →
    List String
  | _, .nil, _, _ => []
  | p :: _, .cons d ds, n, ind =>
    (match d with
      | .goal => judgLines ind s!"{n}: ? " (E.showJudg p)
      | .node m _ _ _ =>
        nodeLines ind s!"{n}: " p m
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

/-- **The view at a position**, as text: the nodes from the root down to the
focus, each with its move; the focus, marked `>`; its premises, numbered;
its address, and where the open goals are. -/
def Cursor.view [E : Explorable S] {j : S.Judg} (c : Cursor S j) : String :=
  let spine := (Path.spine c.pos.z.path).reverse
  let ind := "".pushn ' ' (2 * spine.length)
  let above := (spineLines spine "").map ("  " ++ ·)
  let here :=
    match c.pos.z.focus with
    | .goal => judgLines ind "? " (E.showJudg c.pos.i)
    | .node m _ _ _ => nodeLines ind "" c.pos.i m ""
  let here :=
    match here with
    | [] => []
    | l :: ls => ("> " ++ l) :: ls.map ("  " ++ ·)
  let below :=
    match c.pos.z.focus with
    | .goal => []
    | .node _ _ _ ds => Atts.premiseLines ds 0 ("  " ++ ind ++ "  ")
  "\n".intercalate (above ++ here ++ below ++ ["  " ++ c.viewFoot])

/-- **The view of `d` after the motions `ms`** from its root; or the number
of the first motion that cannot be made, and why. -/
def walkText [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    Except (Nat × String) String :=
  ((Cursor.ofAtt d).moves ms).map (·.view)

/-- The views along a walk from the root of `d`: at the root, then after
each motion made; and, if a motion cannot be made, its number and why. -/
def walkViews [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    List String × Option (Nat × String) :=
  go 0 (Cursor.ofAtt d) ms
where
  /-- From a cursor, the motions numbered from `n`. -/
  go (n : Nat) (c : Cursor S j) : List Motion → List String × Option (Nat × String)
    | [] => ([c.view], none)
    | m :: ms =>
      match c.move m with
      | some c' => let r := go (n + 1) c' ms; (c.view :: r.1, r.2)
      | none => ([c.view], some (n, c.whyNot m))

/-! ## The command -/

/-- A motion, as `#walk` is given it. -/
declare_syntax_cat walk_motion (behavior := both)

/-- To the node this one is a premise of. -/
syntax "up" : walk_motion
/-- To premise number `i` of the focus, numbered from 0. -/
syntax "down " num : walk_motion
/-- To the premise before this one, of the same node. -/
syntax "left" : walk_motion
/-- To the premise after this one, of the same node. -/
syntax "right" : walk_motion
/-- To the root. -/
syntax "top" : walk_motion
/-- To open goal `k` of the whole attempt, numbered from 0. -/
syntax "goal " num : walk_motion

/-- `#walk d m₁ m₂ …` shows the attempt or derivation `d` at the position
that the motions `m₁ m₂ …` reach from its root: `up`, `down i`, `left`,
`right`, `top`, `goal k`.  With no motion, the root.  Written over several
lines, each line shows the view after it, so the infoview follows the
editor's cursor.  `d` is not changed. -/
syntax (name := walkCmd) withPosition("#walk " term:max (colGt walk_motion ","?)*) : command

/-- A motion's term. -/
def motionTerm (stx : Syntax) : MacroM Term :=
  match stx with
  | `(walk_motion| up) => `(ProofTools.Explore.Motion.up)
  | `(walk_motion| down $n) => `(ProofTools.Explore.Motion.down $n)
  | `(walk_motion| left) => `(ProofTools.Explore.Motion.left)
  | `(walk_motion| right) => `(ProofTools.Explore.Motion.right)
  | `(walk_motion| top) => `(ProofTools.Explore.Motion.top)
  | `(walk_motion| goal $k) => `(ProofTools.Explore.Motion.goal $k)
  | _ => Macro.throwUnsupported

/-- See `evalViews`. -/
unsafe def evalViewsU (e : Expr) : MetaM (List String × Option (Nat × String)) :=
  evalExpr (List String × Option (Nat × String))
    (ToExpr.toTypeExpr (α := List String × Option (Nat × String))) e
/-- Evaluate a closed term of type `List String × Option (Nat × String)`. -/
@[implemented_by evalViewsU]
opaque evalViews (e : Expr) : MetaM (List String × Option (Nat × String))

@[command_elab walkCmd, inherit_doc walkCmd]
def elabWalk : CommandElab := fun stx => do
  let d : Term := ⟨stx[1]⟩
  let motions : Array Syntax := stx[2].getArgs.map (·[0])
  let terms ← motions.mapM fun m => liftMacroM (motionTerm m)
  let (views, failed) ← liftTermElabM do
    let e ← Term.elabTerm (← `(ProofTools.Explore.walkViews $d [$terms,*])) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- the term did not elaborate: Lean has said why
    if e.hasSyntheticSorry then throwAbortCommand
    if e.hasMVar || e.hasFVar then
      throwErrorAt d "#walk: the attempt must be a closed term, of a calculus with an \
        instance of `Explorable`"
    evalViews e
  -- item 0 is `#walk d`; item `k + 1` is motion `k`.  View `k` is shown at
  -- item `k`, when the next item is on a later line or there is none.
  let fileMap ← getFileMap
  let item (k : Nat) : Syntax := if k = 0 then mkNullNode #[stx[0], stx[1]] else motions[k - 1]!
  let lastLine (s : Syntax) : Nat := (s.getTailPos?.map fun p => (fileMap.toPosition p).line).getD 0
  let firstLine (s : Syntax) : Nat := (s.getPos?.map fun p => (fileMap.toPosition p).line).getD 0
  let made := views.length - 1
  for k in [0:views.length] do
    let shown :=
      if k < made then lastLine (item k) < firstLine (item (k + 1))
      else failed.isSome || k = motions.size || lastLine (item k) < firstLine (item (k + 1))
    if shown then logInfoAt (item k) views[k]!
  if let some (n, why) := failed then
    logErrorAt (item (n + 1)) m!"#walk: this motion cannot be made: {why}"

end ProofTools.Explore
