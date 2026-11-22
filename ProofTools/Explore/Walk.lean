/-
# `ProofTools.Explore.Walk`: looking at an attempt that is built

An attempt or a derivation is a value: the term a tactic proof builds,
`(run S j ls).att`, `Der.ofScript j ls h`, what a search returns.  This
file is for looking at one, position by position, with the motions of
`ProofTools.Explore.Motion`.  Nothing here changes the attempt.

What is shown at a position is the view (`Cursor.view`, in `View.lean`):
the nodes from the root down to the focus, the focus marked `>`, its
premises numbered, and a last line with its address and the open goals.

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

**To walk by clicking.**  After the last view, `#walk` offers the motions
that can be made from the position reached (`Cursor.motions`), as
suggestions:

    Motions from here:
      [apply] down 0
      [apply] up
      [apply] top

A click on `[apply]` writes that motion after the last one, on the same
line, so the editor's cursor stays where the next view and the next offer
appear.  The walk stays in the file as text.  `set_option walk.offer false`
turns the offer off.

**The panel** (a trial, `Panel.lean`): with `set_option walk.panel true`,
`#walk` also draws the attempt as a tree in the infoview, with nodes to
click.

**A tactic block** walks as well.  Its goal is `Walk d`, its lines are the
motions, and Lean shows the view after each line as the goal there, so the
infoview's goal follows the editor's cursor with no message in the file:

    example : Walk d := by
      down 0
      down 0
      up

A motion that cannot be made is an error at its line.  The block needs no
last line: the goal left is closed when the block ends.  `left` and `right`
are also tactics of Lean; on any goal that is not a walk they are Lean's.

`walkText d ms` is the view after the motions `ms`, as a function, for use
without the command.

Code for the editor: nothing here is trusted, and nothing is proved here.
What a motion does is proved in `Motion.lean`.

Core Lean only.
-/
import Lean
import ProofTools.Explore.Motion
import ProofTools.Explore.Tactic
import ProofTools.Explore.Panel

namespace ProofTools.Explore

open Lean Meta Elab Command Tactic

variable {S : ProofSystem}

/-! ## The view after motions -/

/-- **The view of `d` after the motions `ms`** from its root; or the number
of the first motion that cannot be made, and why. -/
def walkText [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    Except (Nat × String) String :=
  ((Cursor.ofAtt d).moves ms).map (·.view)

/-- The views along a walk from the root of `d`: at the root, then after
each motion made; and, if a motion cannot be made, its number and why. -/
def walkViews [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    List String × Option (Nat × String) :=
  let t := Cursor.trail 0 (Cursor.ofAtt d) ms
  ((t.passed ++ [t.last]).map (·.view), t.failed)

/-- **The motions offered after the walk `ms`** from the root of `d`, as
they are written (`Cursor.motions`); none if a motion of `ms` cannot be
made. -/
def walkOffers {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) : List String :=
  match (Cursor.ofAtt d).moves ms with
  | .ok c => c.motions.map Motion.text
  | .error _ => []

/-- What `#walk` shows: the views along the walk (`walkViews`); the motions
offered at its end (`walkOffers`) if `offer`; what the panel is given
(`walkPanelData`) if `panel`, else the empty string. -/
def walkShown [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion)
    (offer panel : Bool) : (List String × Option (Nat × String)) × List String × String :=
  (walkViews d ms, if offer then walkOffers d ms else [],
    if panel then walkPanelData d ms else "")

/-! ## The command -/

/-- `walk.offer`: `#walk` offers the motions that can be made from the
position it reaches. -/
register_option walk.offer : Bool := {
  defValue := true
  descr := "#walk offers the motions that can be made from the position it reaches, as \
    suggestions: a click writes the motion after the last one"
}

/-- `walk.panel`: `#walk` also draws the attempt as a tree in the infoview,
with nodes to click (a trial; `Panel.lean`). -/
register_option walk.panel : Bool := {
  defValue := false
  descr := "#walk also draws the attempt as a tree in the infoview, with nodes to click \
    (a trial)"
}

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
editor's cursor.  After the last view the motions that can be made from
there are offered: a click writes one after the last motion
(`set_option walk.offer false` for none).  `d` is not changed. -/
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

/-- See `evalShown`. -/
unsafe def evalShownU (e : Expr) :
    MetaM ((List String × Option (Nat × String)) × List String × String) :=
  evalExpr ((List String × Option (Nat × String)) × List String × String)
    (ToExpr.toTypeExpr (α := (List String × Option (Nat × String)) × List String × String)) e
/-- Evaluate a closed term of the type of `walkShown`. -/
@[implemented_by evalShownU]
opaque evalShown (e : Expr) :
    MetaM ((List String × Option (Nat × String)) × List String × String)

@[command_elab walkCmd, inherit_doc walkCmd]
def elabWalk : CommandElab := fun stx => do
  let d : Term := ⟨stx[1]⟩
  let motions : Array Syntax := stx[2].getArgs.map (·[0])
  let terms ← motions.mapM fun m => liftMacroM (motionTerm m)
  let offer : Term := mkCIdent (if walk.offer.get (← getOptions) then ``true else ``false)
  let panel : Term := mkCIdent (if walk.panel.get (← getOptions) then ``true else ``false)
  let ((views, failed), offers, panelData) ← liftTermElabM do
    let e ← Term.elabTerm (← `(ProofTools.Explore.walkShown $d [$terms,*] $offer $panel)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- the term did not elaborate: Lean has said why
    if e.hasSyntheticSorry then throwAbortCommand
    if e.hasMVar || e.hasFVar then
      throwErrorAt d "#walk: the attempt must be a closed term, of a calculus with an \
        instance of `Explorable`"
    evalShown e
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
  -- The motions that can be made from the position reached, offered at the
  -- last item; a click writes one after it, on the same line.
  else if !offers.isEmpty then
    let last := item motions.size
    if let some p := last.getTailPos? then
      let sugg : Array Lean.Meta.Tactic.TryThis.Suggestion :=
        (offers.take maxOffered).toArray.map fun m =>
          { suggestion := .string (" " ++ m), messageData? := some m!"{m}",
            toCodeActionTitle? := some fun _ => s!"#walk: {m}" }
      let footer : MessageData :=
        if offers.length > maxOffered then m!"\n… and {offers.length - maxOffered} more" else .nil
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestions last sugg
        (origSpan? := some (Syntax.ofRange ⟨p, p⟩)) (header := "Motions from here:")
        (footer := footer)
  -- The panel (a trial): the attempt as a tree, shown while the editor's
  -- cursor is on the command.  `range` is where the motions are written:
  -- from the end of `d` to the end of the last motion, or of its comma.
  if let .ok data := Json.parse panelData then
    if let some dEnd := stx[1].getTailPos? then
      let mEnd := stx[2].getTailPos?.getD dEnd
      let range := fileMap.utf8RangeToLspRange ⟨dEnd, mEnd⟩
      let props := data.setObjVal! "range" (toJson range)
      liftCoreM <| Widget.savePanelWidgetInfo walkPanelModule.javascriptHash (pure props) stx

/-! ## The walker as a tactic block -/

/-- **A walk of the attempt or derivation `d`**: the goal of a tactic block
whose lines are motions, `ms` the motions made so far.

    example : Walk d := by
      down 0
      up

It is shown as the view after `ms` (`Cursor.view`), so the goal after each
line is the view there.  It says nothing about `d`: every `Walk d ms` holds,
by the instance below, and that is how the block's last goal is closed. -/
class Walk {S : ProofSystem} {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion := []) :
    Prop where
  /-- A walk holds, whatever its motions. -/
  intro ::

instance {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) : Walk d ms := ⟨⟩

/-- What the goal `Walk d ms` is shown as: the view after the motions `ms`
(`walkText`), or which motion cannot be made. -/
def walkGoalText [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    String :=
  match walkText d ms with
  | .ok v => v
  | .error (n, why) => s!"motion {n} cannot be made: {why}"

open PrettyPrinter Delaborator SubExpr in
/-- **A goal `Walk d ms` is shown as the view** of `d` after the motions
`ms`, under the head `Walk d`. -/
@[delab app.ProofTools.Explore.Walk]
def delabWalk : Delab := do
  let e ← getExpr
  let (``Walk, #[sys, o, j, d, ms]) := e.getAppFnArgs | failure
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then failure
  let inst ← try synthInstance (mkApp (mkConst ``Explorable) sys) catch _ => failure
  let head := match (if d.isConst then headName d else none) with
    | some n => s!"Walk {n}"
    | none => "Walk"
  shownAs head (mkApp6 (mkConst ``walkGoalText) sys inst o j d ms)

/-- **One motion, as a tactic**: the goal `Walk d ms` is closed and the goal
`Walk d (ms ++ [m])` takes its place, if the motion can be made
(`Cursor.move`, through `walkShown`).  The new goal is one that Lean closes
by the instance when the block ends, unless another motion replaces it.

On a goal that is not a walk: an error, or, with `decline`, the syntax is
declined, so that another tactic of the same name is tried. -/
def walkStep (decline : Bool) (m : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  let (``Walk, #[sys, o, j, d, ms]) := (← whnfR (← instantiateMVars (← g.getType))).getAppFnArgs
    | if decline then throwUnsupportedSyntax
      else throwErrorAt m "{m}: a motion is for a goal `Walk d`, and this goal is not one"
  let some (_, made) := ms.listLit?
    | throwError "{m}: the motions made so far are not a list written out"
  let inst ← try synthInstance (mkApp (mkConst ``Explorable) sys) catch _ =>
    throwError "{m}: there is no instance of{indentExpr (mkApp (mkConst ``Explorable) sys)}"
  let me ← Tactic.elabTermEnsuringType (← liftMacroM (motionTerm m)) (some (mkConst ``Motion))
  let ms' ← mkListLit (mkConst ``Motion) (made ++ [← instantiateMVars me])
  let goal := mkApp5 (mkConst ``Walk) sys o j d ms'
  if goal.hasMVar || goal.hasFVar then
    throwError "{m}: the attempt walked must be a closed term"
  let ((_, failed), _, _) ← evalShown
    (mkAppN (mkConst ``walkShown) #[sys, inst, o, j, d, ms', mkConst ``false, mkConst ``false])
  if let some (_, why) := failed then throwError "this motion cannot be made: {why}"
  let new ← mkFreshExprMVar goal .synthetic
  Term.registerSyntheticMVarWithCurrRef new.mvarId! (.typeClass none)
  g.assign (mkApp5 (mkConst ``Walk.intro) sys o j d ms)
  replaceMainGoal [new.mvarId!]

/-- A motion, as a line of a tactic block whose goal is `Walk d`: `up`,
`down i`, `top`, `goal k` (and `left`, `right`, which are Lean's tactics of
those names, and motions on a walk).  The goal after the line is the view
there.  Of low priority: where another tactic has the same form, that one
is read. -/
syntax (name := walkTac) (priority := low) walk_motion : tactic

@[tactic walkTac, inherit_doc walkTac] def evalWalkTac : Tactic := fun stx =>
  walkStep false stx[0]

/-- `left`, on a goal `Walk d`: the motion to the premise before this one.
On any other goal it declines, and the tactic is Lean's `left`.  On a walk
its error is the one reported (`no_fallback`). -/
@[tactic Lean.Parser.Tactic.left, no_fallback] def evalWalkLeft : Tactic := fun _ => do
  walkStep true (← `(walk_motion| left))

/-- `right`, on a goal `Walk d`: the motion to the premise after this one.
On any other goal it declines, and the tactic is Lean's `right`. -/
@[tactic Lean.Parser.Tactic.right, no_fallback] def evalWalkRight : Tactic := fun _ => do
  walkStep true (← `(walk_motion| right))

end ProofTools.Explore
