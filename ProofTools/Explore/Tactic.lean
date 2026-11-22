/-
# `ProofTools.Explore.Tactic`: making moves with Lean's own goals

A goal is an attempt `Att S o j` (or a derivation `Der S j`) at a closed
judgment `j`.  The open goals of the calculus are Lean's open goals, so the
infoview's goal list is the calculus's, and it follows the cursor.  A goal
is shown as its judgment, drawn by the instance's `showJudg` (`delabAtt`):
`Att S   j`, or `Der S   j` where no goal may be left open.

* `apply_move m` makes the move `m` at the first goal: it evaluates
  `S.step m j`, closes the goal with `Att.node m ps rfl …`, and puts one
  goal for each premise in its place, in order.  `apply_move m at k` makes it
  at goal `k`, numbered from 0 as in a script.  The calculus is read off the
  goal's type, so one tactic serves every instance.
* The move may be named without its namespace (`impR` for `Move.impR`), and
  a line may be a **pattern**: holes `_` or `?_` for arguments, or trailing
  arguments left out.  A pattern is matched against the instance's
  `candidates` at the goal, those that apply: one match is made (and shown
  as "Try this"), several are offered, none is an error.
* A line that does not settle its move is a **query**, and makes no move:
  `apply_move` alone offers the moves that apply, `apply_move im` those
  whose names begin with `im`.
* A move one of whose premises adds nothing to its conclusion (the
  instance's `within`) is set aside while another move matches.
* `apply_move where` is the other query: it draws the attempt so far, all
  of it, with the first goal marked `>` (`where at k`: goal `k`), as a
  message at its line.  `set_option apply_move.showWhere true` asks it
  after every move, so that each line of a script shows where the proof is
  after it, and the last line the derivation.  How the attempt is found
  again, since the tactic keeps none: see "The attempt so far" below.
* `apply_script ls` makes the lines of a script, so a stored script can be
  continued by hand; `leave_open` leaves the first goal open.
* `declare_move_tactic t for S` declares `t` as `apply_move` fixed to the
  calculus `S`: a goal of another calculus is then an error.

`Explorable`, what an instance supplies for all this, and the drawing of an
attempt as text are in `View.lean`.

**What is trusted.**  The tactic finds the premises by evaluating compiled
code, and quotes them with the instance's `ToExpr`.  The proof term it
builds is `Att.node m ps (Eq.refl _) …`, whose equation `S.step m j = .ok ps`
is proved by the kernel's own evaluation of `S.step` when the declaration
is checked.  Where the instance sets `eqByDecide`, the equation is proved
by `step_of_stepIs (Eq.refl true)` instead: the kernel evaluates `S.step`
and decides that its premises are the ones written.  Nothing the instance supplies in `Explorable` is trusted: a
wrong `candidates` or `quoteJudg` costs a failure, never a wrong
derivation.

Core Lean only.
-/
import Lean
import ProofTools.Explore.View

namespace ProofTools.Explore

open Lean Meta Elab Tactic

/-! ## What the tactic asks of an instance -/

/-- The premises of `m` at `j`, as terms. -/
def Explorable.premises (S : ProofSystem) [E : Explorable S] (m : S.Move) (j : S.Judg) :
    Except String (List Expr) :=
  (S.step m j).map (·.map E.quoteJudg.toExpr)

/-- The candidates that apply at `j`, as terms with their source text if
the instance gives one, each with whether one of its premises adds
nothing. -/
def Explorable.applicable (S : ProofSystem) [E : Explorable S] (j : S.Judg) :
    List ((Expr × Option String) × Bool) :=
  (E.candidates j).filterMap fun m =>
    match S.step m j with
    | .ok ps => some ((E.quoteMove.toExpr m, E.moveSource m), ps.any (E.within · j))
    | .error _ => none

/-- The lines of a script, their moves as terms. -/
def Explorable.quoteScript (S : ProofSystem) [E : Explorable S] (ls : Script S) :
    List (Nat × Expr) :=
  ls.map fun l => (l.goal, E.quoteMove.toExpr l.move)

/-! ## Evaluating -/

private def exprTy : Expr := mkConst ``Lean.Expr
private def listTy (α : Expr) : Expr := mkApp (mkConst ``List [0]) α
private def prodTy (α β : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) α β

/-- See `evalPremises`. -/
unsafe def evalPremisesU (e : Expr) : MetaM (Except String (List Expr)) :=
  evalExpr (Except String (List Expr))
    (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (listTy exprTy)) e
/-- Evaluate a closed term of type `Except String (List Expr)`. -/
@[implemented_by evalPremisesU]
opaque evalPremises (e : Expr) : MetaM (Except String (List Expr))

/-- A move the instance proposes: its term, and its source text if the
instance gives one. -/
abbrev Cand : Type := Expr × Option String

/-- See `evalApplicable`. -/
unsafe def evalApplicableU (e : Expr) : MetaM (List (Cand × Bool)) :=
  evalExpr (List (Cand × Bool))
    (listTy (prodTy (prodTy exprTy (mkApp (mkConst ``Option [0]) (mkConst ``String)))
      (mkConst ``Bool))) e
/-- Evaluate a closed term of type `List ((Expr × Option String) × Bool)`. -/
@[implemented_by evalApplicableU] opaque evalApplicable (e : Expr) : MetaM (List (Cand × Bool))

/-- See `evalBool`. -/
unsafe def evalBoolU (e : Expr) : MetaM Bool := evalExpr Bool (mkConst ``Bool) e
/-- Evaluate a closed term of type `Bool`. -/
@[implemented_by evalBoolU] opaque evalBool (e : Expr) : MetaM Bool

/-- See `evalScript`. -/
unsafe def evalScriptU (e : Expr) : MetaM (List (Nat × Expr)) :=
  evalExpr (List (Nat × Expr)) (listTy (prodTy (mkConst ``Nat) exprTy)) e
/-- Evaluate a closed term of type `List (Nat × Expr)`. -/
@[implemented_by evalScriptU] opaque evalScript (e : Expr) : MetaM (List (Nat × Expr))

/-- See `evalString`. -/
unsafe def evalStringU (e : Expr) : MetaM String := evalExpr String (mkConst ``String) e
/-- Evaluate a closed term of type `String`: a judgment or a view, drawn by
the instance's printers. -/
@[implemented_by evalStringU] opaque evalString (e : Expr) : MetaM String

/-! ## Goals -/

/-- A goal `Att S o j`, taken apart. -/
structure GoalInfo where
  /-- The calculus. -/
  sys : Expr
  /-- Whether open goals are allowed. -/
  o : Expr
  /-- The judgment, a closed term. -/
  j : Expr
  /-- The instance of `Explorable`. -/
  inst : Expr
  /-- `S.Judg`. -/
  judgTy : Expr
  /-- `S.Move`. -/
  moveTy : Expr

/-- Take a goal apart; `tac` is the tactic's name, for messages. -/
def goalInfo (tac : String) (g : MVarId) : MetaM GoalInfo := do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  match ty.getAppFnArgs with
  | (``Att, #[sys, o, j]) =>
    let j ← instantiateMVars j
    if j.hasFVar || j.hasMVar then
      throwError "{tac}: the goal's judgment is not a closed term"
    let instTy := mkApp (mkConst ``Explorable) sys
    let inst ← try synthInstance instTy catch _ =>
      throwError "{tac}: there is no instance of{indentExpr instTy}"
    let inst ← instantiateMVars inst
    if inst.hasFVar || inst.hasMVar || sys.hasFVar || sys.hasMVar then
      throwError "{tac}: the calculus and its instance of `Explorable` must be closed terms         (declare the instance; a local hypothesis will not do)"
    return { sys, o, j, inst
             judgTy := mkApp (mkConst ``ProofSystem.Judg) sys
             moveTy := mkApp (mkConst ``ProofSystem.Move) sys }
  | _ => throwError "{tac}: the goal is not an attempt `Att S o j` or a derivation `Der S j`"

/-- **Make a move** at the goal `g`, which is goal number `k`: evaluate the
premises, close the goal with the node, and return the premises as new
goals, in order. -/
def applyMoveAt (tac : String) (g : MVarId) (m : Expr) (k : Nat) : MetaM (List MVarId) :=
  g.withContext do
    let gi ← goalInfo tac g
    match ← evalPremises (mkApp4 (mkConst ``Explorable.premises) gi.sys gi.inst m gi.j) with
    | .error e => throwError "the move does not apply to goal {k}: {e}"
    | .ok ps =>
      let tag ← g.getTag
      let mut gs : Array MVarId := #[]
      let mut psE := mkApp (mkConst ``List.nil [0]) gi.judgTy
      let mut dsE := mkApp2 (mkConst ``Atts.nil) gi.sys gi.o
      for p in ps.reverse do
        let ng ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Att) gi.sys gi.o p) tag
        dsE := mkApp6 (mkConst ``Atts.cons) gi.sys gi.o p psE ng dsE
        psE := mkApp3 (mkConst ``List.cons [0]) gi.judgTy p psE
        gs := gs.push ng.mvarId!
      let h ←
        if ← evalBool (mkApp2 (mkConst ``Explorable.eqByDecide) gi.sys gi.inst) then
          -- `step_of_stepIs (Eq.refl true)`: the kernel evaluates `stepIs`
          let decTy ← mkAppM ``DecidableEq #[gi.judgTy]
          let dec ← try synthInstance decTy catch _ =>
            throwError "{tac}: the instance asks for the equation of a node to be decided \
              (`eqByDecide`), and there is no instance of{indentExpr decTy}"
          pure <| mkApp6 (mkConst ``step_of_stepIs) gi.sys dec m gi.j psE
            (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
        else
          let excTy := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (listTy gi.judgTy)
          let okE := mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``String) (listTy gi.judgTy) psE
          pure <| mkApp2 (mkConst ``Eq.refl [1]) excTy okE
      g.assign (mkApp7 (mkConst ``Att.node) gi.sys gi.o gi.j m psE h dsE)
      return gs.toList.reverse

/-- The goal `k` of `gs`, or why there is none. -/
def goalAt (tac : String) (gs : List MVarId) (k : Nat) : MetaM MVarId := do
  if gs.isEmpty then throwError "{tac}: there are no goals"
  let some g := gs[k]? | throwError "there is no goal {k}: the open goals are 0 to {gs.length - 1}"
  return g

/-- The text a goal is shown as: `head`, then the text of the term `text`
(closed, of type `String`) evaluated, beside the head if it is one line and
below it if it is more.  Lean prints the text as it stands. -/
def shownAs (head : String) (text : Expr) : PrettyPrinter.Delaborator.Delab := do
  let t ← try evalString text catch _ => failure
  let sep := if t.contains '\n' then "\n" else "   "
  return ⟨Syntax.node .none strLitKind #[Syntax.atom .none (head ++ sep ++ t)]⟩

/-- A name as a goal's head shows it: a constant by the last part of its
name. -/
def headName? (e : Expr) : Option String :=
  match e.constName? with
  | some (.str _ s) => some s
  | _ => none

open PrettyPrinter Delaborator SubExpr in
/-- **A goal `Att S o j` is shown as its judgment**, drawn by the instance's
`showJudg`: `Att S   j` where open goals are allowed, `Der S   j` where they
are not, the judgment below the head if it is drawn on several lines.  For a
calculus named by a constant, with an instance of `Explorable`, and a closed
judgment; any other is printed by Lean. -/
@[delab app.ProofTools.Explore.Att]
def delabAtt : Delab := do
  let e ← getExpr
  let (``Att, #[sys, o, j]) := e.getAppFnArgs | failure
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then failure
  let some name := headName? sys | failure
  let kind ← if o.isConstOf ``Bool.true then pure "Att " else
    if o.isConstOf ``Bool.false then pure "Der " else failure
  let inst ← try synthInstance (mkApp (mkConst ``Explorable) sys) catch _ => failure
  shownAs (kind ++ name) (mkApp3 (mkConst ``Explorable.showJudg) sys inst j)

/-! ## The attempt so far

`apply_move` keeps no state.  The attempt so far is the value, assigned in
part, of the metavariable the proof began with, and Lean does not hand a
tactic that metavariable.  It is found again in the metavariable context,
from a goal: among the metavariables that are assigned and whose value, with
every assignment put in, still mentions the goal, those of type `Att S o j`
are the attempts the goal is part of, and the one made first holds the
others.  (Going up from the goal through the assignments as they are stored
does not find it: Lean rewrites an assignment when it puts the later ones
in, and the chain is then broken.)

The value is read as a closed term of type `Att S true j`: `o` is set to
`true` at each node, each open goal becomes `Att.goal`, and a part that was
not built by moves (a constant given with `exact`, say) is taken through
`Att.toAtt`.  That term is drawn by evaluating `Att.whereText` on it. -/

/-- The metavariables that hold an attempt which the goal `g` is part of,
the first made first; then `g`. -/
def attemptsAround (g : MVarId) : MetaM (List MVarId) := do
  let mctx ← getMCtx
  let mut found : Array (Nat × MVarId) := #[]
  for (m, _) in mctx.eAssignment do
    let some decl := mctx.findDecl? m | continue
    if ((← instantiateMVars (.mvar m)).findMVar? (· == g)).isSome then
      if (← whnfR (← instantiateMVars decl.type)).isAppOf ``Att then
        found := found.push (decl.index, m)
  return (found.qsort (·.1 < ·.1)).toList.map (·.2) ++ [g]

mutual
/-- Read a term of type `Att S o j`, its metavariables put in, as a closed
term of type `Att S true j`; the open goals met are kept, in order. -/
partial def readAtt (e : Expr) : StateT (Array MVarId) MetaM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Att.node, #[s, _, j, m, ps, h, ds]) =>
    return mkApp7 (mkConst ``Att.node) s (mkConst ``Bool.true) j m ps h (← readAtts ds)
  | _ =>
    if let .mvar g := e then
      match (← whnfR (← instantiateMVars (← g.getType))).getAppFnArgs with
      | (``Att, #[s, _, j]) =>
        modify (·.push g)
        return mkApp2 (mkConst ``Att.goal) s j
      | _ => throwError "not an attempt:{indentExpr e}"
    else if e.hasMVar || e.hasFVar then
      throwError "a part of it is not built by moves, and is not a closed term:{indentExpr e}"
    else
      match (← whnfR (← inferType e)).getAppFnArgs with
      | (``Att, #[s, o, j]) => return mkApp4 (mkConst ``Att.toAtt) s o j e
      | _ => throwError "not an attempt:{indentExpr e}"
/-- `readAtt` on the premises of a node. -/
partial def readAtts (e : Expr) : StateT (Array MVarId) MetaM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Atts.cons, #[s, _, p, ps, d, ds]) =>
    let d ← readAtt d
    return mkApp6 (mkConst ``Atts.cons) s (mkConst ``Bool.true) p ps d (← readAtts ds)
  | (``Atts.nil, #[s, _]) => return mkApp2 (mkConst ``Atts.nil) s (mkConst ``Bool.true)
  | _ =>
    if e.hasMVar || e.hasFVar then
      throwError "a part of it is not built by moves, and is not a closed term:{indentExpr e}"
    else
      match (← whnfR (← inferType e)).getAppFnArgs with
      | (``Atts, #[s, o, ps]) => return mkApp4 (mkConst ``Atts.toAtts) s o ps e
      | _ => throwError "not the premises of a node:{indentExpr e}"
end

/-- **Show where a goal is**: the attempt so far drawn in full, the goal
`cur` marked (`Att.whereText`), as a message at `ref`.  `roots` are the
metavariables that may hold the attempt, the widest first
(`attemptsAround`): the first that can be read is drawn.  With no `cur`, or
one that is not in the attempt, the root is marked. -/
def showWhere (ref : Syntax) (gi : GoalInfo) (roots : List MVarId) (cur : Option MVarId) :
    MetaM Unit := do
  let mut why : MessageData := .nil
  let mut skipped := false
  for r in roots do
    try
      let (``Att, #[_, _, j]) := (← whnfR (← instantiateMVars (← r.getType))).getAppFnArgs
        | throwError "not an attempt"
      let (d, gs) ← (readAtt (← instantiateMVars (.mvar r))).run #[]
      let k : Option Nat := cur.bind (gs.idxOf? ·)
      let text ← evalString (mkApp5 (mkConst ``Att.whereText) gi.sys gi.inst j d (toExpr k))
      let note := if skipped then
        "\n  (an attempt around this one is not drawn: a part of it is not built by moves)" else ""
      logInfoAt ref (text ++ note)
      return
    catch e =>
      why := why ++ m!"\n{e.toMessageData}"
      skipped := true
  throwError "the attempt so far cannot be drawn:{why}"

/-! ## Lines -/

/-- `apply_move.tryThis`: show the line a pattern was filled to. -/
register_option apply_move.tryThis : Bool := {
  defValue := true
  descr := "apply_move shows the line it made from a pattern as a `Try this` suggestion"
}

/-- `apply_move.showWhere`: show where the proof is after each move. -/
register_option apply_move.showWhere : Bool := {
  defValue := false
  descr := "apply_move shows the attempt so far after each move it makes, with the goal the \
    next line acts on marked, as `apply_move where` does"
}

/-- The query that draws the attempt so far, in the place of a move. -/
syntax whereQuery := "where"

/-- The move and the goal number of a line: `m`, `m at k`, or nothing; or
`where`, `where at k`. -/
syntax applyMoveArgs := (ppSpace colGt (whereQuery <|> term))? (" at " num)?

/-- Drop the parentheses around a term. -/
partial def unparen (stx : Syntax) : Syntax :=
  if stx.getKind == ``Lean.Parser.Term.paren then unparen stx[1] else stx

/-- The head and the arguments of a line. -/
def headArgs (line : Syntax) : Syntax × Array Syntax :=
  let l := unparen line
  if l.getKind == ``Lean.Parser.Term.app then (l[0], l[1].getArgs) else (l, #[])

/-- The text of a head that may name a move: `x`, `.x`, or `N.x`. -/
def headText (f : Syntax) : Option String :=
  if f.getKind == ``Lean.Parser.Term.dotIdent then
    match f[1].getId with
    | .str .anonymous s => some s
    | _ => none
  else if f.isIdent then
    match f.getId with
    | .str _ s => some s
    | _ => none
  else none

/-- The inductive type of the moves and its constructors, if `S.Move` is
one. -/
def moveCtors (moveTy : Expr) : MetaM (Option (Name × List Name)) := do
  let ty ← whnf moveTy
  let some n := ty.getAppFn.constName? | return none
  match (← getEnv).find? n with
  | some (.inductInfo info) => return some (n, info.ctors)
  | _ => return none

/-- Run `k` with the namespace `ns` open. -/
def withOpen {α : Type} (ns : Option Name) (k : TacticM α) : TacticM α :=
  match ns with
  | some ns =>
    withTheReader Core.Context
      (fun c => { c with openDecls := OpenDecl.simple ns [] :: c.openDecls }) k
  | none => k

/-- Elaborate a line as a move; holes stay as metavariables.  Errors are
thrown, not logged, so that they outlive a restored state. -/
def elabMove (tac : String) (stx : Syntax) (moveTy : Expr) (ns : Option Name) : TacticM Expr :=
  withOpen ns do
    let e ← Tactic.runTermElab <| Term.withoutErrToSorry do
      let e ← Term.elabTermEnsuringType stx (some moveTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasSyntheticSorry then throwAbortTactic
    if e.hasFVar then throwError "{tac}: the move is not a closed term"
    return e

/-- Does the identifier `f` name a move, or a function into the moves? -/
def namesMove (f : Syntax) (moveTy : Expr) (ns : Option Name) : TacticM Bool :=
  withOpen ns do
    let saved ← saveState
    try
      let ok ← Tactic.runTermElab <| Term.withoutErrToSorry do
        let e ← Term.elabTerm f none
        let (_, _, ty) ← forallMetaTelescope (← inferType e)
        isDefEq ty moveTy
      pure ok
    catch _ => pure false
    finally saved.restore (restoreInfo := true)

/-- A move as source text: the instance's, or Lean's printing of the term
with the namespace of the moves open. -/
def moveText (m : Cand) (ns : Option Name) : TacticM String :=
  match m.2 with
  | some src => pure src
  | none => withOpen ns do
    let stx ← PrettyPrinter.delab m.1
    return (← PrettyPrinter.ppTerm stx).pretty 100

/-- Is there a hole (`_`, `?_`, `?x`) in the term? -/
def hasHole (stx : Syntax) : Bool :=
  (stx.find? fun s =>
    s.isOfKind ``Lean.Parser.Term.hole || s.isOfKind ``Lean.Parser.Term.syntheticHole).isSome

/-- A piece of syntax as its source text. -/
def srcText (stx : Syntax) : Option String :=
  stx.reprint.map fun s => s.trimAscii.toString

/-- **A line as it was typed, with its holes filled.**  `f` and `args` are
the head and the arguments typed, `full` the source text of the move made.
An argument typed without a hole is kept as typed; a hole, an argument with
a hole in it, and an argument left out take the move's.  Where the typed
line and the move's text do not line up, the answer is the move's text. -/
def filledText (f : Syntax) (args : Array Syntax) (full : String) : CoreM String := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term full | return full
  let (_, vals) := headArgs stx
  if vals.size < args.size then return full
  let some h := srcText f | return full
  let mut out := h
  for i in [0:vals.size] do
    let typed? := match args[i]? with
      | some a => if hasHole a then none else srcText a
      | none => none
    let some t := typed? <|> srcText vals[i]! | return full
    out := out ++ " " ++ t
  return out

/-- The line `tac m`, at goal `k` if it is not the first. -/
def lineText (tac : String) (m : String) (k : Nat) : String :=
  if k == 0 then s!"{tac} {m}" else s!"{tac} {m} at {k}"

/-- The most lines offered at once. -/
def maxOffered : Nat := 40

/-- **Offer** lines as suggestions at `ref`; no move is made. -/
def offer (ref : Syntax) (header : String) (lines : Array String) : TacticM Unit := do
  let sugg : Array Lean.Meta.Tactic.TryThis.Suggestion :=
    (lines.toList.take maxOffered).toArray.map fun l => { suggestion := .string l }
  let footer := if lines.size > maxOffered then s!"\n… and {lines.size - maxOffered} more" else ""
  Lean.Meta.Tactic.TryThis.addSuggestions ref sugg (header := header) (footer := footer)

/-- Set aside the moves that add nothing, while another is there. -/
def setAside (ms : List (Cand × Bool)) : List Cand :=
  let good := ms.filter (!·.2)
  (if good.isEmpty then ms else good).map (·.1)

/-- "`n` moves apply". -/
def movesApply (n : Nat) (h : Option String) : String :=
  match h, n with
  | none, 1 => "1 move applies"
  | none, n => s!"{n} moves apply"
  | some h, 1 => s!"1 move whose name begins with `{h}` applies"
  | some h, n => s!"{n} moves whose names begin with `{h}` apply"

/-- The name of the constructor at the head of a move. -/
def headName (m : Expr) : Option String :=
  match m.getAppFn.constName? with
  | some (.str _ s) => some s
  | _ => none

/-- **The body of `apply_move`**: `tac` is the tactic's name, `sys?` the
calculus it is fixed to, if any. -/
def applyMoveCore (tac : String) (sys? : Option Name) (ref : Syntax) (line? : Option Syntax)
    (k : Nat) : TacticM Unit := do
  let gs ← getGoals
  let g ← goalAt tac gs k
  let gi ← g.withContext (goalInfo tac g)
  if let some s := sys? then
    unless ← g.withContext (isDefEq gi.sys (mkConst s)) do
      throwError "{tac}: the goal is not an attempt in `{s}`"
  -- the query `where`: no move is made
  if line?.any (·.isOfKind ``whereQuery) then
    showWhere ref gi (← attemptsAround g) (some g)
    return
  let ctors ← moveCtors gi.moveTy
  let ns := ctors.map (·.1)
  let applicable : TacticM (List (Cand × Bool)) :=
    evalApplicable (mkApp3 (mkConst ``Explorable.applicable) gi.sys gi.inst gi.j)
  let make (m : Expr) : TacticM Unit := do
    -- the attempt is found from `g` while `g` is still open
    let roots ← if apply_move.showWhere.get (← getOptions) then attemptsAround g else pure []
    let new ← applyMoveAt tac g m k
    let gs' := gs.take k ++ new ++ gs.drop (k + 1)
    setGoals gs'
    unless roots.isEmpty do
      try showWhere ref gi roots (gs'[k]? <|> gs'.head?)
      catch e => logInfoAt ref m!"{tac}: {e.toMessageData}"
  let offerAll (ms : List Cand) (h : Option String) : TacticM Unit := do
    let whose := match h with | some h => s!" whose name begins with `{h}`" | none => ""
    if ms.isEmpty then throwError "{tac}: no move{whose} applies at goal {k}"
    let lines ← ms.toArray.mapM fun m => do return lineText tac (← moveText m ns) k
    offer ref s!"{tac}: at goal {k}, {movesApply ms.length h}; no move is made. Try these:" lines
  -- a pattern: match it against the candidates that apply
  let matchPattern (stx : Syntax) : TacticM (Option Expr × List Cand) := do
    let saved ← saveState
    let r ← try
      g.withContext do
        let pat ← elabMove tac stx gi.moveTy ns
        if !pat.hasMVar then pure (some pat, [])
        else
          let ms ← (← applicable).filterM fun (c, _) =>
            withoutModifyingState <| withAssignableSyntheticOpaque <| isDefEq pat c.1
          pure (none, setAside ms)
      catch e =>
        saved.restore (restoreInfo := true)
        throw e
    if r.1.isNone then saved.restore (restoreInfo := true)
    return r
  -- the line a pattern is filled to: what was typed, with its holes filled
  let filled (typed : Option (Syntax × Array Syntax)) (m : Cand) : TacticM String := do
    let full ← moveText m ns
    match typed with
    | some (f, args) => return lineText tac (← filledText f args full) k
    | none => return lineText tac full k
  let usePattern (stx : Syntax) (typed : Option (Syntax × Array Syntax)) : TacticM Unit := do
    match ← matchPattern stx with
    | (some m, _) => make m
    | (none, []) =>
      throwError "{tac}: no candidate move of this form applies at goal {k}; write its \
        arguments out, or `{tac}` alone to see the moves that apply"
    | (none, [m]) =>
      if apply_move.tryThis.get (← getOptions) then
        Lean.Meta.Tactic.TryThis.addSuggestion ref { suggestion := .string (← filled typed m) }
      make m.1
    | (none, ms) =>
      let lines ← ms.toArray.mapM (filled typed)
      offer ref s!"{tac}: {ms.length} moves of this form apply at goal {k}; no move is made. \
        Try these:" lines
  match line? with
  | none => offerAll (setAside (← applicable)) none
  | some line =>
    let (f, args) := headArgs line
    match headText f, ctors with
    | some txt, some (_, cs) =>
      if let some c := cs.find? (fun c => c.getString! == txt) then
        -- a move's name: the arguments left out are holes
        let arity := (← getConstInfoCtor c).numFields
        let mut as := args
        for _ in [args.size:arity] do as := as.push (← `(_))
        let head := mkIdentFrom f (`_root_ ++ c)
        let stx : Syntax := if as.isEmpty then head else Syntax.mkApp ⟨head⟩ (as.map (⟨·⟩))
        usePattern stx (some (f, args))
      else
        let withPrefix := cs.filter fun c => c.getString!.startsWith txt
        if withPrefix.isEmpty || (← g.withContext (namesMove f gi.moveTy ns)) then
          usePattern line (some (f, args))
        else
          -- the start of a name: a query
          let names := withPrefix.map (·.getString!)
          let ms := (← applicable).filter fun (m, _) => (headName m.1).any (names.contains ·)
          offerAll (setAside ms) (some txt)
    | _, _ => usePattern line none

/-- The goal number of a line. -/
def goalNum (k? : Option Syntax) : Nat :=
  match k? with
  | some k => k.isNatLit?.getD 0
  | none => 0

/-- Read `applyMoveArgs`: the move, if any, and the goal number. -/
def readArgs (a : Syntax) : Option Syntax × Nat :=
  let line? := if a[0].getNumArgs == 0 then none else some a[0][0]
  let k := if a[1].getNumArgs == 0 then 0 else (a[1][1].isNatLit?).getD 0
  (line?, k)

/-- `apply_move m` makes the move `m` of the goal's calculus at the first
goal, and `apply_move m at k` at goal `k`: the goal is closed by the node of
the move, and the move's premises take its place, in order.  So the lines
of a proof by `apply_move` are the lines of a script.

The move may be written without its namespace; arguments may be holes `_`
or `?_`, and trailing ones may be left out: the line is then matched against
the moves the instance proposes, and the line it is filled to keeps the
arguments as they were typed.  A line that does not settle its move makes
none, and offers what it could be: `apply_move` alone offers the moves that
apply, `apply_move im` those whose names begin with `im`. -/
syntax (name := applyMoveTac) "apply_move" applyMoveArgs : tactic

@[tactic applyMoveTac] def evalApplyMove : Tactic := fun stx => do
  let (line?, k) := readArgs stx[1]
  applyMoveCore "apply_move" none stx line? k

/-- `apply_script ls` makes the lines of the script `ls` (a closed term of
type `Script S`, for the calculus `S` of the first goal), in order. -/
syntax (name := applyScriptTac) "apply_script " term : tactic

@[tactic applyScriptTac] def evalApplyScript : Tactic := fun stx => do
  let g ← getMainGoal
  let gi ← g.withContext (goalInfo "apply_script" g)
  let ls ← g.withContext do
    let e ← Tactic.elabTermEnsuringType stx[1] (some (mkApp (mkConst ``Script) gi.sys))
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then throwAbortTactic
    if e.hasFVar || e.hasMVar then throwError "apply_script: the script is not a closed term"
    evalScript (mkApp3 (mkConst ``Explorable.quoteScript) gi.sys gi.inst e)
  let mut n : Nat := 0
  for (k, m) in ls do
    let gs ← getGoals
    let g ← try goalAt "apply_script" gs k catch e =>
      throwError "apply_script: line {n}: {e.toMessageData}"
    let new ← try applyMoveAt "apply_script" g m k catch e =>
      throwError "apply_script: line {n}: {e.toMessageData}"
    setGoals (gs.take k ++ new ++ gs.drop (k + 1))
    n := n + 1

/-- `leave_open` leaves the first goal of an attempt open: it closes it
with `Att.goal`. -/
syntax (name := leaveOpenTac) "leave_open" : tactic

@[tactic leaveOpenTac] def evalLeaveOpen : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    match ty.getAppFnArgs with
    | (``Att, #[sys, o, j]) =>
      unless ← isDefEq o (mkConst ``Bool.true) do
        throwError "leave_open: the goal is a derivation, which has no open goals"
      g.assign (mkApp2 (mkConst ``Att.goal) sys j)
      replaceMainGoal []
    | _ => throwError "leave_open: the goal is not an attempt `Att S true j`"

/-- `declare_move_tactic t for S` declares the tactic `t` as `apply_move`
fixed to the calculus `S`: `t m`, `t m at k`, `t`.  A goal of another
calculus is an error. -/
syntax "declare_move_tactic " ident " for " ident : command

set_option hygiene false in
macro_rules
  | `(declare_move_tactic $t for $s) => do
    let tok := Syntax.mkStrLit t.getId.toString
    let name := Syntax.mkStrLit t.getId.toString
    `(elab (name := $(mkIdent (t.getId ++ `moveTactic))) tk:$tok:str
          a:ProofTools.Explore.applyMoveArgs : tactic => do
        let (line?, k) := ProofTools.Explore.readArgs a
        ProofTools.Explore.applyMoveCore $name (some ``$s) tk line? k)

end ProofTools.Explore
