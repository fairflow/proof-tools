/-
# A declaration's statement and status, printed for a page that cites it

A tutorial or a report that displays a theorem should display what Lean
has, not a copy typed by hand, and should not call a result PROVED on
its own say-so.  These commands print both from the environment.

* `#statement f` prints the kind and signature of `f` as Lean's
  pretty-printer gives it (`ppSignature`, the form `#check` uses), then a
  status line:

      theorem GLS.completeness : Completeness
        where GLS.Completeness :=
          ∀ (s : GLS.Seq), Valid s → Nonempty (Fam s)
      PROVED · axioms: Quot.sound, propext

  When the statement is a name for a proposition (`Completeness` above, the
  convention of a campaign that writes its statements first), the name's
  definition is printed after `where`: without it the signature says
  nothing.  Set `pp.funBinderTypes` to see the type in a subtype
  `{ d' : T // p }`.  The status is OPEN when `sorryAx` is among the axioms `f` depends on,
  and PROVED otherwise; the axioms are those `#print axioms` reports
  (`collectAxioms`), sorted.  For a `def`, PROVED means only that it is
  built without `sorry`: pin a definition when the page treats it as a
  result (a construction such as a search that returns a derivation or a
  refutation), and not when it is a plain definition.  Wrapped in
  `#guard_msgs`, it fails the build when the page's copy and the library
  disagree.
* `#statement_status f` prints the status line alone, for a page that
  states `f` in its own words (a paraphrase) and cites it.
* `#statement_location f` prints the module that declares `f` and the
  lines of the declaration, for links into the source.  It is used when a
  page is written, not in its tests, so that moving a declaration does not
  break the build.

What the status does NOT check: that the statement says what the page
says it does.  That is the reader's judgment, and the reason the page
shows the signature rather than a description of it.

Core Lean only.  Written 2026-11-26 for the pinned tutorial format
(`scripts/tutorial_pins.py`).  Tests: `ProofToolsTest/Statement.lean`.
-/
import Lean

open Lean Elab Command

namespace ProofTools.Audit

/-- The word a page uses for the kind of a constant. -/
def kindWord : ConstantInfo → String
  | .thmInfo _    => "theorem"
  | .defnInfo _   => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _  => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"
  | .quotInfo _   => "quotient"

/-- PROVED or OPEN, from the axioms a declaration depends on. -/
def statusWord (axs : Array Name) : String :=
  if axs.contains ``sorryAx then "OPEN" else "PROVED"

/-- The axioms, sorted, as the status line lists them. -/
def axiomList (axs : Array Name) : String :=
  if axs.isEmpty then "none"
  else ", ".intercalate (axs.map toString |>.qsort (· < ·)).toList

/-- `#statement f`: the kind and signature of `f`, and its status. -/
elab "#statement " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let sig ← liftTermElabM <| PrettyPrinter.ppSignature n
  let axs ← collectAxioms n
  -- A statement made by name (`theorem completeness : Completeness`):
  -- show what the name says, or the signature says nothing.
  let unfolded ← match ci.type.getAppFn with
    | .const c _ =>
      match (← getEnv).find? c with
      | some (.defnInfo d) =>
        let body ← liftTermElabM <| PrettyPrinter.ppExpr d.value
        pure m!"\n  where {c} :=\n{MessageData.nest 4 (m!"    " ++ body)}"
      | _ => pure m!""
    | _ => pure m!""
  logInfo m!"{kindWord ci} {sig.fmt}{unfolded}\n{statusWord axs} · axioms: {axiomList axs}"

/-- `#statement_status f`: the status line of `#statement f` alone. -/
elab "#statement_status " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← collectAxioms n
  logInfo m!"{statusWord axs} · axioms: {axiomList axs}"

/-- `#statement_location f`: the declaring module of `f` and the first and
last lines of its declaration, separated by spaces. -/
elab "#statement_location " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let modName := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none   => env.mainModule
  match ← findDeclarationRanges? n with
  | some r => logInfo m!"{modName} {r.range.pos.line} {r.range.endPos.line}"
  | none   => throwError "no declaration range for {n}"

end ProofTools.Audit
