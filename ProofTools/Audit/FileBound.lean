/-
# A bound on the axioms of one file

`#axioms_within` (`ProofTools/Audit/Axioms.lean`) bounds one declaration.
`#axiom_sweep` (`ProofTools/Audit/Sweep.lean`) bounds every declaration of
the modules a file imports, so it has to stand in another file.  Neither
can stand in a theory file and bound that file.  This command does:

    #axioms_within_file [propext, Quot.sound]

It checks every declaration of the current file that precedes it, so it
belongs at the END of the file.  Like `#axioms_within`, it states an upper
bound: a declaration may depend on fewer axioms than the list allows, and
must depend on none outside it.  It is silent when the bound holds.

    #axioms_within_file [propext, Quot.sound] except [foo, bar]

holds the named declarations of this file out of the check.  An exception
is recorded debt, one name in a file under review; it is not a silencer for
the rest, which is still checked.  The axioms of a declaration reach
whatever uses it, so a declaration that uses `foo` needs holding out as
well, or it is reported.  A held-out declaration can carry its own, wider,
`#axioms_within`.

Four things it will not let pass in silence:

* a file with no declaration above the command is an error, never a pass
  (this is what happens if the command is put at the top);
* an exception that is not a declaration of this file is an error;
* an axiom that the file itself declares is reported unless the bound
  names it;
* generated declarations are checked like written ones.  Under a bound
  that leaves out `propext` this reports the injectivity theorem that Lean
  generates for a constructor with arguments (`S.mk.injEq`), which is
  proved with `propext`.

What it does not check: declarations that follow it, and (as with every
axiom test) that a statement says anything.

Written 2026-11-19 for `proof-tools`; it is not among the files carried in
from lax-logic-in-lean.  Core Lean only.
-/
import ProofTools.Audit.Sweep

open Lean Elab Command

namespace ProofTools.Audit

/-- The declarations of the current file so far, sorted by name: the
constants the environment holds that no imported module declared, without
Lean's own bookkeeping (`isNoise`). -/
def fileConsts (env : Environment) : Array Name :=
  (env.constants.map₂.foldl (fun acc n _ => if isNoise n then acc else acc.push n) #[]).qsort
    Name.lt

/-- `#axioms_within_file [a₁, …]`, at the end of a file: every declaration
of the file above it depends on no axiom outside the list.
`… except [d₁, …]` holds the named declarations of this file out of the
check. -/
syntax (name := axiomsWithinFileCmd)
  "#axioms_within_file " "[" ident,* "]" (" except " "[" ident,* "]")? : command

@[command_elab axiomsWithinFileCmd] def elabAxiomsWithinFile : CommandElab
  | `(#axioms_within_file [$axs,*] $[except [$exc,*]]?) => do
      let allowed ← axs.getElems.mapM resolveIdent
      let held ← match exc with
        | some e => e.getElems.mapM resolveIdent
        | none => pure #[]
      let all := fileConsts (← getEnv)
      if all.isEmpty then
        throwError "#axioms_within_file checks the declarations of this file that precede \
it, and there are none.  Put it at the end of the file."
      for h in held do
        unless all.contains h do
          throwError "'{h}' is not a declaration of this file, so it cannot be held out \
of this file's bound."
      let mut bad : Array (Name × List String) := #[]
      for n in all do
        unless held.contains n do
          let actual ← collectAxioms n
          let extra := actual.filter (fun a => !allowed.contains a)
          unless extra.isEmpty do
            bad := bad.push (n, (extra.qsort Name.lt).toList.map toString)
      unless bad.isEmpty do
        let bound := String.intercalate ", " ((allowed.qsort Name.lt).toList.map toString)
        let subject := if bad.size == 1 then "1 declaration of this file depends"
          else s!"{bad.size} declarations of this file depend"
        let mut msg := m!"{subject} on axioms outside the bound [{bound}]:"
        for (n, extra) in bad.extract 0 (min bad.size 40) do
          msg := msg ++ m!"\n  {n}  → {String.intercalate ", " extra}"
        if bad.size > 40 then
          msg := msg ++ m!"\n  … and {bad.size - 40} more"
        msg := msg ++ m!"\nLocate an entry with `#axiom_path`; hold a declaration out with \
`except [name]`."
        throwError msg
  | _ => throwUnsupportedSyntax

end ProofTools.Audit
