/-
`#axioms_within_file` checks the declarations Lean generates like the ones
that are written.  A structure is enough to show it: the injectivity theorem
of its constructor is proved with `propext`.
-/
import ProofTools.Audit.FileBound

namespace ProofToolsTest.FileBoundGenerated

structure Pair where
  fst : Nat
  snd : Nat

/--
error: 1 declaration of this file depends on axioms outside the bound []:
  ProofToolsTest.FileBoundGenerated.Pair.mk.injEq  → propext
Locate an entry with `#axiom_path`; hold a declaration out with `except [name]`.
-/
#guard_msgs in
#axioms_within_file []

#guard_msgs in
#axioms_within_file [propext]

#guard_msgs in
#axioms_within_file [] except [Pair.mk.injEq]

end ProofToolsTest.FileBoundGenerated
