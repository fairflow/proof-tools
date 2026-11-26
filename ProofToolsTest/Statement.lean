/-
Tests of `#statement` and `#statement_location`
(`ProofTools/Audit/Statement.lean`): a theorem, a definition, a theorem
that uses `Classical.choice`, one that uses `sorry` (OPEN), a library
theorem, a statement made by name, the status alone, and a location.  Every message is pasted from Lean's output.
-/
import ProofTools.Audit.Statement

namespace ProofToolsTest.Statement

theorem two_add (n : Nat) : 2 + n = n + 2 := Nat.add_comm 2 n

def double (n : Nat) : Nat := n + n

theorem classical_em (p : Prop) : p ∨ ¬p := Classical.em p

#guard_msgs (drop warning) in
theorem not_yet (n : Nat) : n * 0 = 1 := sorry

/--
info: theorem ProofToolsTest.Statement.two_add (n : Nat) : 2 + n = n + 2
PROVED · axioms: none
-/
#guard_msgs in #statement two_add

/--
info: def ProofToolsTest.Statement.double (n : Nat) : Nat
PROVED · axioms: none
-/
#guard_msgs in #statement double

/--
info: theorem ProofToolsTest.Statement.classical_em (p : Prop) : p ∨ ¬p
PROVED · axioms: Classical.choice, Quot.sound, propext
-/
#guard_msgs in #statement classical_em

/--
info: theorem ProofToolsTest.Statement.not_yet (n : Nat) : n * 0 = 1
OPEN · axioms: sorryAx
-/
#guard_msgs in #statement not_yet

/--
info: theorem Nat.add_comm (n m : Nat) : n + m = m + n
PROVED · axioms: none
-/
#guard_msgs in #statement Nat.add_comm

/-- A statement made by name, as a campaign writes its statements first. -/
def TwoAdd : Prop := ∀ n : Nat, 2 + n = n + 2

theorem two_add' : TwoAdd := fun n => Nat.add_comm 2 n

/--
info: theorem ProofToolsTest.Statement.two_add' : TwoAdd
  where ProofToolsTest.Statement.TwoAdd :=
    ∀ (n : Nat), 2 + n = n + 2
PROVED · axioms: none
-/
#guard_msgs in #statement two_add'

/-- info: OPEN · axioms: sorryAx -/
#guard_msgs in #statement_status not_yet

/-- info: ProofToolsTest.Statement 11 11 -/
#guard_msgs in #statement_location two_add

end ProofToolsTest.Statement
