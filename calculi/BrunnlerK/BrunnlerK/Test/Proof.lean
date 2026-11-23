/-
Tests of system K as a proof system, and of the tactic `kmove`: the nine
kinds of `reference/explore.md` §10 of the skill.  Every message is pinned.

The reference derivations of the exercises (`Play/BrunnlerK.lean`) are
here, and not in that file.
-/
import BrunnlerK.Tactic
import BrunnlerK.Test.System
import LeanCertify

namespace BrunnlerK.Test

open ProofTools ProofTools.Explore BrunnlerK

/-! Each message below is pasted from Lean's output after reading it.  The
atoms `p q a b c d` are those of `BrunnlerK/Test/Sequent.lean`, under the
names the suggested lines write.

The printer writes a negated proposition as its letter followed by the
combining macron U+0304.  In this file every barred letter is spelt that
way, also in comments: `#guard_msgs` compares character by character, and
an editor that composes `a` and the macron into one character breaks the
comparison. -/

/-! ## 0. Typing a sequent -/

example : seq[◇(∼a ⋏ ∼b), □a, ◇b] = mk [◇(∼a ⋏ ∼b), □a, ◇b] [] := rfl
-- Formulas and boxes may be mixed; the formulas keep their order, and the
-- boxes theirs.
example : seq[a, [b, [c]], d, []] = mk [a, d] [mk [b] [mk [c] []], mk [] []] := rfl
example : seq[] = NSeq.leaf [] := rfl
#guard (seq[a, [b, [c]], d, []]).show == "a, d, [b, [c]], [∅]"

/-! ## 1. Each rule, where it applies and where it does not -/

-- the axiom: at the root, in a box, and not across nodes
#guard (S.step (.ax [] 0) seq[p, ∼p, q]).toOption == some []
#guard (S.step (.ax [0] 0) seq[q, [∼p, p]]).toOption == some []
#guard (S.step (.ax [] 0) seq[p, [∼p]]).toOption.isNone
#guard (S.step (.ax [0] 0) seq[p, [∼p]]).toOption.isNone

-- `∧`: two premises, `A` and `B` in place of `A ∧ B`, in front
#guard (S.step (.and [] a b) seq[c, a ⋏ b]).toOption == some [seq[a, c], seq[b, c]]
#guard (S.step (.and [0] a b) seq[c, [d, a ⋏ b]]).toOption
  == some [seq[c, [a, d]], seq[c, [b, d]]]
#guard (S.step (.and [] a b) seq[c, a ⋎ b]).toOption.isNone

-- `∨`: one premise, `A, B` in place of `A ∨ B`
#guard (S.step (.or [] a b) seq[c, a ⋎ b]).toOption == some [seq[a, b, c]]
#guard (S.step (.or [] a b) seq[c, [a ⋎ b]]).toOption.isNone

-- `□`: a new box `[A]` in place of `□A`, after the boxes that are there
#guard (S.step (.box [] a) seq[□a, c, [d]]).toOption == some [seq[c, [d], [a]]]
#guard (S.step (.box [0, 0] a) seq[[[□a]]]).toOption == some [seq[[[[a]]]]]
#guard (S.step (.box [] a) seq[◇a, c]).toOption.isNone

-- `◇k_c`: `A` put into the box named; `◇A` stays
#guard (S.step (.dia [] 1 a) seq[◇a, [b], [c]]).toOption == some [seq[◇a, [b], [a, c]]]
#guard (S.step (.dia [0] 0 a) seq[[◇a, [b]]]).toOption == some [seq[[◇a, [a, b]]]]
#guard (S.step (.dia [] 2 a) seq[◇a, [b], [c]]).toOption.isNone
#guard (S.step (.dia [] 0 a) seq[□a, [b]]).toOption.isNone
-- a diamond does not reach a box two levels down
#guard (S.step (.dia [] 0 a) seq[◇a, [[b]]]).toOption == some [seq[◇a, [a, [b]]]]

-- One step of each move reduces in the kernel.
example : (S.step (.ax [0] 0) seq[q, [∼p, p]]).toOption = some [] := by decide +kernel
example : (S.step (.and [0] a b) seq[c, [d, a ⋏ b]]).toOption
    = some [seq[c, [a, d]], seq[c, [b, d]]] := by decide +kernel
example : (S.step (.or [] a b) seq[c, a ⋎ b]).toOption = some [seq[a, b, c]] := by
  decide +kernel
example : (S.step (.box [] a) seq[□a, c, [d]]).toOption = some [seq[c, [d], [a]]] := by
  decide +kernel
example : (S.step (.dia [] 1 a) seq[◇a, [b], [c]]).toOption = some [seq[◇a, [b], [a, c]]] := by
  decide +kernel

/-! ## 2. The source's derivation, and the four further exercises -/

/-- **Example 2.3** (pp. 9–10), from the sequent `◇(ā ∧ b̄), □a, ◇b`. -/
def ex23Der : Der S seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  kmove box [] a
  kmove dia [] 0 (∼a ⋏ ∼b)
  kmove and [0] (∼a) (∼b)
  kmove ax [0] 4
  kmove dia [] 0 b
  kmove ax [0] 5

/-- Example 2.3 from its formula `□(a ∨ b) ⊃ (□a ∨ ◇b)`: `∨` twice first. -/
def ex23FormDer : Der S seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)] := by
  kmove or [] ◇(∼a ⋏ ∼b) (□a ⋎ ◇b)
  kmove or [] □a ◇b
  kmove box [] a
  kmove dia [] 0 (∼a ⋏ ∼b)
  kmove and [0] (∼a) (∼b)
  kmove ax [0] 4
  kmove dia [] 0 b
  kmove ax [0] 5

/-- `□(a ∧ b) ⊃ (□a ∧ □b)`.  (The choice of exercise is ours.) -/
def boxAndDer : Der S seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] := by
  kmove or [] ◇(∼a ⋎ ∼b) (□a ⋏ □b)
  kmove and [] □a □b
  kmove box [] a
  kmove dia [] 0 (∼a ⋎ ∼b)
  kmove or [0] (∼a) (∼b)
  kmove ax [0] 4
  kmove box [] b
  kmove dia [] 0 (∼a ⋎ ∼b)
  kmove or [0] (∼a) (∼b)
  kmove ax [0] 5

/-- `(□a ∧ □b) ⊃ □(a ∧ b)`.  (Ours.) -/
def andBoxDer : Der S seq[(□a ⋏ □b) ⊃ □(a ⋏ b)] := by
  kmove or [] (◇∼a ⋎ ◇∼b) □(a ⋏ b)
  kmove or [] ◇∼a ◇∼b
  kmove box [] (a ⋏ b)
  kmove and [0] a b
  kmove dia [] 0 (∼a)
  kmove ax [0] 4
  kmove dia [] 0 (∼b)
  kmove ax [0] 5

/-- `□□(a ∨ ā)`: the rules act two boxes deep.  (Ours.) -/
def deepDer : Der S seq[□□(a ⋎ ∼a)] := by
  kmove box [] □(a ⋎ ∼a)
  kmove box [0] (a ⋎ ∼a)
  kmove or [0, 0] a (∼a)
  kmove ax [0, 0] 4

/-! ## 3. Non-theorems, taken as far as they go

The plan's table "Known non-theorems", and the exercise that must fail. -/

-- Axiom d, `□p ⊃ ◇p`: there is no box, so no move applies.
/-- error: kmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true seq[◇(∼p), ◇p] := by
  kmove

-- Axiom t, `□p ⊃ p`.
/-- error: kmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true seq[◇(∼p), p] := by
  kmove

-- Axiom b, `p ⊃ □◇p`: after `□`, open at `p̄, [◇p]`.
/--
error: kmove: no move applies at goal 0
---
trace: ⊢ Att S   p̄, [◇p]
-/
#guard_msgs in
example : Att S true seq[∼p, □◇p] := by
  kmove box [] ◇p
  trace_state
  kmove

-- Axiom 4, `□p ⊃ □□p`: after `□`, `◇k_c`, `□`, open at `◇p̄, [p̄, [p]]`.
-- The one move left is a `◇k_c` that puts `p̄` where it is already: it is
-- offered because no other move applies.
/--
info: kmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] kmove dia [] 0 (∼p)
---
trace: ⊢ Att S   ◇p̄, [p̄, [p]]
-/
#guard_msgs in
example : Att S true seq[◇(∼p), □□p] := by
  kmove box [] □p
  kmove dia [] 0 (∼p)
  kmove box [0] p
  trace_state
  kmove
  leave_open

-- The same, from the formula of the exercise, `□a ⊃ □□a`.
/--
info:   ◇ā ∨ □□a   by ∨ at []: ◇ā ∨ □□a
    ◇ā, □□a   by □ at []: □□a
      ◇ā, [□a]   by ◇k_c at []: ◇ā, into box 0
        ◇ā, [ā, □a]   by □ at [0]: □a
>         ? ◇ā, [ā, [a]]
  at 0.0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true seq[□a ⊃ □□a] := by
  kmove or [] ◇∼a □□a
  kmove box [] □a
  kmove dia [] 0 (∼a)
  kmove box [0] a
  kmove where
  leave_open

-- Axiom 5, `◇p ⊃ □◇p`: after `□` twice, open at `[p̄], [◇p]`.
/--
error: kmove: no move applies at goal 0
---
trace: ⊢ Att S   [p̄], [◇p]
-/
#guard_msgs in
example : Att S true seq[□(∼p), □◇p] := by
  kmove box [] (∼p)
  kmove box [] ◇p
  trace_state
  kmove

-- `□(p ∨ q) ⊃ □p ∨ □q`: one branch of `∧` stays open.
/--
info:   ◇(p̄ ∧ q̄), □p, □q   by □ at []: □p
    ◇(p̄ ∧ q̄), □q, [p]   by □ at []: □q
      ◇(p̄ ∧ q̄), [p], [q]   by ◇k_c at []: ◇(p̄ ∧ q̄), into box 0
        ◇(p̄ ∧ q̄), [p̄ ∧ q̄, p], [q]   by ∧ at [0]: p̄ ∧ q̄
          ◇(p̄ ∧ q̄), [p̄, p], [q]   by ax at [0]: p, p̄
          ◇(p̄ ∧ q̄), [q̄, p], [q]   by ◇k_c at []: ◇(p̄ ∧ q̄), into box 1
            ◇(p̄ ∧ q̄), [q̄, p], [p̄ ∧ q̄, q]   by ∧ at [1]: p̄ ∧ q̄
>             ? ◇(p̄ ∧ q̄), [q̄, p], [p̄, q]
              ◇(p̄ ∧ q̄), [q̄, p], [q̄, q]   by ax at [1]: q, q̄
  at 0.0.0.1.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true seq[◇(∼p ⋏ ∼q), □p, □q] := by
  kmove box [] p
  kmove box [] q
  kmove dia [] 0 (∼p ⋏ ∼q)
  kmove and [0] (∼p) (∼q)
  kmove ax [0] 0
  kmove dia [] 1 (∼p ⋏ ∼q)
  kmove and [1] (∼p) (∼q)
  kmove ax [1] 1 at 1
  kmove where
  leave_open

/-! ## 4. Every refusal of `step`, seen once -/

/-- error: the move does not apply to goal 0: the sequent has no node at this path -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove ax [1] 0

/-- error: the move does not apply to goal 0: the proposition is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove ax [] 1

/-- error: the move does not apply to goal 0: the negated proposition is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove ax [] 0

/-- error: the move does not apply to goal 0: the conjunction is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove and [] p q

/-- error: the move does not apply to goal 0: the disjunction is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove or [] p q

/-- error: the move does not apply to goal 0: the formula □A is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove box [] p

/-- error: the move does not apply to goal 0: the formula ◇A is not in the node -/
#guard_msgs in
example : Att S true seq[p, [q]] := by
  kmove dia [] 0 p

/-- error: the move does not apply to goal 0: the node has no box at this position -/
#guard_msgs in
example : Att S true seq[◇p, [q]] := by
  kmove dia [] 1 p

/-! ## 5, 6. A query, a pattern, a move set aside, the goal as the infoview
shows it, and where the proof is -/

/--
info: kmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] kmove box [] a
---
info: Try this:
  [apply] kmove box [] a
---
info: kmove: 2 moves of this form apply at goal 0; no move is made. Try these:
  [apply] kmove dia [] 0 (∼a ⋏ ∼b)
  [apply] kmove dia [] 0 b
---
info: Try this:
  [apply] kmove dia [] 0 (∼a ⋏ ∼b)
---
info: kmove: at goal 0, 1 move whose name begins with `a` applies; no move is made. Try these:
  [apply] kmove and [0] (∼a) (∼b)
---
info:   ◇(ā ∧ b̄), □a, ◇b   by □ at []: □a
    ◇(ā ∧ b̄), ◇b, [a]   by ◇k_c at []: ◇(ā ∧ b̄), into box 0
      ◇(ā ∧ b̄), ◇b, [ā ∧ b̄, a]   by ∧ at [0]: ā ∧ b̄
>       ? ◇(ā ∧ b̄), ◇b, [ā, a]
        ? ◇(ā ∧ b̄), ◇b, [b̄, a]
  at 0.0.0: open goal 0; 2 open in all
---
trace: ⊢ Att S   ◇(ā ∧ b̄), ◇b, [a]
-/
#guard_msgs in
example : Att S true seq[◇(∼a ⋏ ∼b), □a, ◇b] := by
  kmove
  kmove box
  trace_state
  kmove dia
  kmove dia _ _ (_ ⋏ _)
  kmove a
  kmove and [0] (∼a) (∼b)
  kmove where
  all_goals leave_open

-- A `◇k_c` that would put into a box a formula the box has is set aside
-- while another move applies: here only `∨` is offered.
/--
info: kmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] kmove or [] q q
-/
#guard_msgs in
example : Att S true seq[◇(∼p), q ⋎ q, [∼p]] := by
  kmove
  leave_open

/-! ## 7. The certificates, checked with no tactic; corrupted ones, rejected -/

def treeCert := Cert.certifier step_sound
def scriptCert := certifier step_sound

/-- info: R3 passes: the evaluation path of treeCert is structural -/
#guard_msgs in
#certify_structural BrunnlerK.Test.treeCert

/-- info: R2 passes: the property of treeCert mentions no budget -/
#guard_msgs in
#certify_statement BrunnlerK.Test.treeCert

-- For the script the path reaches `Nat.repr`, in the library's message for
-- a failing line: a note, and not an error.
/--
info: R3 passes: the evaluation path of scriptCert is structural
---
info: R3 note: the evaluation path of scriptCert reaches 1 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Nat.repr [Init.Data.Repr]: @[implemented_by]: the compiled code is not the definition
    via [BrunnlerK.Test.scriptCert,
 ProofTools.Explore.run,
 ProofTools.Explore.Att.run,
 ProofTools.Explore.Att.runFrom,
 ProofTools.Explore.Cursor.runFrom,
 ProofTools.Explore.Cursor.runFrom._f,
 ProofTools.Explore.Cursor.step,
 instToStringNat,
 Nat.repr]
-/
#guard_msgs in
#certify_structural BrunnlerK.Test.scriptCert

/-- info: R2 passes: the property of scriptCert mentions no budget -/
#guard_msgs in
#certify_statement BrunnlerK.Test.scriptCert

/-- The tree of moves of Example 2.3, written out. -/
def ex23Cert : Cert S :=
  .mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] (∼a) (∼b))
    [.mk (.ax [0] 4) [], .mk (.dia [] 0 b) [.mk (.ax [0] 5) []]]]]

example : ex23Der.cert = ex23Cert := rfl

/-- The kernel checks the tree; the result is the derivation in system K. -/
def ex23ByTree : K seq[◇(∼a ⋏ ∼b), □a, ◇b] := treeCert.verdict _ ex23Cert

/-- The kernel runs the script; the result is the derivation in system K. -/
def ex23ByScript : K seq[◇(∼a ⋏ ∼b), □a, ◇b] := scriptCert.verdict _ ex23Der.script

-- one move wrong: the last axiom on `a`, where it is `b` that is there
theorem bad_tree_rejected : treeCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    (.mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] (∼a) (∼b))
      [.mk (.ax [0] 4) [], .mk (.dia [] 0 b) [.mk (.ax [0] 4) []]]]]) = false := by
  decide +kernel

-- one subtree left out: the right premise of `∧`
theorem short_tree_rejected : treeCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    (.mk (.box [] a) [.mk (.dia [] 0 (∼a ⋏ ∼b)) [.mk (.and [0] (∼a) (∼b))
      [.mk (.ax [0] 4) []]]]) = false := by
  decide +kernel

theorem bad_script_rejected : scriptCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b]
    [⟨0, .box [] a⟩, ⟨0, .dia [] 0 (∼a ⋏ ∼b)⟩, ⟨0, .and [0] (∼a) (∼b)⟩, ⟨0, .ax [0] 4⟩,
      ⟨0, .dia [] 0 b⟩, ⟨0, .ax [0] 4⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check seq[◇(∼a ⋏ ∼b), □a, ◇b] (ex23Der.script.take 5) = false := by
  decide +kernel

-- the same certifier at the proposition
example : Derivable seq[◇(∼a ⋏ ∼b), □a, ◇b] :=
  (Cert.certifier step_sound_derivable.soundT).verdict _ ex23Cert

/-! ## 8. A derivation, walked: by the command, and as a tactic block -/

set_option walk.offer false in
/--
info:   ◇(ā ∧ b̄), □a, ◇b   by □ at []: □a
    ◇(ā ∧ b̄), ◇b, [a]   by ◇k_c at []: ◇(ā ∧ b̄), into box 0
>     ◇(ā ∧ b̄), ◇b, [ā ∧ b̄, a]   by ∧ at [0]: ā ∧ b̄
        0: ◇(ā ∧ b̄), ◇b, [ā, a]   by ax at [0]: a, ā   [closed]
        1: ◇(ā ∧ b̄), ◇b, [b̄, a]   by ◇k_c at []: ◇b, into box 0   [closed]
  at 0.0: 2 premises; no open goals
-/
#guard_msgs in
#walk ex23Der down 0 down 0

/--
trace: ⊢ Walk ex23Der
      ◇(ā ∧ b̄), □a, ◇b   by □ at []: □a
    >   ◇(ā ∧ b̄), ◇b, [a]   by ◇k_c at []: ◇(ā ∧ b̄), into box 0
          0: ◇(ā ∧ b̄), ◇b, [ā ∧ b̄, a]   by ∧ at [0]: ā ∧ b̄   [closed]
      at 0: 1 premise; no open goals
-/
#guard_msgs in
example : Walk ex23Der := by
  down 0
  trace_state

/-! ## 9. A derivation, mapped out to system K as the source states it -/

-- What the tactic built, mapped out, is Example 2.3 as it was written with
-- the constructors of the family (`BrunnlerK/Test/System.lean`).
example : famOfDer ex23Der = ex23 := rfl
example : famOfDer ex23FormDer = ex23' := rfl
example : ex23ByTree = famOfDer ex23Der := rfl

-- and back: S2 gives a derivation of the proof system for it.
example : Nonempty (Der S seq[◇(∼a ⋏ ∼b), □a, ◇b]) := famToDer _ ex23

end BrunnlerK.Test
