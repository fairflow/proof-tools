/-
Tests of the GLS instance of the explorer, every message pinned.

Each message below is pasted from Lean's output, spaces included:
`#guard_msgs` compares exactly.  No marked letter is used.
-/
import GLS.Tactic
import GLS.Source
import LeanCertify

namespace GLS.Test

open ProofTools ProofTools.Explore GLS

-- The variables, under the names `Move.src` writes.
abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-! ## 1. Each rule, where it applies and where it does not -/

#guard (S.step (.idP 0) ([q, p] ⇒ [p])).toOption == some []
#guard (S.step (.idP 0) ([p] ⇒ [q])).toOption.isNone
#guard (S.step (.idP 0) ([□p] ⇒ [□p])).toOption.isNone
#guard (S.step .botL ([p, ⊥] ⇒ [])).toOption == some []
#guard (S.step .botL ([p] ⇒ [⊥])).toOption.isNone
#guard (S.step (.impR p q) ([q] ⇒ [p, p ⟶ q])).toOption == some [[p, q] ⇒ [q, p]]
#guard (S.step (.impR p q) ([p ⟶ q] ⇒ [q])).toOption.isNone
-- one occurrence is removed, the first
#guard (S.step (.impR p q) ([] ⇒ [p ⟶ q, p ⟶ q])).toOption == some [[p] ⇒ [q, p ⟶ q]]
#guard (S.step (.impL p q) ([p, p ⟶ q] ⇒ [q])).toOption == some [[p] ⇒ [p, q], [q, p] ⇒ [q]]
#guard (S.step (.impL p q) ([p] ⇒ [p ⟶ q])).toOption.isNone
#guard (S.step (.glr p) ([] ⇒ [□p])).toOption == some [[□p] ⇒ [p]]
-- the second reader's instance (`campaign/rule-table.md`): boxed and other
-- formulas mixed, a boxed formula twice, the principal box on the left too
#guard (S.step (.glr q) ([□p, q, p ⟶ q, □q, □p] ⇒ [q, □q, ⊥])).toOption
  == some [[p, □p, q, □q, p, □p, □q] ⇒ [q]]
#guard (S.step (.glr p) ([□q] ⇒ [p])).toOption.isNone

-- by the kernel, through `Except.toOption`
example : (S.step (.glr p) ([q, □(□p ⟶ p)] ⇒ [q, □p])).toOption
    = some [[□p ⟶ p, □(□p ⟶ p), □p] ⇒ [p]] := by decide +kernel
example : (S.step (.glr p) ([□q] ⇒ [p])).toOption = none := by decide +kernel

/-! ## 2. The source's derivation, and the axioms of GL

`Id_all_form` (the Coq file, l. 331) at an implication, at a box, and at a
boxed implication, by the tactic.  The three axioms of GL are the
operator's choice (the plan, Q4). -/

/-- `Id_all_form` at `p → q`. -/
def idImp : Der S ([p ⟶ q] ⇒ [p ⟶ q]) := by
  glsmove impR p q
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

/-- `Id_all_form` at `□p`. -/
def idBox : Der S ([□p] ⇒ [□p]) := by
  glsmove glr p
  glsmove idP 0

/-- `Id_all_form` at `□(p → q)`. -/
def idBoxImp : Der S ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) := by
  glsmove glr (p ⟶ q)
  glsmove impR p q
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

/-- The axiom K. -/
def axK : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove impR □(p ⟶ q) (□p ⟶ □q)
  glsmove impR □p □q
  glsmove glr q
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

/-- The axiom 4. -/
def ax4 : Der S ([] ⇒ [□p ⟶ □□p]) := by
  glsmove impR □p □□p
  glsmove glr □p
  glsmove glr p
  glsmove idP 0

/-- Löb's axiom. -/
def axLob : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  glsmove impR □(□p ⟶ p) □p
  glsmove glr p
  glsmove impL □p p
  glsmove glr p
  glsmove idP 0
  glsmove idP 0

/--
info: ⇒ □(□p → p) → □p   by ImpR □(□p → p) → □p
  □(□p → p) ⇒ □p   by GLR □p
    □p → p, □(□p → p), □p ⇒ p   by ImpL □p → p
      □(□p → p), □p ⇒ □p, p   by GLR □p
        □p → p, □(□p → p), p, □p, □p ⇒ p   by IdP p
      p, □(□p → p), □p ⇒ p   by IdP p
-/
#guard_msgs in
#eval IO.println axLob.render

/-! ## 3, 4. Non-theorems, and each refusal -/

-- `⇒ □p → p`: after ImpR no move applies.
/-- error: glsmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⇒ [□p ⟶ p]) := by
  glsmove impR □p p
  glsmove

/-- error: glsmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⇒ [p]) := by
  glsmove

-- `⇒ □⊥ → ⊥`: after ImpR no move applies (`⊥` on the right is no axiom).
/-- error: glsmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⇒ [□⊥ ⟶ ⊥]) := by
  glsmove impR □⊥ ⊥
  glsmove

-- `⇒ □(□p → p)`: GLR, ImpR, and then no move applies.
/-- error: glsmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⇒ [□(□p ⟶ p)]) := by
  glsmove glr (□p ⟶ p)
  glsmove impR □p p
  glsmove

/-- `⇒ (□p → □q) → □(p → q)`: the second premise of ImpL closes, the
first stays open whichever box GLR takes. -/
def notConverseK : Att S true ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) := by
  glsmove impR (□p ⟶ □q) □(p ⟶ q)
  glsmove impL □p □q
  glsmove glr p at 0
  glsmove glr (p ⟶ q) at 1
  glsmove impR p q at 1
  glsmove idP 1 at 1
  all_goals leave_open

/--
info: ⇒ (□p → □q) → □(p → q)   by ImpR (□p → □q) → □(p → q)
  □p → □q ⇒ □(p → q)   by ImpL □p → □q
    ⇒ □p, □(p → q)   by GLR □p
      ? □p ⇒ p
    □q ⇒ □(p → q)   by GLR □(p → q)
      q, □q, □(p → q) ⇒ p → q   by ImpR p → q
        p, q, □q, □(p → q) ⇒ q   by IdP q
-/
#guard_msgs in
#eval IO.println notConverseK.render

/-- error: the move does not apply to goal 0: IdP: the variable is not on both sides of the sequent -/
#guard_msgs in
example : Att S true ([p] ⇒ [q]) := by
  glsmove idP 0

/-- error: the move does not apply to goal 0: BotL: ⊥ is not in the antecedent -/
#guard_msgs in
example : Att S true ([p] ⇒ [⊥]) := by
  glsmove botL

/-- error: the move does not apply to goal 0: ImpR: the implication is not in the succedent -/
#guard_msgs in
example : Att S true ([p ⟶ q] ⇒ [q]) := by
  glsmove impR p q

/-- error: the move does not apply to goal 0: ImpL: the implication is not in the antecedent -/
#guard_msgs in
example : Att S true ([p] ⇒ [p ⟶ q]) := by
  glsmove impL p q

/-- error: the move does not apply to goal 0: GLR: the boxed formula is not in the succedent -/
#guard_msgs in
example : Att S true ([□p] ⇒ [p]) := by
  glsmove glr p

/-! ## 5, 6. A query, a pattern, the goal as the infoview shows it, and
where the proof is -/

/--
info: glsmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] glsmove impR □(p ⟶ q) (□p ⟶ □q)
---
info: Try this:
  [apply] glsmove impR □(p ⟶ q) (□p ⟶ □q)
---
info: Try this:
  [apply] glsmove impR □p □q
---
info: Try this:
  [apply] glsmove glr q
---
info:   ⇒ □(p → q) → □p → □q   by ImpR □(p → q) → □p → □q
    □(p → q) ⇒ □p → □q   by ImpR □p → □q
      □p, □(p → q) ⇒ □q   by GLR □q
>       ? p, □p, p → q, □(p → q), □q ⇒ q
  at 0.0.0: open goal 0; 1 open in all
---
trace: ⊢ Att S   □p, □(p → q) ⇒ □q
-/
#guard_msgs in
example : Att S true ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove
  glsmove impR
  glsmove impR
  trace_state
  glsmove glr
  glsmove where
  all_goals leave_open

-- Two moves apply: an axiom and a rule.
/--
info: glsmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] glsmove idP 0
  [apply] glsmove impL □p p
-/
#guard_msgs in
example : Att S true ([□p ⟶ p, p] ⇒ [p]) := by
  glsmove
  all_goals leave_open

/-! ## 7. The certificates, checked with no tactic; corrupted ones, rejected -/

/-- The certifier of derivations by their trees of moves. -/
def treeCert := Cert.certifier step_sound
/-- The certifier of derivations by their scripts. -/
def scriptCert := certifier step_sound

/-- info: R3 passes: the evaluation path of treeCert is structural -/
#guard_msgs in
#certify_structural GLS.Test.treeCert

/-- info: R2 passes: the property of treeCert mentions no budget -/
#guard_msgs in
#certify_statement GLS.Test.treeCert

/--
info: R3 passes: the evaluation path of scriptCert is structural
---
info: R3 note: the evaluation path of scriptCert reaches 1 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Nat.repr [Init.Data.Repr]: @[implemented_by]: the compiled code is not the definition
    via [GLS.Test.scriptCert,
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
#certify_structural GLS.Test.scriptCert

/-- info: R2 passes: the property of scriptCert mentions no budget -/
#guard_msgs in
#certify_statement GLS.Test.scriptCert

/-- The tree of moves of `axLob`, written out. -/
def axLobCert : Cert S :=
  .mk (.impR □(□p ⟶ p) □p) [.mk (.glr p) [.mk (.impL □p p)
    [.mk (.glr p) [.mk (.idP 0) []], .mk (.idP 0) []]]]

example : axLob.cert = axLobCert := rfl

/-- The kernel checks the tree; the result is the derivation in GLS. -/
def axLobByTree : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := treeCert.verdict _ axLobCert

/-- The kernel runs the script; the result is the derivation in GLS. -/
def axLobByScript : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := scriptCert.verdict _ axLob.script

/-- A wrong move: the inner GLR on `q`, which is not there. -/
theorem bad_tree_rejected :
    treeCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p])
      (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr p) [.mk (.impL □p p)
        [.mk (.glr q) [.mk (.idP 0) []], .mk (.idP 0) []]]]) = false := by
  decide +kernel

/-- A tree that stops early: the second premise of ImpL is left out. -/
theorem short_tree_rejected :
    treeCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p])
      (.mk (.impR □(□p ⟶ p) □p) [.mk (.glr p) [.mk (.impL □p p)
        [.mk (.glr p) [.mk (.idP 0) []]]]]) = false := by
  decide +kernel

theorem bad_script_rejected :
    scriptCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p])
      [⟨0, .impR □(□p ⟶ p) □p⟩, ⟨0, .glr p⟩, ⟨0, .impL □p p⟩, ⟨0, .glr q⟩,
       ⟨0, .idP 0⟩, ⟨0, .idP 0⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check ([] ⇒ [□(□p ⟶ p) ⟶ □p]) (axLob.script.take 5) = false := by
  decide +kernel

-- the same certifier at the proposition
example : Derivable ([] ⇒ [□(□p ⟶ p) ⟶ □p]) :=
  (Cert.certifier step_sound_derivable.soundT).verdict _ axLobCert

/-! ## 8. A derivation, walked -/

set_option walk.offer false in
/--
info:   ⇒ □(□p → p) → □p   by ImpR □(□p → p) → □p
>   □(□p → p) ⇒ □p   by GLR □p
      0: □p → p, □(□p → p), □p ⇒ p   by ImpL □p → p   [closed]
  at 0: 1 premise; no open goals
-/
#guard_msgs in
#walk axLob down 0

/--
trace: ⊢ Walk axLob
      ⇒ □(□p → p) → □p   by ImpR □(□p → p) → □p
    >   □(□p → p) ⇒ □p   by GLR □p
          0: □p → p, □(□p → p), □p ⇒ p   by ImpL □p → p   [closed]
      at 0: 1 premise; no open goals
-/
#guard_msgs in
example : Walk axLob := by
  down 0
  trace_state

/-! ## 9. A derivation, mapped out to the family -/

example : famOfDer idImp = Source.idImp := rfl
example : famOfDer idBox = Source.idBox := rfl
example : famOfDer idBoxImp = Source.idBoxImp := rfl
example : axLobByTree = famOfDer axLob := rfl
example : (famOfDer axLob).height = 5 := rfl

/-! ## 10. The exercises of `Play/GLS.lean`, each run here

For each: the moves offered at its first step, and its outcome, by script
with no tactic: the derivation, or where a non-theorem stops. -/

/-- The moves of the candidates that apply at a sequent, as the tactic
writes them. -/
def offered (j : Seq) : List String :=
  ((candidates j).filter fun m => (S.step m j).toOption.isSome).map Move.src

-- Exercise 1: the identity on `□p → q`.
#guard offered ([□p ⟶ q] ⇒ [□p ⟶ q]) == ["impR □p q", "impL □p q"]
#guard derives S ([□p ⟶ q] ⇒ [□p ⟶ q])
  [⟨0, .impR □p q⟩, ⟨0, .impL □p q⟩, ⟨0, .glr p⟩, ⟨0, .idP 0⟩, ⟨0, .idP 1⟩]

-- Exercise 2: the axiom K.
#guard offered ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) == ["impR □(p ⟶ q) (□p ⟶ □q)"]
#guard derives S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) axK.script

-- Exercise 3: the axiom 4.
#guard offered ([] ⇒ [□p ⟶ □□p]) == ["impR □p □□p"]
#guard derives S ([] ⇒ [□p ⟶ □□p]) ax4.script

-- Exercise 4: Löb's axiom.
#guard offered ([] ⇒ [□(□p ⟶ p) ⟶ □p]) == ["impR □(□p ⟶ p) □p"]
#guard derives S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) axLob.script
example : derives S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) axLob.script = true := by decide +kernel

-- Exercise 5: `⇒ □p → p`.  One move at the first step; after it, none
-- (the error of the query is pinned in section 3).
#guard offered ([] ⇒ [□p ⟶ p]) == ["impR □p p"]
#guard (S.step (.impR □p p) ([] ⇒ [□p ⟶ p])).toOption == some [[□p] ⇒ [p]]
#guard offered ([□p] ⇒ [p]) == []

-- Exercise 6: the converse of K.  The attempt `notConverseK` of section 3
-- is as far as it goes: the goal left after GLR on `□p` has no move, and
-- neither has the one left after GLR on `□(p → q)` and ImpR.
#guard offered ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) == ["impR (□p ⟶ □q) □(p ⟶ q)"]
#guard offered ([] ⇒ [□p, □(p ⟶ q)]) == ["glr p", "glr (p ⟶ q)"]
#guard offered ([□p] ⇒ [p]) == []
#guard (S.step (.glr (p ⟶ q)) ([] ⇒ [□p, □(p ⟶ q)])).toOption == some [[□(p ⟶ q)] ⇒ [p ⟶ q]]
#guard offered ([p, □(p ⟶ q)] ⇒ [q]) == []

-- The derivation the file walks.
#guard derives S ([□p] ⇒ [□p]) [⟨0, .glr p⟩, ⟨0, .idP 0⟩]

end GLS.Test
