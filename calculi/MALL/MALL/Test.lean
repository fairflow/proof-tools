/-
Tests of the MALL instance: each rule on `step`, derivations of what the
source asserts, the known non-theorems, every refusal, the tactic's
messages, the certificates and their negative tests, a walk, and the map
out.  Every message is pinned: it was pasted from Lean's output after
reading it.

Code, not theory.  The letters are written `p q r`; a dual is typed `pᗮ`
(U+15EE after the letter) and printed `p⊥`.
-/
import MALL.Tactic
import MALL.Source
import LeanCertify

namespace MALL.Test

open ProofTools ProofTools.Explore MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## 1. Each rule, where it applies and where it does not -/

-- ax: the sequent is `⊢ A, A⊥`, in either order, and nothing more
#guard (S.step (.ax p) [p, pᗮ]).toOption == some []
#guard (S.step (.ax p) [pᗮ, p]).toOption == some []
#guard (S.step (.ax (p ⊗ q)) [pᗮ ⅋ qᗮ, p ⊗ q]).toOption == some []
#guard (S.step (.ax p) [p, pᗮ, q]).toOption.isNone
#guard (S.step (.ax p) [p, p]).toOption.isNone
#guard (S.step (.ax p) [p]).toOption.isNone
-- cut: the context named goes to the first premise, the rest to the second
#guard (S.step (.cut p [q]) [q, r]).toOption == some [[p, q], [pᗮ, r]]
#guard (S.step (.cut p []) [q, r]).toOption == some [[p], [pᗮ, q, r]]
#guard (S.step (.cut p [q, q]) [q, r]).toOption.isNone
-- ⊤: any context
#guard (S.step .top [p, ⊤, q]).toOption == some []
#guard (S.step .top [p, q]).toOption.isNone
-- &: the same context in both premises
#guard (S.step (.wth p q) [r, p & q]).toOption == some [[p, r], [q, r]]
#guard (S.step (.wth p q) [r, p ⊕ q]).toOption.isNone
-- 1⊕, 2⊕
#guard (S.step (.plus₁ p q) [r, p ⊕ q]).toOption == some [[p, r]]
#guard (S.step (.plus₂ p q) [r, p ⊕ q]).toOption == some [[q, r]]
#guard (S.step (.plus₁ p q) [r, q ⊕ p]).toOption.isNone
#guard (S.step (.plus₂ p q) [r]).toOption.isNone
-- 1: the sequent is `⊢ 1`, and nothing more (no weakening)
#guard (S.step .one [𝟏]).toOption == some []
#guard (S.step .one [𝟏, 𝟏]).toOption.isNone
#guard (S.step .one [𝟏, p]).toOption.isNone
#guard (S.step .one []).toOption.isNone
-- ⊥: one occurrence is removed
#guard (S.step .bot [p, ⊥, ⊥]).toOption == some [[p, ⊥]]
#guard (S.step .bot [p]).toOption.isNone
-- ⊗: the context named goes with `A`, the rest with `B`; it must be part
-- of the rest, as a multiset (no contraction: `q` is there once)
#guard (S.step (.tensor p q [r]) [r, p ⊗ q, pᗮ]).toOption == some [[p, r], [q, pᗮ]]
#guard (S.step (.tensor p q []) [r, p ⊗ q]).toOption == some [[p], [q, r]]
#guard (S.step (.tensor p q [r, r]) [r, p ⊗ q, r]).toOption == some [[p, r, r], [q]]
#guard (S.step (.tensor p q [r, r]) [r, p ⊗ q]).toOption.isNone
#guard (S.step (.tensor p q [p ⊗ q]) [r, p ⊗ q]).toOption.isNone
#guard (S.step (.tensor p q []) [r, p ⅋ q]).toOption.isNone
-- ⅋
#guard (S.step (.par p q) [r, p ⅋ q]).toOption == some [[p, q, r]]
#guard (S.step (.par p q) [r, p ⊗ q]).toOption.isNone
-- one step reduces in the kernel
example : (S.step (.tensor p q [r]) [r, p ⊗ q, pᗮ]).toOption = some [[p, r], [q, pᗮ]] := by
  decide +kernel
example : (S.step .one [𝟏, 𝟏]).toOption = none := by decide +kernel

/-! ## 2. What the source asserts, by the tactic

The source draws no derivation of this fragment; these are the
derivations of `MALL/Source.lean`, each cited there. -/

/-- P. 5: "A ⊸ A & A is [derivable]". -/
def p5 : Der S [pᗮ ⅋ (p & p)] := by
  mallmove par pᗮ (p & p)
  mallmove wth p p
  mallmove ax p
  mallmove ax p

/-- The axiom at `p ⊗ q`, from axioms at letters (the remark of p. 22). -/
def idTensor : Der S [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove par pᗮ qᗮ
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q

/-- The same sequent, by the axiom at a compound formula. -/
def idTensor' : Der S [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove ax (p ⊗ q)

/-- 1.9(ii), `1 ⊗ G = G`: both halves. -/
def tensorUnit : Der S [(𝟏 ⊗ p)ᗮ, p] := by
  mallmove par ⊥ pᗮ
  mallmove bot
  mallmove ax pᗮ

def tensorUnit' : Der S [pᗮ, 𝟏 ⊗ p] := by
  mallmove tensor 𝟏 p []
  mallmove one
  mallmove ax p

/-- 1.13(i), ⊗ distributes over ⊕, one half. -/
def distrib : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  mallmove par pᗮ (qᗮ & rᗮ)
  mallmove wth qᗮ rᗮ
  mallmove plus₁ (p ⊗ q) (p ⊗ r)
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove plus₂ (p ⊗ q) (p ⊗ r)
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

/-- 1.13(i), `⊤ ⅋ G = ⊤`, one half. -/
def topAbsorbs : Der S [(⊤ ⅋ p)ᗮ, ⊤] := by
  mallmove top

/-- The cut rule. -/
def cutEx : Der S [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove par pᗮ qᗮ
  mallmove tensor q p [qᗮ]
  mallmove ax q
  mallmove ax p

/-! ## 3, 4. Non-theorems, and each refusal -/

-- `⊢ 1, 1`: weakening is forbidden
/-- error: the move does not apply to goal 0: 1: the sequent is not ⊢ 1 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove one

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove

-- `⊢ p ⊕ p⊥`: contraction is forbidden; either choice leaves one letter
/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [p ⊕ pᗮ] := by
  mallmove plus₁ p pᗮ
  mallmove

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [p ⊕ pᗮ] := by
  mallmove plus₂ p pᗮ
  mallmove

-- p. 5: "A ⊸ A ⊗ A is not derivable": whichever way the context is
-- split, one premise is `⊢ p`
/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove par pᗮ (p ⊗ p)
  mallmove tensor p p [pᗮ]
  mallmove ax p
  mallmove

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove par pᗮ (p ⊗ p)
  mallmove tensor p p []
  mallmove

-- the empty sequent, `⊢ 0`, `⊢ ⊥`, `⊢ p`
/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [] := by
  mallmove

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [𝟎] := by
  mallmove

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [⊥] := by
  mallmove bot
  mallmove

-- the other refusals of `step`, each seen once
/-- error: the move does not apply to goal 0: ax: the sequent is not ⊢ A, A⊥ -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove ax p

/--
error: the move does not apply to goal 0: cut: the context named for the first premise is not part of the sequent
-/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove cut p [r]

/-- error: the move does not apply to goal 0: ⊤: ⊤ is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove top

/-- error: the move does not apply to goal 0: &: the formula is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove wth p q

/-- error: the move does not apply to goal 0: 1⊕: the formula is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove plus₁ p q

/-- error: the move does not apply to goal 0: 2⊕: the formula is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove plus₂ p q

/-- error: the move does not apply to goal 0: ⊥: ⊥ is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove bot

/--
error: the move does not apply to goal 0: ⊗: the formula is not in the sequent, or the context named for the first premise is not part of the rest
-/
#guard_msgs in
example : Att S true [p ⊗ q, r] := by
  mallmove tensor p q [p]

/-- error: the move does not apply to goal 0: ⅋: the formula is not in the sequent -/
#guard_msgs in
example : Att S true [p, q] := by
  mallmove par p q

/-! ## 5, 6. A query, a pattern, the goal as the infoview shows it, and
where the proof is -/

/--
info: mallmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] mallmove par pᗮ qᗮ
  [apply] mallmove tensor q p []
  [apply] mallmove tensor q p [pᗮ ⅋ qᗮ]
---
info: Try this:
  [apply] mallmove par pᗮ qᗮ
---
info: mallmove: 4 moves of this form apply at goal 0; no move is made. Try these:
  [apply] mallmove tensor q p []
  [apply] mallmove tensor q p [qᗮ]
  [apply] mallmove tensor q p [pᗮ]
  [apply] mallmove tensor q p [pᗮ, qᗮ]
---
info:   ⊢ p⊥ ⅋ q⊥, q ⊗ p   by ⅋ p⊥ ⅋ q⊥
    ⊢ p⊥, q⊥, q ⊗ p   by ⊗ q ⊗ p [q⊥]
>     ? ⊢ q, q⊥
      ? ⊢ p, p⊥
  at 0.0: open goal 0; 2 open in all
---
trace: ⊢ Att S   ⊢ p⊥, q⊥, q ⊗ p
-/
#guard_msgs in
example : Att S true [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove
  mallmove par
  trace_state
  mallmove tensor
  mallmove tensor q p [qᗮ]
  mallmove where
  all_goals leave_open

/-! ## 7. The certificates, checked with no tactic; corrupted ones, rejected -/

def treeCert := Cert.certifier step_sound
def scriptCert := certifier step_sound

/-- info: R3 passes: the evaluation path of treeCert is structural -/
#guard_msgs in
#certify_structural MALL.Test.treeCert

/-- info: R2 passes: the property of treeCert mentions no budget -/
#guard_msgs in
#certify_statement MALL.Test.treeCert

/-- info: R2 passes: the property of scriptCert mentions no budget -/
#guard_msgs in
#certify_statement MALL.Test.scriptCert

/-- The tree of moves of `p5`, written out. -/
def p5Cert : Cert S := .mk (.par pᗮ (p & p)) [.mk (.wth p p) [.mk (.ax p) [], .mk (.ax p) []]]

example : p5.cert = p5Cert := rfl

/-- The kernel checks the tree; the result is the derivation. -/
def p5ByTree : Fam [pᗮ ⅋ (p & p)] := treeCert.verdict _ p5Cert

/-- The kernel runs the script; the result is the derivation. -/
def p5ByScript : Fam [pᗮ ⅋ (p & p)] := scriptCert.verdict _ p5.script

-- a wrong move: 1⊕ where the formula is a &
theorem bad_tree_rejected :
    treeCert.check [pᗮ ⅋ (p & p)]
      (.mk (.par pᗮ (p & p)) [.mk (.plus₁ p p) [.mk (.ax p) []]]) = false := by
  decide +kernel

-- a wrong split: the context of `q ⊗ p` given the other way round
theorem bad_split_rejected :
    treeCert.check [pᗮ, qᗮ, q ⊗ p]
      (.mk (.tensor q p [pᗮ]) [.mk (.ax q) [], .mk (.ax p) []]) = false := by
  decide +kernel

theorem short_tree_rejected :
    treeCert.check [pᗮ ⅋ (p & p)]
      (.mk (.par pᗮ (p & p)) [.mk (.wth p p) [.mk (.ax p) []]]) = false := by
  decide +kernel

theorem bad_script_rejected :
    scriptCert.check [pᗮ ⅋ (p & p)]
      [⟨0, .par pᗮ (p & p)⟩, ⟨0, .wth p p⟩, ⟨0, .ax p⟩, ⟨0, .ax q⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check [pᗮ ⅋ (p & p)] (p5.script.take 3) = false := by
  decide +kernel

-- the same certifier at the proposition
example : Derivable [pᗮ ⅋ (p & p)] :=
  (Cert.certifier step_sound_derivable.soundT).verdict _ p5Cert

/-! ## 8. A derivation, walked: by the command, and as a tactic block -/

set_option walk.offer false in
/--
info:   ⊢ p⊥ ⅋ (p & p)   by ⅋ p⊥ ⅋ (p & p)
>   ⊢ p⊥, p & p   by & p & p
      0: ⊢ p, p⊥   by ax p   [closed]
      1: ⊢ p, p⊥   by ax p   [closed]
  at 0: 2 premises; no open goals
-/
#guard_msgs in
#walk p5 down 0

/--
trace: ⊢ Walk p5
      ⊢ p⊥ ⅋ (p & p)   by ⅋ p⊥ ⅋ (p & p)
    >   ⊢ p⊥, p & p   by & p & p
          0: ⊢ p, p⊥   by ax p   [closed]
          1: ⊢ p, p⊥   by ax p   [closed]
      at 0: 2 premises; no open goals
-/
#guard_msgs in
example : Walk p5 := by
  down 0
  trace_state

/-! ## 9. A derivation, mapped out to the family -/

example : famOfDer p5 =
    .par pᗮ (p & p) [] (by decide)
      (.wth p p [pᗮ] (by decide) (.ax p (by decide)) (.ax p (by decide))) := rfl

example : p5ByTree = famOfDer p5 := rfl

-- the derivation built with the tactic, mapped out, is the one written
-- with the constructors in `MALL/Source.lean`
example : famOfDer p5 = Source.p5 := rfl
example : famOfDer idTensor = Source.idTensor := rfl
example : famOfDer distrib = Source.distrib := rfl
example : (famOfDer cutEx).height = 4 := rfl

/-! ## 10. The exercises of `Play/MALL.lean`, by script

For each: the moves offered at its first step, and its outcome: a script
that derives it, or where a non-theorem stops. -/

-- 1
/--
info: mallmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] mallmove par pᗮ (p & p)
-/
#guard_msgs in
example : Att S true [pᗮ ⅋ (p & p)] := by
  mallmove
  all_goals leave_open

#guard derives S [pᗮ ⅋ (p & p)] p5.script

-- 2
/--
info: mallmove: at goal 0, 4 moves apply; no move is made. Try these:
  [apply] mallmove ax (pᗮ ⅋ qᗮ)
  [apply] mallmove par pᗮ qᗮ
  [apply] mallmove tensor p q []
  [apply] mallmove tensor p q [pᗮ ⅋ qᗮ]
-/
#guard_msgs in
example : Att S true [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove
  all_goals leave_open

#guard derives S [(p ⊗ q)ᗮ, p ⊗ q]
  [⟨0, .par pᗮ qᗮ⟩, ⟨0, .tensor p q [pᗮ]⟩, ⟨0, .ax p⟩, ⟨0, .ax q⟩]
-- the other split does not close: `⊢ p, q⊥` is no axiom
#guard !derives S [(p ⊗ q)ᗮ, p ⊗ q]
  [⟨0, .par pᗮ qᗮ⟩, ⟨0, .tensor p q [qᗮ]⟩, ⟨0, .ax p⟩, ⟨0, .ax q⟩]

-- 3
/--
info: mallmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] mallmove par ⊥ pᗮ
-/
#guard_msgs in
example : Att S true [(𝟏 ⊗ p)ᗮ, p] := by
  mallmove
  all_goals leave_open

/--
info: mallmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] mallmove tensor 𝟏 p []
  [apply] mallmove tensor 𝟏 p [pᗮ]
-/
#guard_msgs in
example : Att S true [pᗮ, 𝟏 ⊗ p] := by
  mallmove
  all_goals leave_open

#guard derives S [(𝟏 ⊗ p)ᗮ, p] tensorUnit.script
#guard derives S [pᗮ, 𝟏 ⊗ p] [⟨0, .tensor 𝟏 p []⟩, ⟨0, .one⟩, ⟨0, .ax p⟩]
-- with `p⊥` on the left, the first premise is `⊢ 1, p⊥`: the rule 1 is refused
#guard (run S [pᗮ, 𝟏 ⊗ p] [⟨0, .tensor 𝟏 p [pᗮ]⟩, ⟨0, .one⟩]).2.isSome

-- 4
/--
info: mallmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] mallmove par pᗮ (qᗮ & rᗮ)
  [apply] mallmove plus₁ (p ⊗ q) (p ⊗ r)
  [apply] mallmove plus₂ (p ⊗ q) (p ⊗ r)
-/
#guard_msgs in
example : Att S true [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  mallmove
  all_goals leave_open

#guard derives S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] distrib.script

-- 5
/--
info: mallmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] mallmove par pᗮ (qᗮ ⊕ rᗮ)
  [apply] mallmove wth (p ⊗ q) (p ⊗ r)
-/
#guard_msgs in
example : Att S true [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)] := by
  mallmove
  all_goals leave_open

/-- 1.13(ii), half-distributivity. -/
def halfDistrib : Der S [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)] := by
  mallmove par pᗮ (qᗮ ⊕ rᗮ)
  mallmove wth (p ⊗ q) (p ⊗ r)
  mallmove plus₁ qᗮ rᗮ
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove plus₂ qᗮ rᗮ
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

#guard derives S [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)] halfDistrib.script

-- 6: with the cut, and without it
#guard derives S [pᗮ, qᗮ, q ⊗ p] cutEx.script
#guard derives S [pᗮ, qᗮ, q ⊗ p] [⟨0, .tensor q p [qᗮ]⟩, ⟨0, .ax q⟩, ⟨0, .ax p⟩]

-- 7: section 3 has where it stops, for both splits
/--
info: mallmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] mallmove par pᗮ (p ⊗ p)
---
info: mallmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] mallmove tensor p p []
  [apply] mallmove tensor p p [pᗮ]
-/
#guard_msgs in
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove
  mallmove par pᗮ (p ⊗ p)
  mallmove
  all_goals leave_open

-- 8: section 3 has both messages

-- 9
/--
info: mallmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] mallmove plus₁ p pᗮ
  [apply] mallmove plus₂ p pᗮ
-/
#guard_msgs in
example : Att S true [p ⊕ pᗮ, p ⊕ pᗮ] := by
  mallmove
  all_goals leave_open

#guard derives S [p ⊕ pᗮ, p ⊕ pᗮ] [⟨0, .plus₁ p pᗮ⟩, ⟨0, .plus₂ p pᗮ⟩, ⟨0, .ax pᗮ⟩]

-- 10: the four first moves; after 1⊕ and the only split that keeps `p⊥`
-- with `p`, the & leaves `⊢ r, q⊥`
/--
info: mallmove: at goal 0, 4 moves apply; no move is made. Try these:
  [apply] mallmove plus₁ (pᗮ ⅋ qᗮ) (pᗮ ⅋ rᗮ)
  [apply] mallmove plus₂ (pᗮ ⅋ qᗮ) (pᗮ ⅋ rᗮ)
  [apply] mallmove tensor p (q & r) []
  [apply] mallmove tensor p (q & r) [(pᗮ ⅋ qᗮ) ⊕ (pᗮ ⅋ rᗮ)]
-/
#guard_msgs in
example : Att S true [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] := by
  mallmove
  all_goals leave_open

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] := by
  mallmove plus₁ (pᗮ ⅋ qᗮ) (pᗮ ⅋ rᗮ)
  mallmove par pᗮ qᗮ
  mallmove tensor p (q & r) [pᗮ]
  mallmove ax p
  mallmove wth q r
  mallmove ax q
  mallmove

-- the walk at the end of the file
def d : Der S [pᗮ, 𝟏 ⊗ p] := by
  mallmove tensor 𝟏 p []
  mallmove one
  mallmove ax p

set_option walk.offer false in
/--
info:   ⊢ p⊥, 1 ⊗ p   by ⊗ 1 ⊗ p []
>   ⊢ 1   by 1
  at 0: no premises; no open goals
-/
#guard_msgs in
#walk d down 0

end MALL.Test
