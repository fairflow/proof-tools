/-
Tests of the DILL instance: each move on `step`, the derivations of
`DILL/Source.lean` again by the tactic, the known non-theorems of the
plan, every refusal, the tactic's messages, the certificates and their
negative tests, a walk, the map out, and the exercises of `Play/DILL.lean`
by script.  Every message is pinned: it was pasted from Lean's output
after reading it.

Code, not theory.  The atoms are written `p q r s`.  A sequent is typed
`Γ ⨾ Δ ⟹ C` with lists for the zones, and printed `Γ ; Δ ⟹ C` with `·`
for an empty zone.  `!A` is typed `(!A)` wherever an operator follows it,
and as a move's argument; `A ⊕ B` is typed `(A ⊕ B)` before `⊸`: core
Lean's `!` and `⊕` would take more.
-/
import DILL.Tactic
import DILL.Source
import LeanCertify

namespace DILL.Test

open ProofTools ProofTools.Explore DILL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-! ## 1. Each move, where it applies and where it does not -/

-- init: the linear zone is the conclusion and nothing more, whatever the
-- unrestricted zone (no linear weakening); a valid hypothesis is not a
-- linear one
#guard (S.step .init ([] ⨾ [p] ⟹ p)).toOption == some []
#guard (S.step .init ([q] ⨾ [p] ⟹ p)).toOption == some []
#guard (S.step .init ([] ⨾ [p, q] ⟹ p)).toOption.isNone
#guard (S.step .init ([] ⨾ [] ⟹ p)).toOption.isNone
#guard (S.step .init ([p] ⨾ [] ⟹ p)).toOption.isNone
#guard (S.step .init ([] ⨾ [q] ⟹ p)).toOption.isNone
-- copy: the formula stays in the unrestricted zone, so it can be copied
-- again; a linear hypothesis cannot be copied
#guard (S.step (.copy p) ([p] ⨾ [] ⟹ p)).toOption == some [[p] ⨾ [p] ⟹ p]
#guard (S.step (.copy p) ([q, p] ⨾ [p] ⟹ r)).toOption == some [[q, p] ⨾ [p, p] ⟹ r]
#guard (S.step (.copy p) ([q] ⨾ [] ⟹ p)).toOption.isNone
#guard (S.step (.copy p) ([] ⨾ [p] ⟹ p)).toOption.isNone
-- ⊗L: on the linear zone only
#guard (S.step (.tensorL p q) ([] ⨾ [r, p ⊗ q] ⟹ r)).toOption == some [[] ⨾ [p, q, r] ⟹ r]
#guard (S.step (.tensorL p q) ([] ⨾ [p, q] ⟹ r)).toOption.isNone
#guard (S.step (.tensorL p q) ([p ⊗ q] ⨾ [] ⟹ r)).toOption.isNone
-- ⊗R: the zone named goes to the first premise, the rest to the second;
-- both premises keep the unrestricted zone.  The zone named must be part
-- of the linear zone, as a multiset (no contraction: `p` is there once),
-- and a valid hypothesis is not part of it
#guard (S.step (.tensorR p q [p]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption
  == some [[s] ⨾ [p] ⟹ p, [s] ⨾ [q, r] ⟹ q]
#guard (S.step (.tensorR p q []) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption
  == some [[s] ⨾ [] ⟹ p, [s] ⨾ [p, q, r] ⟹ q]
#guard (S.step (.tensorR p q [r, p]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption
  == some [[s] ⨾ [r, p] ⟹ p, [s] ⨾ [q] ⟹ q]
#guard (S.step (.tensorR p q [p, p]) ([s] ⨾ [p, q, p] ⟹ p ⊗ q)).toOption
  == some [[s] ⨾ [p, p] ⟹ p, [s] ⨾ [q] ⟹ q]
#guard (S.step (.tensorR p q [p, p]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption.isNone
#guard (S.step (.tensorR p q [s]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption.isNone
#guard (S.step (.tensorR q p [p]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption.isNone
#guard (S.step (.tensorR p q [p]) ([s] ⨾ [p, q, r] ⟹ p & q)).toOption.isNone
-- 1L: one occurrence is removed
#guard (S.step .oneL ([] ⨾ [p, 𝟏, 𝟏] ⟹ p)).toOption == some [[] ⨾ [p, 𝟏] ⟹ p]
#guard (S.step .oneL ([𝟏] ⨾ [p] ⟹ p)).toOption.isNone
-- 1R: the linear zone is empty (no weakening), whatever the unrestricted
-- zone
#guard (S.step .oneR ([p] ⨾ [] ⟹ 𝟏)).toOption == some []
#guard (S.step .oneR ([] ⨾ [p] ⟹ 𝟏)).toOption.isNone
#guard (S.step .oneR ([] ⨾ [𝟏] ⟹ 𝟏)).toOption.isNone
#guard (S.step .oneR ([] ⨾ [] ⟹ p)).toOption.isNone
-- ⊸L: the zone named goes to the premise for `A`, the rest with `B`; it
-- must be part of the rest (no contraction), and the implication is not
-- part of its own rest unless it is there twice
#guard (S.step (.lolliL p q [p]) ([] ⨾ [p, p ⊸ q, r] ⟹ s)).toOption
  == some [[] ⨾ [p] ⟹ p, [] ⨾ [q, r] ⟹ s]
#guard (S.step (.lolliL p q []) ([] ⨾ [p, p ⊸ q, r] ⟹ s)).toOption
  == some [[] ⨾ [] ⟹ p, [] ⨾ [q, p, r] ⟹ s]
#guard (S.step (.lolliL p q [r, p]) ([] ⨾ [p, p ⊸ q, r] ⟹ s)).toOption
  == some [[] ⨾ [r, p] ⟹ p, [] ⨾ [q] ⟹ s]
#guard (S.step (.lolliL p q [p ⊸ q]) ([] ⨾ [p ⊸ q, p ⊸ q] ⟹ s)).toOption
  == some [[] ⨾ [p ⊸ q] ⟹ p, [] ⨾ [q] ⟹ s]
#guard (S.step (.lolliL p q [p, p]) ([] ⨾ [p, p ⊸ q, r] ⟹ s)).toOption.isNone
#guard (S.step (.lolliL p q [p ⊸ q]) ([] ⨾ [p, p ⊸ q, r] ⟹ s)).toOption.isNone
#guard (S.step (.lolliL p q [p]) ([] ⨾ [p, q ⊸ p] ⟹ s)).toOption.isNone
#guard (S.step (.lolliL p q []) ([p ⊸ q] ⨾ [p] ⟹ q)).toOption.isNone
-- ⊸R
#guard (S.step (.lolliR p q) ([s] ⨾ [r] ⟹ p ⊸ q)).toOption == some [[s] ⨾ [p, r] ⟹ q]
#guard (S.step (.lolliR p q) ([] ⨾ [r] ⟹ p ⊗ q)).toOption.isNone
#guard (S.step (.lolliR p q) ([] ⨾ [p ⊸ q] ⟹ r)).toOption.isNone
-- &L₁, &L₂
#guard (S.step (.withL₁ p q) ([] ⨾ [r, p & q] ⟹ s)).toOption == some [[] ⨾ [p, r] ⟹ s]
#guard (S.step (.withL₂ p q) ([] ⨾ [r, p & q] ⟹ s)).toOption == some [[] ⨾ [q, r] ⟹ s]
#guard (S.step (.withL₁ p q) ([] ⨾ [r, q & p] ⟹ s)).toOption.isNone
#guard (S.step (.withL₂ p q) ([] ⨾ [r] ⟹ p & q)).toOption.isNone
-- &R: the same linear zone in both premises
#guard (S.step (.withR p q) ([] ⨾ [r] ⟹ p & q)).toOption
  == some [[] ⨾ [r] ⟹ p, [] ⨾ [r] ⟹ q]
#guard (S.step (.withR p q) ([] ⨾ [r] ⟹ p ⊕ q)).toOption.isNone
-- ⊤R: any linear zone
#guard (S.step .topR ([] ⨾ [p, q] ⟹ ⊤)).toOption == some []
#guard (S.step .topR ([] ⨾ [⊤] ⟹ p)).toOption.isNone
-- 0L: any conclusion; `0` must be linear
#guard (S.step .zeroL ([] ⨾ [p, 𝟎] ⟹ q)).toOption == some []
#guard (S.step .zeroL ([] ⨾ [p] ⟹ 𝟎)).toOption.isNone
#guard (S.step .zeroL ([𝟎] ⨾ [] ⟹ q)).toOption.isNone
-- ⊕L, ⊕R₁, ⊕R₂
#guard (S.step (.plusL p q) ([] ⨾ [r, p ⊕ q] ⟹ s)).toOption
  == some [[] ⨾ [p, r] ⟹ s, [] ⨾ [q, r] ⟹ s]
#guard (S.step (.plusL p q) ([] ⨾ [r] ⟹ p ⊕ q)).toOption.isNone
#guard (S.step (.plusR₁ p q) ([] ⨾ [r] ⟹ p ⊕ q)).toOption == some [[] ⨾ [r] ⟹ p]
#guard (S.step (.plusR₂ p q) ([] ⨾ [r] ⟹ p ⊕ q)).toOption == some [[] ⨾ [r] ⟹ q]
#guard (S.step (.plusR₁ p q) ([] ⨾ [r] ⟹ q ⊕ p)).toOption.isNone
#guard (S.step (.plusR₂ p q) ([] ⨾ [p ⊕ q] ⟹ r)).toOption.isNone
-- !L: `A` goes to the head of the unrestricted zone; one occurrence of
-- `!A` is removed
#guard (S.step (.bangL p) ([s] ⨾ [r, !p] ⟹ q)).toOption == some [[p, s] ⨾ [r] ⟹ q]
#guard (S.step (.bangL p) ([] ⨾ [!p, !p] ⟹ q)).toOption == some [[p] ⨾ [!p] ⟹ q]
#guard (S.step (.bangL p) ([] ⨾ [p] ⟹ q)).toOption.isNone
#guard (S.step (.bangL p) ([] ⨾ [] ⟹ !p)).toOption.isNone
-- !R: the linear zone is empty
#guard (S.step (.bangR p) ([p] ⨾ [] ⟹ !p)).toOption == some [[p] ⨾ [] ⟹ p]
#guard (S.step (.bangR p) ([] ⨾ [p] ⟹ !p)).toOption.isNone
#guard (S.step (.bangR p) ([] ⨾ [!p] ⟹ !p)).toOption.isNone
#guard (S.step (.bangR p) ([p] ⨾ [] ⟹ p)).toOption.isNone
-- cut: the zone named goes to the premise that proves `A`
#guard (S.step (.cut p [q]) ([] ⨾ [q, r] ⟹ s)).toOption
  == some [[] ⨾ [q] ⟹ p, [] ⨾ [p, r] ⟹ s]
#guard (S.step (.cut p []) ([] ⨾ [q, r] ⟹ s)).toOption
  == some [[] ⨾ [] ⟹ p, [] ⨾ [p, q, r] ⟹ s]
#guard (S.step (.cut p [q, q]) ([] ⨾ [q, r] ⟹ s)).toOption.isNone
#guard (S.step (.cut p [s]) ([s] ⨾ [q] ⟹ r)).toOption.isNone
-- cut!: the first premise has an empty linear zone; it always applies
#guard (S.step (.cutU p) ([s] ⨾ [q] ⟹ r)).toOption
  == some [[s] ⨾ [] ⟹ p, [p, s] ⨾ [q] ⟹ r]
#guard (S.step (.cutU p) ([] ⨾ [] ⟹ 𝟎)).toOption == some [[] ⨾ [] ⟹ p, [p] ⨾ [] ⟹ 𝟎]
-- one step reduces in the kernel
example : (S.step (.tensorR p q [p]) ([s] ⨾ [p, q, r] ⟹ p ⊗ q)).toOption
    = some [[s] ⨾ [p] ⟹ p, [s] ⨾ [q, r] ⟹ q] := by
  decide +kernel
example : (S.step .oneR ([] ⨾ [p] ⟹ 𝟏)).toOption = none := by decide +kernel

/-! ## 2. What the sources assert, by the tactic

The derivations of `DILL/Source.lean`, each cited there, at letters. -/

/-- CCP p. 16: `Γ, A ; · ⟹ A`. -/
def copyInit : Der S ([p] ⨾ [] ⟹ p) := by
  dillmove copy p
  dillmove init

/-- CCP p. 16: `Γ ; A, A ⊸ B ⟹ B`. -/
def modusPonens : Der S ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove lolliL p q [p]
  dillmove init
  dillmove init

/-- CCP p. 17: `Γ ; A & B ⟹ A`. -/
def withFst : Der S ([] ⨾ [p & q] ⟹ p) := by
  dillmove withL₁ p q
  dillmove init

/-- The premise of the inversion below: `· ; (p ⊸ q) & r ⟹ p ⊸ q`. -/
def invPremise : Der S ([] ⨾ [(p ⊸ q) & r] ⟹ p ⊸ q) := by
  dillmove withL₁ (p ⊸ q) r
  dillmove init

/-- CCP p. 18, the inversion of ⊸R by cut: from `· ; (p ⊸ q) & r ⟹ p ⊸ q`
to `· ; p, (p ⊸ q) & r ⟹ q`. -/
def lolliRInv : Der S ([] ⨾ [p, (p ⊸ q) & r] ⟹ q) := by
  dillmove cut (p ⊸ q) [(p ⊸ q) & r]
  dillmove withL₁ (p ⊸ q) r
  dillmove init
  dillmove lolliL p q [p]
  dillmove init
  dillmove init

/-- `· ; !A ⟹ A`. -/
def bangDerelict : Der S ([] ⨾ [!p] ⟹ p) := by
  dillmove bangL p
  dillmove copy p
  dillmove init

/-- `· ; !A ⟹ !!A`. -/
def bangDig : Der S ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove bangL p
  dillmove bangR (!p)
  dillmove bangR p
  dillmove copy p
  dillmove init

/-- `· ; !A ⟹ !A ⊗ !A`. -/
def bangContract : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove bangL p
  dillmove tensorR (!p) (!p) []
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove bangR p
  dillmove copy p
  dillmove init

/-- `· ; !A ⟹ 1`. -/
def bangWeaken : Der S ([] ⨾ [!p] ⟹ 𝟏) := by
  dillmove bangL p
  dillmove oneR

/-- `· ; !(A & B) ⟹ !A ⊗ !B`. -/
def bangWithTensor : Der S ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) := by
  dillmove bangL (p & q)
  dillmove tensorR (!p) (!q) []
  dillmove bangR p
  dillmove copy (p & q)
  dillmove withL₁ p q
  dillmove init
  dillmove bangR q
  dillmove copy (p & q)
  dillmove withL₂ p q
  dillmove init

/-- `· ; !A ⊗ !B ⟹ !(A & B)`. -/
def bangTensorWith : Der S ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) := by
  dillmove tensorL (!p) (!q)
  dillmove bangL p
  dillmove bangL q
  dillmove bangR (p & q)
  dillmove withR p q
  dillmove copy p
  dillmove init
  dillmove copy q
  dillmove init

/-- `· ; !A, !(A ⊸ B) ⟹ !B`. -/
def bangMap : Der S ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) := by
  dillmove bangL p
  dillmove bangL (p ⊸ q)
  dillmove bangR q
  dillmove copy (p ⊸ q)
  dillmove lolliL p q []
  dillmove copy p
  dillmove init
  dillmove init

/-! ## 3. The known non-theorems of the plan, each as far as it goes -/

-- `· ; · ⟹ 0` (Pfenning 3.11).  Predicted: a query where no move applies
/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [] ⟹ 𝟎) := by
  dillmove

-- `· ; p ⟹ 1`: no linear weakening.  Predicted: 1R refused
/-- error: the move does not apply to goal 0: 1R: the linear zone is not empty -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ 𝟏) := by
  dillmove oneR

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ 𝟏) := by
  dillmove

-- `· ; p, q ⟹ p`: no linear weakening.  Predicted: init refused
/--
error: the move does not apply to goal 0: init: the linear zone is not exactly the conclusion
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, q] ⟹ p) := by
  dillmove init

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p, q] ⟹ p) := by
  dillmove

-- `· ; p ⟹ p ⊗ p`: no linear contraction.  Predicted: every division of
-- the zone leaves a premise where no move applies.  There are two
-- divisions; each leaves `· ; · ⟹ p`
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove tensorR p p []
  [apply] dillmove tensorR p p [p]
---
info:   · ; p ⟹ p ⊗ p   by ⊗R p ⊗ p [p]
    · ; p ⟹ p   by init
>   ? · ; · ⟹ p
  at 1: open goal 0; 1 open in all
---
error: dillmove: no move applies at goal 0
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove
  dillmove tensorR p p [p]
  dillmove init
  dillmove where
  dillmove

/--
info:   · ; p ⟹ p ⊗ p   by ⊗R p ⊗ p []
>   ? · ; · ⟹ p
    ? · ; p ⟹ p
  at 0: open goal 0; 2 open in all
---
error: dillmove: no move applies at goal 0
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove tensorR p p []
  dillmove where
  dillmove

-- the division that would use `p` twice is refused
/--
error: the move does not apply to goal 0: ⊗R: the zone named for the first premise is not part of the linear zone
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove tensorR p p [p, p]

-- `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)` (Pfenning p. 60).  Predicted:
-- attempts that stay open.  Three first moves apply.  With the
-- implication given to the first premise of ⊗R, the attempt stops at
-- `· ; q, r ⟹ q` and `· ; · ⟹ p ⊸ r`
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove tensorR (p ⊸ q) (p ⊸ r) []
  [apply] dillmove tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)]
  [apply] dillmove lolliL p (q ⊗ r) []
---
info:   · ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)   by ⊗R (p ⊸ q) ⊗ (p ⊸ r) [p ⊸ (q ⊗ r)]
    · ; p ⊸ (q ⊗ r) ⟹ p ⊸ q   by ⊸R p ⊸ q
      · ; p, p ⊸ (q ⊗ r) ⟹ q   by ⊸L p ⊸ (q ⊗ r) [p]
        · ; p ⟹ p   by init
        · ; q ⊗ r ⟹ q   by ⊗L q ⊗ r
>         ? · ; q, r ⟹ q
    ? · ; · ⟹ p ⊸ r
  at 0.0.1.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove
  dillmove tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)]
  dillmove lolliR p q
  dillmove lolliL p (q ⊗ r) [p]
  dillmove init
  dillmove tensorL q r
  dillmove where
  all_goals leave_open

-- at `· ; q, r ⟹ q` no move applies
/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)]
  dillmove lolliR p q
  dillmove lolliL p (q ⊗ r) [p]
  dillmove init
  dillmove tensorL q r
  dillmove

-- with the implication given to the second premise, the first is
-- `· ; · ⟹ p ⊸ q`, and stops at `· ; p ⟹ q`
/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove tensorR (p ⊸ q) (p ⊸ r) []
  dillmove lolliR p q
  dillmove

-- with ⊸L first, its first premise is `· ; · ⟹ p`
/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove lolliL p (q ⊗ r) []
  dillmove

-- `· ; p ⟹ !p`: !R needs an empty linear zone.  Predicted: !R refused
/-- error: the move does not apply to goal 0: !R: the linear zone is not empty -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ !p) := by
  dillmove bangR p

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ !p) := by
  dillmove

-- `· ; p ⊕ q ⟹ p`: the additives.  Predicted: an open premise
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove plusL p q
---
info:   · ; p ⊕ q ⟹ p   by ⊕L p ⊕ q
    · ; p ⟹ p   by init
>   ? · ; q ⟹ p
  at 1: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊕ q] ⟹ p) := by
  dillmove
  dillmove plusL p q
  dillmove init
  dillmove where
  all_goals leave_open

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊕ q] ⟹ p) := by
  dillmove plusL p q
  dillmove init
  dillmove

-- `· ; p ⟹ p & q`.  Predicted: an open premise
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove withR p q
---
info:   · ; p ⟹ p & q   by &R p & q
    · ; p ⟹ p   by init
>   ? · ; p ⟹ q
  at 1: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p & q) := by
  dillmove
  dillmove withR p q
  dillmove init
  dillmove where
  all_goals leave_open

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p & q) := by
  dillmove withR p q
  dillmove init
  dillmove

-- `· ; !p ⊸ q ⟹ p ⊸ q`.  Predicted: copy is always offered, and the
-- attempt stays open.  Not so at this sequent: `!p` is to be proved, never
-- a hypothesis, so nothing reaches the unrestricted zone and no copy is
-- offered; each division at ⊸L stops where no move applies
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove lolliR p q
  [apply] dillmove lolliL (!p) q []
---
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove lolliL (!p) q []
  [apply] dillmove lolliL (!p) q [p]
---
info:   · ; !p ⊸ q ⟹ p ⊸ q   by ⊸R p ⊸ q
    · ; p, !p ⊸ q ⟹ q   by ⊸L !p ⊸ q [p]
>     ? · ; p ⟹ !p
      ? · ; q ⟹ q
  at 0.0: open goal 0; 2 open in all
---
error: the move does not apply to goal 0: !R: the linear zone is not empty
-/
#guard_msgs in
example : Att S true ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) := by
  dillmove
  dillmove lolliR p q
  dillmove
  dillmove lolliL (!p) q [p]
  dillmove where
  dillmove bangR p

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) := by
  dillmove lolliR p q
  dillmove lolliL (!p) q [p]
  dillmove

/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) := by
  dillmove lolliR p q
  dillmove lolliL (!p) q []
  dillmove bangR p
  dillmove

-- "and the like with `!` on the left": `· ; !(p ⊸ q) ⟹ q`.  Here the
-- prediction holds: after !L, copy is offered at every sequent, so no
-- query is ever an error and the attempt stays open
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove bangL (p ⊸ q)
---
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove copy (p ⊸ q)
---
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove lolliL p q []
  [apply] dillmove copy (p ⊸ q)
---
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove copy (p ⊸ q)
---
info:   · ; !(p ⊸ q) ⟹ q   by !L !(p ⊸ q)
    p ⊸ q ; · ⟹ q   by copy (p ⊸ q)
      p ⊸ q ; p ⊸ q ⟹ q   by ⊸L p ⊸ q []
>       ? p ⊸ q ; · ⟹ p
        ? p ⊸ q ; q ⟹ q
  at 0.0.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [!(p ⊸ q)] ⟹ q) := by
  dillmove
  dillmove bangL (p ⊸ q)
  dillmove
  dillmove copy (p ⊸ q)
  dillmove
  dillmove lolliL p q []
  dillmove
  dillmove where
  all_goals leave_open

-- All the attempts at once.  `offered n j`: some tree of the moves that
-- the tactic offers (`candidates`: every rule but the cuts), of depth at
-- most `n`, derives `j`.  While the unrestricted zone is empty no copy
-- applies and every premise is smaller than its conclusion, so a tree is
-- no deeper than its sequent is large: 12 covers each sequent below but
-- the last.  This is a test of the moves offered, and no proof that a
-- sequent has no derivation: that is the search's to give
def offered : Nat → Seq → Bool
  | 0, _ => false
  | n + 1, j => (candidates j).any fun m =>
      match S.step m j with
      | .ok ps => ps.all (offered n)
      | .error _ => false

-- it finds the derivations of section 2, at their heights and no lower
#guard offered 2 ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard !offered 1 ([] ⨾ [p, p ⊸ q] ⟹ q)
#guard offered 7 ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q))
#guard !offered 6 ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q))
#guard offered 7 ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q)
#guard !offered 6 ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q)
-- and none of a non-theorem
#guard !offered 12 ([] ⨾ [] ⟹ 𝟎)
#guard !offered 12 ([] ⨾ [p] ⟹ 𝟏)
#guard !offered 12 ([] ⨾ [p, q] ⟹ p)
#guard !offered 12 ([] ⨾ [p] ⟹ p ⊗ p)
#guard !offered 12 ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))
#guard !offered 12 ([] ⨾ [p] ⟹ !p)
#guard !offered 12 ([] ⨾ [p ⊕ q] ⟹ p)
#guard !offered 12 ([] ⨾ [p] ⟹ p & q)
#guard !offered 12 ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q)
-- with a valid hypothesis a copy always applies, and there is no bound:
-- none to depth 8
#guard !offered 8 ([] ⨾ [!(p ⊸ q)] ⟹ q)
-- the same, reduced by the kernel
example : offered 12 ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) = false := by
  decide +kernel
example : offered 12 ([] ⨾ [p] ⟹ p ⊗ p) = false := by decide +kernel

/-! ## 4. The other refusals of `step`, each seen once

⊗R, 1R, ⊸L and !R each ask two things, and each says which one failed.
Section 3 has the refusal of init, and one of the two of each of ⊗R, 1R
and !R (the zone).  Here are the others.  cut! is never refused. -/

-- 1R at an empty linear zone, the conclusion not `1`
/-- error: the move does not apply to goal 0: 1R: the conclusion is not 1 -/
#guard_msgs in
example : Att S true ([] ⨾ [] ⟹ p) := by
  dillmove oneR

-- !R at an empty linear zone, the conclusion not `!p`
/-- error: the move does not apply to goal 0: !R: the conclusion is not this formula -/
#guard_msgs in
example : Att S true ([p] ⨾ [] ⟹ p) := by
  dillmove bangR p

-- ⊸L where the implication is not in the linear zone
/-- error: the move does not apply to goal 0: ⊸L: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove lolliL p q []

-- where both conditions fail, the conclusion is named
/-- error: the move does not apply to goal 0: !R: the conclusion is not this formula -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove bangR p

/-- error: the move does not apply to goal 0: 1R: the conclusion is not 1 -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove oneR

/-- error: the move does not apply to goal 0: ⊗R: the conclusion is not this tensor -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove tensorR p q [r]

/-- error: the move does not apply to goal 0: ⊸L: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove lolliL p q [r]

/-- error: the move does not apply to goal 0: copy: the formula is not in the unrestricted zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove copy p

/-- error: the move does not apply to goal 0: ⊗L: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove tensorL p q

/-- error: the move does not apply to goal 0: ⊗R: the conclusion is not this tensor -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove tensorR p q []

/-- error: the move does not apply to goal 0: 1L: 1 is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove oneL

/--
error: the move does not apply to goal 0: ⊸L: the zone named for the first premise is not part of the rest of the linear zone
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove lolliL p q [p, p]

/-- error: the move does not apply to goal 0: ⊸R: the conclusion is not this implication -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove lolliR p q

/-- error: the move does not apply to goal 0: &L₁: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove withL₁ p q

/-- error: the move does not apply to goal 0: &L₂: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove withL₂ p q

/-- error: the move does not apply to goal 0: &R: the conclusion is not this formula -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove withR p q

/-- error: the move does not apply to goal 0: ⊤R: the conclusion is not ⊤ -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove topR

/-- error: the move does not apply to goal 0: 0L: 0 is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove zeroL

/-- error: the move does not apply to goal 0: ⊕L: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove plusL p q

/-- error: the move does not apply to goal 0: ⊕R₁: the conclusion is not this formula -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove plusR₁ p q

/-- error: the move does not apply to goal 0: ⊕R₂: the conclusion is not this formula -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove plusR₂ p q

/-- error: the move does not apply to goal 0: !L: the formula is not in the linear zone -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove bangL p

/--
error: the move does not apply to goal 0: cut: the zone named for the first premise is not part of the linear zone
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ q) := by
  dillmove cut r [q]

/-! ## 5, 6. A query, a pattern, the goal as the infoview shows it, and
where the proof is

In order: a query; a pattern that one move fills (it is made, and shown
as "Try this"); a pattern that four moves fill (each is offered); a query
by the beginning of a name; a pattern with holes that one move fills; the
attempt as `where` draws it; and last the goal after the ⊗L, as
`trace_state` printed it. -/

/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove tensorL p q
  [apply] dillmove tensorR q p []
  [apply] dillmove tensorR q p [p ⊗ q]
---
info: Try this:
  [apply] dillmove tensorL p q
---
info: dillmove: 4 moves of this form apply at goal 0; no move is made. Try these:
  [apply] dillmove tensorR q p []
  [apply] dillmove tensorR q p [q]
  [apply] dillmove tensorR q p [p]
  [apply] dillmove tensorR q p [p, q]
---
info: dillmove: at goal 0, 4 moves whose names begin with `te` apply; no move is made. Try these:
  [apply] dillmove tensorR q p []
  [apply] dillmove tensorR q p [q]
  [apply] dillmove tensorR q p [p]
  [apply] dillmove tensorR q p [p, q]
---
info: Try this:
  [apply] dillmove tensorR q p [q]
---
info:   · ; p ⊗ q ⟹ q ⊗ p   by ⊗L p ⊗ q
    · ; p, q ⟹ q ⊗ p   by ⊗R q ⊗ p [q]
>     ? · ; q ⟹ q
      ? · ; p ⟹ p
  at 0.0: open goal 0; 2 open in all
---
trace: ⊢ Att S   · ; p, q ⟹ q ⊗ p
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) := by
  dillmove
  dillmove tensorL
  trace_state
  dillmove tensorR
  dillmove te
  dillmove tensorR _ _ [q]
  dillmove where
  all_goals leave_open

-- a pattern that no move fills, and a query at a goal that is not there
/--
error: dillmove: no candidate move of this form applies at goal 0; write its arguments out, or `dillmove` alone to see the moves that apply
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) := by
  dillmove bangL

/-- error: there is no goal 1: the open goals are 0 to 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) := by
  dillmove at 1

-- a move at goal 1: the second premise of ⊗R first
/--
info:   · ; p, q ⟹ q ⊗ p   by ⊗R q ⊗ p [q]
>   ? · ; q ⟹ q
    · ; p ⟹ p   by init
  at 0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, q] ⟹ q ⊗ p) := by
  dillmove tensorR q p [q]
  dillmove init at 1
  dillmove where
  all_goals leave_open

/-! ## 7. The certificates, checked with no tactic; corrupted ones, rejected -/

def treeCert := Cert.certifier step_sound
def scriptCert := certifier step_sound

/-- info: R3 passes: the evaluation path of treeCert is structural -/
#guard_msgs in
#certify_structural DILL.Test.treeCert

/-- info: R2 passes: the property of treeCert mentions no budget -/
#guard_msgs in
#certify_statement DILL.Test.treeCert

/--
info: R3 passes: the evaluation path of scriptCert is structural
---
info: R3 note: the evaluation path of scriptCert reaches 1 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Nat.repr [Init.Data.Repr]: @[implemented_by]: the compiled code is not the definition
    via [DILL.Test.scriptCert,
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
#certify_structural DILL.Test.scriptCert

/-- info: R2 passes: the property of scriptCert mentions no budget -/
#guard_msgs in
#certify_statement DILL.Test.scriptCert

/-- The tree of moves of `bangContract`, written out. -/
def bangContractCert : Cert S :=
  .mk (.bangL p) [.mk (.tensorR (!p) (!p) [])
    [.mk (.bangR p) [.mk (.copy p) [.mk .init []]],
     .mk (.bangR p) [.mk (.copy p) [.mk .init []]]]]

example : bangContract.cert = bangContractCert := rfl

/-- The script of `bangContract`, written out: its lines by the tactic. -/
def bangContractScript : Script S :=
  [⟨0, .bangL p⟩, ⟨0, .tensorR (!p) (!p) []⟩, ⟨0, .bangR p⟩, ⟨0, .copy p⟩, ⟨0, .init⟩,
   ⟨0, .bangR p⟩, ⟨0, .copy p⟩, ⟨0, .init⟩]

example : bangContract.script = bangContractScript := rfl

/-- The kernel checks the tree; the result is the derivation. -/
def bangContractByTree : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  treeCert.verdict _ bangContractCert

/-- The kernel runs the script; the result is the derivation. -/
def bangContractByScript : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  scriptCert.verdict _ bangContractScript

-- the two checks themselves, reduced by the kernel; and the derivation of
-- the proof system from each, with no tactic of the explorer
example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractCert = true := by decide +kernel
example : derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractScript = true := by decide +kernel

example : Der.ofCert ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractCert (by decide +kernel)
    = bangContract := rfl

/-- The derivation of the proof system, from the script. -/
def bangContractOfScript : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  Der.ofScript _ bangContractScript (by decide +kernel)

-- a wrong move: ⊗R before !L.  `!p` goes to one premise, and the other
-- is `· ; · ⟹ !p`, where after !R there is nothing to copy
theorem bad_tree_rejected :
    treeCert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
      (.mk (.tensorR (!p) (!p) [!p])
        [.mk .init [], .mk (.bangR p) [.mk (.copy p) [.mk .init []]]]) = false := by
  decide +kernel

-- a wrong division: ⊸L with nothing for the premise that proves `p`
theorem bad_split_rejected :
    treeCert.check ([] ⨾ [p, p ⊸ q] ⟹ q)
      (.mk (.lolliL p q []) [.mk .init [], .mk .init []]) = false := by
  decide +kernel

-- the right division, for comparison
example : treeCert.check ([] ⨾ [p, p ⊸ q] ⟹ q)
    (.mk (.lolliL p q [p]) [.mk .init [], .mk .init []]) = true := by
  decide +kernel

-- a tree that stops early: the second premise of ⊗R has no subtree
theorem short_tree_rejected :
    treeCert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
      (.mk (.bangL p) [.mk (.tensorR (!p) (!p) [])
        [.mk (.bangR p) [.mk (.copy p) [.mk .init []]]]]) = false := by
  decide +kernel

-- a script with a wrong line: the last copy is of `q`
theorem bad_script_rejected :
    scriptCert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
      [⟨0, .bangL p⟩, ⟨0, .tensorR (!p) (!p) []⟩, ⟨0, .bangR p⟩, ⟨0, .copy p⟩, ⟨0, .init⟩,
       ⟨0, .bangR p⟩, ⟨0, .copy q⟩, ⟨0, .init⟩] = false := by
  decide +kernel

-- a script that stops early
theorem short_script_rejected :
    scriptCert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) (bangContractScript.take 7) = false := by
  decide +kernel

-- the same certifier at the proposition
example : Derivable ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  (Cert.certifier step_sound_derivable.soundT).verdict _ bangContractCert

/-! ## 8. A derivation, walked: by the command, and as a tactic block -/

set_option walk.offer false in
/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
>   p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
      0: p ; · ⟹ !p   by !R !p   [closed]
      1: p ; · ⟹ !p   by !R !p   [closed]
  at 0: 2 premises; no open goals
-/
#guard_msgs in
#walk bangContract down 0

set_option walk.offer false in
/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
      p ; · ⟹ !p   by !R !p
>       p ; · ⟹ p   by copy p
          0: p ; p ⟹ p   by init   [closed]
  at 0.1.0: 1 premise; no open goals
-/
#guard_msgs in
#walk bangContract down 0 down 1 down 0

-- with the motions offered
/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
>     p ; · ⟹ !p   by !R !p
        0: p ; · ⟹ p   by copy p   [closed]
  at 0.0: 1 premise; no open goals
---
info: Motions from here:
  [apply] down 0
  [apply] up
  [apply] right
  [apply] top
-/
#guard_msgs in
#walk bangContract down 0 down 0

/--
trace: ⊢ Walk bangContract
      · ; !p ⟹ !p ⊗ !p   by !L !p
    >   p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
          0: p ; · ⟹ !p   by !R !p   [closed]
          1: p ; · ⟹ !p   by !R !p   [closed]
      at 0: 2 premises; no open goals
-/
#guard_msgs in
example : Walk bangContract := by
  down 0
  trace_state

/-! ## 9. A derivation, mapped out to the family

`famOfDer d` is equal by `rfl` to the same derivation written with the
constructors of `Fam true`; and to the derivation of `DILL/Source.lean`,
which is in the calculus without cut, lifted. -/

example : famOfDer modusPonens =
    .lolliL p q [p] [] (by decide) (.init p (by decide)) (.init q (by decide)) := rfl

example : famOfDer bangContract =
    .bangL p [] (by decide)
      (.tensorR [] [] (by decide)
        (.bangR (by decide) (.copy p (by decide) (.init p (by decide))))
        (.bangR (by decide) (.copy p (by decide) (.init p (by decide))))) := rfl

example : bangContractByTree = famOfDer bangContract := rfl

/-- `Eq.refl`, given to the kernel unchecked by the elaborator.  The
derivation that the script's certifier gives is the same one again, and
the kernel accepts it at once; the elaborator's `rfl` does not reach it
(with no limit set it was stopped after 110 seconds). -/
local elab "rfl_by_kernel" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some (_, a, _) := (← Lean.Meta.whnfR (← g.getType)).eq?
    | throwError "rfl_by_kernel: the goal is not an equation"
  g.assign (← Lean.Meta.mkEqRefl a)

example : bangContractByScript = famOfDer bangContract := by rfl_by_kernel

-- the kernel does check: a false equation is refused by it
/--
error: (kernel) declaration type mismatch, 'DILL.Test._example' has type
  (famOfDer bangContract).height = (famOfDer bangContract).height
but it is expected to have type
  (famOfDer bangContract).height = 6
-/
#guard_msgs in
example : (famOfDer bangContract).height = 6 := by rfl_by_kernel

example : (famOfDer bangContract).height = 5 := by decide +kernel

example : famOfDer copyInit = Source.copyInit.lift := rfl
example : famOfDer modusPonens = Source.modusPonens.lift := rfl
example : famOfDer withFst = Source.withFst.lift := rfl
example : famOfDer bangDerelict = Source.bangDerelict.lift := rfl
example : famOfDer bangDig = Source.bangDig.lift := rfl
example : famOfDer bangContract = Source.bangContract.lift := rfl
example : famOfDer bangWeaken = Source.bangWeaken.lift := rfl
example : famOfDer bangWithTensor = Source.bangWithTensor.lift := rfl
example : famOfDer bangTensorWith = Source.bangTensorWith.lift := rfl
example : famOfDer bangMap = Source.bangMap.lift := rfl
-- the derivation with a cut: the source's function, applied to the
-- premise mapped out
example : famOfDer lolliRInv = Source.lolliRInv (famOfDer invPremise) := rfl
example : (famOfDer lolliRInv).height = 3 := rfl

/-! ## 10. The exercises of `Play/DILL.lean`, by script

For each: the moves offered at its first step, and its outcome: a script
that derives it, or where a non-theorem stops. -/

-- 1: `· ; p ⟹ p` and `p ; · ⟹ p`
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove init
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p) := by
  dillmove
  all_goals leave_open

/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove copy p
-/
#guard_msgs in
example : Att S true ([p] ⨾ [] ⟹ p) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [p] ⟹ p) [⟨0, .init⟩]
#guard derives S ([p] ⨾ [] ⟹ p) copyInit.script
-- init alone does not close the second: the valid `p` is not linear
#guard !derives S ([p] ⨾ [] ⟹ p) [⟨0, .init⟩]

-- 2: `· ; p, p ⊸ q ⟹ q`
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove lolliL p q []
  [apply] dillmove lolliL p q [p]
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [p, p ⊸ q] ⟹ q) modusPonens.script
-- the other division does not close: its first premise is `· ; · ⟹ p`,
-- where init is refused (line 1 of the script)
#guard (run S ([] ⨾ [p, p ⊸ q] ⟹ q) [⟨0, .lolliL p q []⟩, ⟨0, .init⟩]).2.map (·.1) == some 1
#guard (run S ([] ⨾ [p, p ⊸ q] ⟹ q) [⟨0, .lolliL p q []⟩, ⟨0, .init⟩]).1.goals
  == [[] ⨾ [] ⟹ p, [] ⨾ [q, p] ⟹ q]

-- 3: `· ; p & q ⟹ p` and `· ; p ⊗ q ⟹ q ⊗ p`
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove withL₁ p q
  [apply] dillmove withL₂ p q
-/
#guard_msgs in
example : Att S true ([] ⨾ [p & q] ⟹ p) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [p & q] ⟹ p) withFst.script
-- &L₂ leaves `· ; q ⟹ p`, where init is refused
#guard (run S ([] ⨾ [p & q] ⟹ p) [⟨0, .withL₂ p q⟩, ⟨0, .init⟩]).2.map (·.1) == some 1
#guard (run S ([] ⨾ [p & q] ⟹ p) [⟨0, .withL₂ p q⟩, ⟨0, .init⟩]).1.goals == [[] ⨾ [q] ⟹ p]

-- the first query of `· ; p ⊗ q ⟹ q ⊗ p` is in section 5
/-- ⊗ is commutative. -/
def tensorComm : Der S ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) := by
  dillmove tensorL p q
  dillmove tensorR q p [q]
  dillmove init
  dillmove init

#guard derives S ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) tensorComm.script
-- ⊗R before ⊗L: `p ⊗ q` goes whole to one premise; what is left open
#guard !derives S ([] ⨾ [p ⊗ q] ⟹ q ⊗ p)
  [⟨0, .tensorR q p [p ⊗ q]⟩, ⟨0, .tensorL p q⟩]
#guard (run S ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) [⟨0, .tensorR q p [p ⊗ q]⟩, ⟨0, .tensorL p q⟩]).1.goals
  == [[] ⨾ [p, q] ⟹ q, [] ⨾ [] ⟹ p]

-- 4: `· ; p ⊸ (q ⊸ r) ⟹ (p ⊗ q) ⊸ r`
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove lolliR (p ⊗ q) r
  [apply] dillmove lolliL p (q ⊸ r) []
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) := by
  dillmove
  all_goals leave_open

/-- Uncurrying. -/
def uncurry : Der S ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) := by
  dillmove lolliR (p ⊗ q) r
  dillmove tensorL p q
  dillmove lolliL p (q ⊸ r) [p]
  dillmove init
  dillmove lolliL q r [q]
  dillmove init
  dillmove init

#guard derives S ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) uncurry.script

-- 5: `· ; p ⊗ (q ⊕ r) ⟹ (p ⊗ q) ⊕ (p ⊗ r)`
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove tensorL p (q ⊕ r)
  [apply] dillmove plusR₁ (p ⊗ q) (p ⊗ r)
  [apply] dillmove plusR₂ (p ⊗ q) (p ⊗ r)
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r)) := by
  dillmove
  all_goals leave_open

/-- ⊗ distributes over ⊕, one half. -/
def distrib : Der S ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r)) := by
  dillmove tensorL p (q ⊕ r)
  dillmove plusL q r
  dillmove plusR₁ (p ⊗ q) (p ⊗ r)
  dillmove tensorR p q [p]
  dillmove init
  dillmove init
  dillmove plusR₂ (p ⊗ q) (p ⊗ r)
  dillmove tensorR p r [p]
  dillmove init
  dillmove init

#guard derives S ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r)) distrib.script
-- ⊕R₁ before ⊕L: the branch for `r` is left with `· ; r ⟹ q`
#guard (run S ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r))
  [⟨0, .tensorL p (q ⊕ r)⟩, ⟨0, .plusR₁ (p ⊗ q) (p ⊗ r)⟩, ⟨0, .plusL q r⟩,
   ⟨0, .tensorR p q [p]⟩, ⟨0, .init⟩, ⟨0, .init⟩, ⟨0, .tensorR p q [p]⟩, ⟨0, .init⟩]).1.goals
  == [[] ⨾ [r] ⟹ q]

-- 6: `· ; p, (p ⊸ q) & r ⟹ q`, with the cut and without it
/--
info:   · ; p, (p ⊸ q) & r ⟹ q   by cut (p ⊸ q) [(p ⊸ q) & r]
>   ? · ; (p ⊸ q) & r ⟹ p ⊸ q
    ? · ; p ⊸ q, p ⟹ q
  at 0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, (p ⊸ q) & r] ⟹ q) := by
  dillmove cut (p ⊸ q) [(p ⊸ q) & r]
  dillmove where
  all_goals leave_open

#guard derives S ([] ⨾ [p, (p ⊸ q) & r] ⟹ q) lolliRInv.script
#guard derives S ([] ⨾ [p, (p ⊸ q) & r] ⟹ q)
  [⟨0, .withL₁ (p ⊸ q) r⟩, ⟨0, .lolliL p q [p]⟩, ⟨0, .init⟩, ⟨0, .init⟩]

-- 7: `· ; p, q ⟹ p` and `· ; p ⟹ p ⊗ p`: section 3 has the messages of
-- both, and where each division of the second stops
#guard (run S ([] ⨾ [p] ⟹ p ⊗ p) [⟨0, .tensorR p p [p]⟩, ⟨0, .init⟩]).1.goals
  == [[] ⨾ [] ⟹ p]
#guard (run S ([] ⨾ [p] ⟹ p ⊗ p) [⟨0, .tensorR p p []⟩, ⟨1, .init⟩]).1.goals
  == [[] ⨾ [] ⟹ p]

-- 8: `· ; !p ⟹ p`, `· ; !p ⟹ 1`, `· ; !p ⟹ !p ⊗ !p`
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove bangL p
---
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove copy p
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ p) := by
  dillmove
  dillmove bangL p
  dillmove
  all_goals leave_open

/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove bangL p
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ 𝟏) := by
  dillmove
  all_goals leave_open

/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove bangL p
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove tensorR (!p) (!p) [!p]
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [!p] ⟹ p) bangDerelict.script
#guard derives S ([] ⨾ [!p] ⟹ 𝟏) bangWeaken.script
#guard derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContract.script
-- ⊗R before !L: `!p` goes to one premise only, and the other is left
-- with `· ; · ⟹ p`
#guard (run S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
  [⟨0, .tensorR (!p) (!p) [!p]⟩, ⟨0, .init⟩, ⟨0, .bangR p⟩]).1.goals == [[] ⨾ [] ⟹ p]

-- 9: `· ; !p ⟹ !!p`, and `· ; p ⟹ !p` (section 3 has its messages)
/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove bangL p
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove
  all_goals leave_open

-- !R first is refused: the linear zone is not empty
/-- error: the move does not apply to goal 0: !R: the linear zone is not empty -/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove bangR (!p)

#guard derives S ([] ⨾ [!p] ⟹ !(!p)) bangDig.script
-- a copy between the two !R: the linear zone is no longer empty, and the
-- second !R is refused (line 3 of the script, counted from 0)
#guard (run S ([] ⨾ [!p] ⟹ !(!p))
    [⟨0, .bangL p⟩, ⟨0, .bangR (!p)⟩, ⟨0, .copy p⟩, ⟨0, .bangR p⟩]).2
  == some (3, "the move does not apply to goal 0: !R: the linear zone is not empty")

-- 10: `· ; !(p & q) ⟹ !p ⊗ !q` and `· ; !p ⊗ !q ⟹ !(p & q)`
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove bangL (p & q)
  [apply] dillmove tensorR (!p) (!q) []
  [apply] dillmove tensorR (!p) (!q) [!(p & q)]
-/
#guard_msgs in
example : Att S true ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) := by
  dillmove
  all_goals leave_open

/--
info: dillmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] dillmove tensorL (!p) (!q)
-/
#guard_msgs in
example : Att S true ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) bangWithTensor.script
#guard derives S ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) bangTensorWith.script

-- 11: `· ; !p, !(p ⊸ q) ⟹ !q`
/--
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove bangL p
  [apply] dillmove bangL (p ⊸ q)
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) := by
  dillmove
  all_goals leave_open

#guard derives S ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) bangMap.script

-- 12: `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)`: section 3 has its first
-- query and where the three first moves stop

-- the walk at the end of the file
def d : Der S ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove lolliL p q [p]
  dillmove init
  dillmove init

set_option walk.offer false in
/--
info:   · ; p, p ⊸ q ⟹ q   by ⊸L p ⊸ q [p]
>   · ; p ⟹ p   by init
  at 0: no premises; no open goals
-/
#guard_msgs in
#walk d down 0

set_option walk.offer false in
/--
info:   · ; p, p ⊸ q ⟹ q   by ⊸L p ⊸ q [p]
>   · ; q ⟹ q   by init
  at 1: no premises; no open goals
-/
#guard_msgs in
#walk d down 1

end DILL.Test
