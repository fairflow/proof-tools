/-
What `Play/GLSTutorial.lean` says each step shows, pinned.  The sections
are the tutorial's.  Every message is pasted from Lean's output.
-/
import GLS.Explore

namespace GLS.ExploreTest

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-- The moves that apply at a sequent, as the tactic writes them. -/
def offered (j : Seq) : List String :=
  ((candidates j).filter fun m => (S.step m j).toOption.isSome).map Move.src

/-- What a move leaves, as the goals are shown. -/
def leaves (m : Move) (j : Seq) : Option (List String) :=
  (S.step m j).toOption.map (·.map Seq.show)

/-! ## 1. Building a derivation: the goal after each line -/

def lob : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  glsmove impR □(□p ⟶ p) □p
  glsmove glr p
  glsmove impL □p p
  glsmove glr p
  glsmove idP 0
  glsmove idP 0

#guard leaves (.impR □(□p ⟶ p) □p) ([] ⇒ [□(□p ⟶ p) ⟶ □p]) == some ["□(□p → p) ⇒ □p"]
#guard leaves (.glr p) ([□(□p ⟶ p)] ⇒ [□p]) == some ["□p → p, □(□p → p), □p ⇒ p"]
#guard leaves (.impL □p p) ([□p ⟶ p, □(□p ⟶ p), □p] ⇒ [p])
  == some ["□(□p → p), □p ⇒ □p, p", "p, □(□p → p), □p ⇒ p"]
-- the first: GLR on a □p that is on both sides; its premise has p on both sides
#guard (□p ∈ [□(□p ⟶ p), □p]) && (□p ∈ [□p, p])
#guard leaves (.glr p) ([□(□p ⟶ p), □p] ⇒ [□p, p])
  == some ["□p → p, □(□p → p), p, □p, □p ⇒ p"]
#guard leaves (.idP 0) ([□p ⟶ p, □(□p ⟶ p), p, □p, □p] ⇒ [p]) == some []
#guard leaves (.idP 0) ([p, □(□p ⟶ p), □p] ⇒ [p]) == some []

/-! ## 2. Asking what applies -/

/--
info: glsmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] glsmove impR □(p ⟶ q) (□p ⟶ □q)
---
info: glsmove: at goal 0, 1 move applies; no move is made. Try these:
  [apply] glsmove glr q
---
info:   ⇒ □(p → q) → □p → □q   by ImpR □(p → q) → □p → □q
    □(p → q) ⇒ □p → □q   by ImpR □p → □q
      □p, □(p → q) ⇒ □q   by GLR □q
>       ? p, □p, p → q, □(p → q), □q ⇒ q
  at 0.0.0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove
  glsmove impR □(p ⟶ q) (□p ⟶ □q)
  glsmove impR □p □q
  glsmove
  glsmove glr q
  glsmove where
  all_goals leave_open

/-! ## 3. Patterns: each is filled as the tutorial says -/

/--
info: Try this:
  [apply] glsmove impR □(p ⟶ q) (□p ⟶ □q)
---
info: Try this:
  [apply] glsmove impR □p □q
---
info: Try this:
  [apply] glsmove glr q
---
info: Try this:
  [apply] glsmove impL p q
---
info: Try this:
  [apply] glsmove idP 0
---
info: Try this:
  [apply] glsmove idP 1
-/
#guard_msgs in
def axK : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove impR
  glsmove impR
  glsmove glr
  glsmove impL _ q
  glsmove idP
  glsmove idP

/-! ## 4. A script -/

#guard axK.script.length == 6
#guard derives S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) axK.script
-- the first three lines leave the goal the tutorial names
#guard leaves (.glr q) ([□p, □(p ⟶ q)] ⇒ [□q]) == some ["p, □p, p → q, □(p → q), □q ⇒ q"]

example : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  apply_script axK.script.take 3
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

/-! ## 5. Tactics of the calculus -/

-- `routine` makes the two ImpR and stops before GLR: one goal is left
#guard (routine 20 ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q])).map (·.map fun l => l.move.src)
  == some ["impR □(p ⟶ q) (□p ⟶ □q)", "impR □p □q"]
#guard leaves (.impR □p □q) ([□(p ⟶ q)] ⇒ [□p ⟶ □q]) == some ["□p, □(p → q) ⇒ □q"]
-- and after GLR it closes what is left
#guard derives S ([p, □p, p ⟶ q, □(p ⟶ q), □q] ⇒ [q])
  ((routine 20 ([p, □p, p ⟶ q, □(p ⟶ q), □q] ⇒ [q])).getD [])

example : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  apply_script (routine 20 ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q])).getD []
  glsmove glr q
  apply_script (routine 20 ([p, □p, p ⟶ q, □(p ⟶ q), □q] ⇒ [q])).getD []

def lobByTheSearch : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  apply_script (found ([] ⇒ [□(□p ⟶ p) ⟶ □p])).getD []

#guard lobByTheSearch.script.length == 6
#guard lobByTheSearch.script == lob.script

/-! ## 6. A walk -/

set_option walk.offer false in
/--
info:   ⇒ □(□p → p) → □p   by ImpR □(□p → p) → □p
    □(□p → p) ⇒ □p   by GLR □p
>     □p → p, □(□p → p), □p ⇒ p   by ImpL □p → p
        0: □(□p → p), □p ⇒ □p, p   by GLR □p   [closed]
        1: p, □(□p → p), □p ⇒ p   by IdP p   [closed]
  at 0.0: 2 premises; no open goals
-/
#guard_msgs in
#walk lob down 0 down 0

/--
trace: ⊢ Walk lob
      ⇒ □(□p → p) → □p   by ImpR □(□p → p) → □p
        □(□p → p) ⇒ □p   by GLR □p
          □p → p, □(□p → p), □p ⇒ p   by ImpL □p → p
    >       p, □(□p → p), □p ⇒ p   by IdP p
      at 0.0.1: no premises; no open goals
-/
#guard_msgs in
example : Walk lob := by
  down 0
  down 0
  down 1
  trace_state
  up

/-! ## 7. A sequent with no derivation -/

#guard leaves (.impR □p p) ([] ⇒ [□p ⟶ p]) == some ["□p ⇒ p"]
#guard offered ([□p] ⇒ [p]) == []

/--
info: ⇒ □p → p
  is not derivable in GLS: it is false at the root of
{}
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [□p ⟶ p]))

/--
info: ⇒ (□p → □q) → □(p → q)
  is not derivable in GLS: it is false at the root of
{}
  {}
  {p}
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]))

/--
info: ⇒ □(□p → p) → □p
  is derivable in GLS: the search found a derivation of height 5
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [□(□p ⟶ p) ⟶ □p]))

instance (s : Seq) : Decidable (Valid s) := validDecidable s
example : ¬ Valid ([] ⇒ [□p ⟶ p]) := by decide +kernel
example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (.node [] [.node [] [], .node [0] []])

/-! ## 8. Out to the mathematics -/

def lobFam : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := famOfDer lob

example : lobFam.height = 5 := rfl
example : Valid ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := soundness _ lobFam
example : Nonempty (Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p])) := completeness _ (soundness _ lobFam)

def cutLeft : Der S ([□p] ⇒ [□□p, □□□p]) := by
  apply_script (found ([□p] ⇒ [□□p, □□□p])).getD []

def cutRight : Der S ([□□p, □p] ⇒ [□□□p]) := by
  apply_script (found ([□□p, □p] ⇒ [□□□p])).getD []

def cutResult : Fam ([□p] ⇒ [□□□p]) :=
  cutAdmissible (□□p) [] [□p] [] [□□□p] (famOfDer cutLeft) (famOfDer cutRight)

#guard ((famOfDer cutLeft).height, (famOfDer cutRight).height, cutResult.height) == (3, 4, 4)

end GLS.ExploreTest
