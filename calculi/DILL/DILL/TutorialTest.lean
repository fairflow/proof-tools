/-
The solutions of the exercises of `tutorial.md`, and every claim that
page, `Play/DILLTutorial.lean` and `campaign/users-guide.md` make about a
particular sequent, checked.  The sections are the tutorial's parts.
Every message and every value was pasted from Lean's output after
reading it.

Code, not theory.
-/
import DILL.Goals
import DILL.Invert
import DILL.Translate
import DILL.Tactic
import DILL.Source
import DILL.Engine

namespace DILL.TutorialTest

open ProofTools ProofTools.Explore DILL List

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-- The moves that apply at a sequent, as the tactic writes them. -/
def offered (j : Seq) : List String :=
  ((candidates j).filter fun m => (S.step m j).toOption.isSome).map Move.src

/-- What a move leaves, as the goals are shown. -/
def leaves (m : Move) (j : Seq) : Option (List String) :=
  (S.step m j).toOption.map (·.map showSeq)

/-- What `step` says where a move does not apply. -/
def refusal (m : Move) (j : Seq) : Option String :=
  match S.step m j with
  | .error e => some e
  | .ok _ => none

/-- The rules of a derivation, from the last one up. -/
def sketch {c : Bool} : {j : Seq} → Fam c j → String
  | _, .init _ _ => "init"
  | _, .copy _ _ d => "copy(" ++ sketch d ++ ")"
  | _, .tensorL _ _ _ _ d => "⊗L(" ++ sketch d ++ ")"
  | _, .tensorR _ _ _ d₁ d₂ => "⊗R(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .oneL _ _ d => "1L(" ++ sketch d ++ ")"
  | _, .oneR _ => "1R"
  | _, .lolliL _ _ _ _ _ d₁ d₂ => "⊸L(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .lolliR d => "⊸R(" ++ sketch d ++ ")"
  | _, .withL₁ _ _ _ _ d => "&L₁(" ++ sketch d ++ ")"
  | _, .withL₂ _ _ _ _ d => "&L₂(" ++ sketch d ++ ")"
  | _, .withR d₁ d₂ => "&R(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .topR => "⊤R"
  | _, .zeroL _ _ => "0L"
  | _, .plusL _ _ _ _ d₁ d₂ => "⊕L(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .plusR₁ d => "⊕R₁(" ++ sketch d ++ ")"
  | _, .plusR₂ d => "⊕R₂(" ++ sketch d ++ ")"
  | _, .bangL _ _ _ d => "!L(" ++ sketch d ++ ")"
  | _, .bangR _ d => "!R(" ++ sketch d ++ ")"
  | _, .cut _ _ _ _ _ d₁ d₂ => "cut(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .cutU _ _ d₁ d₂ => "cut!(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"

/-! ## Section 0: the two notation traps -/

-- `(!p) ⊗ q` is the formula; without the parentheses core Lean's `!` takes
-- all that follows, and the term is `!(p ⊗ q)`
#guard ((!p) ⊗ q) == Form.tensor (.bang p) q
#guard [!p, !(p ⊸ q)] == [Form.bang p, Form.bang (.lolli p q)]
/--
error: Application type mismatch: The argument
  p ⊗ q
has type
  Form
but is expected to have type
  Bool
in the application
  !p ⊗ q
-/
#guard_msgs in
#check (!p ⊗ q : Form)

/-- info: [p ⊕ q, r] : List Form -/
#guard_msgs in
#check ((p ⊕ q) :: [r] : List Form)

/--
error: Application type mismatch: The argument
  p
has type
  Form
of sort `Type` but is expected to have type
  Type ?u.4
of sort `Type (?u.4 + 1)` in the application
  Sum p
-/
#guard_msgs in
#check (p ⊕ q :: [r] : List Form)

-- inside brackets `⊕` is the formula
#guard [p ⊕ q] == [Form.plus p q]
#guard ((p ⊕ q) :: [r]) == [Form.plus p q, r]

/-! ## Section 2: the rules, and the two worked derivations -/

-- `· ; !p ⟹ !p ⊗ !p`
def bangContract : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove bangL p
  dillmove tensorR (!p) (!p) []
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove bangR p
  dillmove copy p
  dillmove init

/--
info: · ; !p ⟹ !p ⊗ !p   by !L !p
  p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
    p ; · ⟹ !p   by !R !p
      p ; · ⟹ p   by copy p
        p ; p ⟹ p   by init
    p ; · ⟹ !p   by !R !p
      p ; · ⟹ p   by copy p
        p ; p ⟹ p   by init
-/
#guard_msgs in
#eval IO.println bangContract.render

#guard (famOfDer bangContract).height == 5

-- what a query says at its root, and after !L
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove bangL p
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove tensorR (!p) (!p) [!p]
---
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove copy p
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove
  dillmove bangL p
  dillmove
  all_goals leave_open

-- the goal as the infoview shows it, and the attempt drawn
/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
>     ? p ; · ⟹ !p
      ? p ; · ⟹ !p
  at 0.0: open goal 0; 2 open in all
---
trace: ⊢ Att S   p ; · ⟹ !p

⊢ Att S   p ; · ⟹ !p
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove bangL p
  dillmove tensorR (!p) (!p) []
  trace_state
  dillmove where
  all_goals leave_open

-- `· ; !p, !(p ⊸ q) ⟹ !q`
def bangMap : Der S ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) := by
  dillmove bangL p
  dillmove bangL (p ⊸ q)
  dillmove bangR q
  dillmove copy (p ⊸ q)
  dillmove lolliL p q []
  dillmove copy p
  dillmove init
  dillmove init

/--
info: · ; !p, !(p ⊸ q) ⟹ !q   by !L !p
  p ; !(p ⊸ q) ⟹ !q   by !L !(p ⊸ q)
    p ⊸ q, p ; · ⟹ !q   by !R !q
      p ⊸ q, p ; · ⟹ q   by copy (p ⊸ q)
        p ⊸ q, p ; p ⊸ q ⟹ q   by ⊸L p ⊸ q []
          p ⊸ q, p ; · ⟹ p   by copy p
            p ⊸ q, p ; p ⟹ p   by init
          p ⊸ q, p ; q ⟹ q   by init
-/
#guard_msgs in
#eval IO.println bangMap.render

#guard (famOfDer bangMap).height == 7

-- !R before the two !L is refused
#guard refusal (.bangR q) ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q)
  == some "!R: the linear zone is not empty"
#guard offered ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) == ["bangL p", "bangL (p ⊸ q)"]
-- after them, copy is offered for each valid hypothesis, and stays offered
#guard offered ([p ⊸ q, p] ⨾ [] ⟹ !q) == ["bangR q", "copy (p ⊸ q)", "copy p"]
#guard offered ([p ⊸ q, p] ⨾ [p ⊸ q] ⟹ q) == ["lolliL p q []", "copy (p ⊸ q)", "copy p"]

-- the derivations are those of `DILL/Source.lean`, written there with the
-- family's constructors
#guard sketch (famOfDer bangContract) == sketch (Source.bangContract (A := p))
#guard sketch (famOfDer bangMap) == sketch (Source.bangMap (A := p) (B := q))
#guard sketch (famOfDer bangMap) == "!L(!L(!R(copy(⊸L(copy(init), init)))))"

-- the rules with no premise: init and 1R take no other linear hypothesis,
-- ⊤R and 0L take any; all four take any unrestricted zone
#guard offered ([] ⨾ [p, q] ⟹ p) == []
#guard refusal .init ([] ⨾ [p, q] ⟹ p)
  == some "init: the linear zone is not exactly the conclusion"
#guard offered ([q] ⨾ [p] ⟹ p) == ["init", "copy q"]
#guard offered ([] ⨾ [p, q] ⟹ ⊤) == ["topR"]
#guard offered ([] ⨾ [𝟎, p] ⟹ q) == ["zeroL"]
-- ⊗R divides the linear zone, &R shares it
#guard leaves (.tensorR p q [p]) ([r] ⨾ [p, q] ⟹ p ⊗ q) == some ["r ; p ⟹ p", "r ; q ⟹ q"]
#guard leaves (.withR p q) ([r] ⨾ [p & q] ⟹ p & q) == some ["r ; p & q ⟹ p", "r ; p & q ⟹ q"]
-- ⊸L divides the rest of the zone
#guard leaves (.lolliL p q [r]) ([] ⨾ [p ⊸ q, r, s] ⟹ s)
  == some ["· ; r ⟹ p", "· ; q, s ⟹ s"]
-- !L moves its formula to the unrestricted zone; copy brings one back and keeps it
#guard leaves (.bangL p) ([] ⨾ [!p, q] ⟹ r) == some ["p ; q ⟹ r"]
#guard leaves (.copy p) ([p] ⨾ [q] ⟹ r) == some ["p ; p, q ⟹ r"]
-- the two cuts
#guard leaves (.cut r [p]) ([s] ⨾ [p, q] ⟹ q) == some ["s ; p ⟹ r", "s ; r, q ⟹ q"]
#guard leaves (.cutU r) ([s] ⨾ [p, q] ⟹ q) == some ["s ; · ⟹ r", "r, s ; p, q ⟹ q"]

/-! ## Part A: derivations -/

-- A1: the four rules with no premise.
def a1a : Der S ([] ⨾ [p] ⟹ p) := by
  dillmove init

def a1b : Der S ([] ⨾ [] ⟹ 𝟏) := by
  dillmove oneR

def a1c : Der S ([] ⨾ [p, q] ⟹ ⊤) := by
  dillmove topR

def a1d : Der S ([] ⨾ [𝟎, p] ⟹ q) := by
  dillmove zeroL

-- A2: CCP p. 16 and p. 17.
def a2a : Der S ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove lolliL p q [p]
  dillmove init
  dillmove init

def a2b : Der S ([] ⨾ [p & q] ⟹ p) := by
  dillmove withL₁ p q
  dillmove init

#guard offered ([] ⨾ [p, p ⊸ q] ⟹ q) == ["lolliL p q []", "lolliL p q [p]"]
#guard leaves (.lolliL p q []) ([] ⨾ [p, p ⊸ q] ⟹ q) == some ["· ; · ⟹ p", "· ; q, p ⟹ q"]
#guard leaves (.lolliL p q [p]) ([] ⨾ [p, p ⊸ q] ⟹ q) == some ["· ; p ⟹ p", "· ; q ⟹ q"]
#guard sketch (famOfDer a2a) == sketch (Source.modusPonens (Γ := []) (A := p) (B := q))

-- A3: CCP p. 16, and a valid hypothesis used twice.
def a3a : Der S ([p] ⨾ [] ⟹ p) := by
  dillmove copy p
  dillmove init

def a3b : Der S ([p] ⨾ [] ⟹ p ⊗ p) := by
  dillmove copy p
  dillmove copy p
  dillmove tensorR p p [p]
  dillmove init
  dillmove init

-- the other order: ⊗R on an empty zone, then a copy in each premise
def a3b' : Der S ([p] ⨾ [] ⟹ p ⊗ p) := by
  dillmove tensorR p p []
  dillmove copy p
  dillmove init
  dillmove copy p
  dillmove init

#guard (famOfDer a3b).height == 4
#guard (famOfDer a3b').height == 3

-- A4: three laws of `!`.
def a4a : Der S ([] ⨾ [!p] ⟹ p) := by
  dillmove bangL p
  dillmove copy p
  dillmove init

def a4b : Der S ([] ⨾ [!p] ⟹ 𝟏) := by
  dillmove bangL p
  dillmove oneR

def a4c : Der S ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove bangL p
  dillmove bangR (!p)
  dillmove bangR p
  dillmove copy p
  dillmove init

-- the third is also an instance of init after !R is refused: at the root
#guard offered ([] ⨾ [!p] ⟹ !(!p)) == ["bangL p"]
#guard offered ([] ⨾ [!p] ⟹ p) == ["bangL p"]
#guard offered ([] ⨾ [!p] ⟹ 𝟏) == ["bangL p"]

-- A5: `!(p & q)` and `!p ⊗ !q`, each from the other.
def a5a : Der S ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) := by
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

def a5b : Der S ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) := by
  dillmove tensorL (!p) (!q)
  dillmove bangL p
  dillmove bangL q
  dillmove bangR (p & q)
  dillmove withR p q
  dillmove copy p
  dillmove init
  dillmove copy q
  dillmove init

#guard offered ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) == ["tensorL (!p) (!q)"]
#guard offered ([] ⨾ [!p, !q] ⟹ !(p & q)) == ["bangL p", "bangL q"]
#guard offered ([p] ⨾ [!q] ⟹ !(p & q)) == ["bangL q", "copy p"]

-- A6: currying, both ways.
def a6a : Der S ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ (q ⊸ r)) := by
  dillmove lolliR p (q ⊸ r)
  dillmove lolliR q r
  dillmove lolliL (p ⊗ q) r [q, p]
  dillmove tensorR p q [p]
  dillmove init
  dillmove init
  dillmove init

def a6b : Der S ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) := by
  dillmove lolliR (p ⊗ q) r
  dillmove tensorL p q
  dillmove lolliL p (q ⊸ r) [p]
  dillmove init
  dillmove lolliL q r [q]
  dillmove init
  dillmove init

/--
info: dillmove: at goal 0, 4 moves apply; no move is made. Try these:
  [apply] dillmove lolliL (p ⊗ q) r []
  [apply] dillmove lolliL (p ⊗ q) r [p]
  [apply] dillmove lolliL (p ⊗ q) r [q]
  [apply] dillmove lolliL (p ⊗ q) r [q, p]
-/
#guard_msgs in
example : Att S true ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ (q ⊸ r)) := by
  dillmove lolliR p (q ⊸ r)
  dillmove lolliR q r
  dillmove
  all_goals leave_open

-- A7: ⊸ distributes over & on the right; & on the left is a choice.
def a7 : Der S ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r)) := by
  dillmove lolliR p (q & r)
  dillmove withR q r
  dillmove withL₁ (p ⊸ q) (p ⊸ r)
  dillmove lolliL p q [p]
  dillmove init
  dillmove init
  dillmove withL₂ (p ⊸ q) (p ⊸ r)
  dillmove lolliL p r [p]
  dillmove init
  dillmove init

/--
info: · ; (p ⊸ q) & (p ⊸ r) ⟹ p ⊸ (q & r)   by ⊸R p ⊸ (q & r)
  · ; p, (p ⊸ q) & (p ⊸ r) ⟹ q & r   by &R q & r
    · ; p, (p ⊸ q) & (p ⊸ r) ⟹ q   by &L₁ (p ⊸ q) & (p ⊸ r)
      · ; p ⊸ q, p ⟹ q   by ⊸L p ⊸ q [p]
        · ; p ⟹ p   by init
        · ; q ⟹ q   by init
    · ; p, (p ⊸ q) & (p ⊸ r) ⟹ r   by &L₂ (p ⊸ q) & (p ⊸ r)
      · ; p ⊸ r, p ⟹ r   by ⊸L p ⊸ r [p]
        · ; p ⟹ p   by init
        · ; r ⟹ r   by init
-/
#guard_msgs in
#eval IO.println a7.render

#guard offered ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r))
  == ["lolliR p (q & r)", "withL₁ (p ⊸ q) (p ⊸ r)", "withL₂ (p ⊸ q) (p ⊸ r)"]
-- &L₁ first loses the derivation
#guard leaves (.withL₁ (p ⊸ q) (p ⊸ r)) ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r))
  == some ["· ; p ⊸ q ⟹ p ⊸ (q & r)"]
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p ⊸ q] ⟹ p ⊸ (q & r))) := by decide
#guard (famOfDer a7).height == 5

-- A8: a cut, and the same without; a lemma used twice by cut!.
def a8cut : Der S ([] ⨾ [p, q] ⟹ q ⊗ p) := by
  dillmove cut (p ⊗ q) [p, q]
  dillmove tensorR p q [p]
  dillmove init
  dillmove init
  dillmove tensorL p q
  dillmove tensorR q p [q]
  dillmove init
  dillmove init

def a8 : Der S ([] ⨾ [p, q] ⟹ q ⊗ p) := by
  dillmove tensorR q p [q]
  dillmove init
  dillmove init

#guard (famOfDer a8cut).height == 4
#guard (famOfDer a8).height == 2

def a8cutU : Der S ([] ⨾ [] ⟹ (p ⊸ p) ⊗ (p ⊸ p)) := by
  dillmove cutU (p ⊸ p)
  dillmove lolliR p p
  dillmove init
  dillmove tensorR (p ⊸ p) (p ⊸ p) []
  dillmove copy (p ⊸ p)
  dillmove init
  dillmove copy (p ⊸ p)
  dillmove init

#guard (famOfDer a8cutU).height == 4
#guard sketch (famOfDer a8cutU) == "cut!(⊸R(init), ⊗R(copy(init), copy(init)))"
-- no cut is offered by a query
#guard offered ([] ⨾ [] ⟹ (p ⊸ p) ⊗ (p ⊸ p)) == ["tensorR (p ⊸ p) (p ⊸ p) []"]

-- A9: the S combinator, with `!A ⊸ B` for the function type.
def a9 : Der S ([] ⨾ [!((!p) ⊸ ((!q) ⊸ r)), !((!p) ⊸ q), !p] ⟹ r) := by
  dillmove bangL ((!p) ⊸ ((!q) ⊸ r))
  dillmove bangL ((!p) ⊸ q)
  dillmove bangL p
  dillmove copy ((!p) ⊸ ((!q) ⊸ r))
  dillmove lolliL (!p) ((!q) ⊸ r) []
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove lolliL (!q) r []
  dillmove bangR q
  dillmove copy ((!p) ⊸ q)
  dillmove lolliL (!p) q []
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove init
  dillmove init

#guard (famOfDer a9).height == 12
-- `p` is copied twice
#guard sketch (famOfDer a9)
  == "!L(!L(!L(copy(⊸L(!R(copy(init)), ⊸L(!R(copy(⊸L(!R(copy(init)), init))), init))))))"

/-! ## Part B: resources -/

-- B1: no weakening of the linear zone; the unrestricted zone weakens.
/-- error: dillmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ 𝟏) := by
  dillmove

/-- error: the move does not apply to goal 0: 1R: the linear zone is not empty -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ 𝟏) := by
  dillmove oneR

#guard offered ([] ⨾ [p] ⟹ 𝟏) == []
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) := by decide

def b1 : Der S ([p] ⨾ [] ⟹ 𝟏) := by
  dillmove oneR

#guard offered ([p] ⨾ [] ⟹ 𝟏) == ["oneR", "copy p"]

-- B2: no contraction of the linear zone; `!` gives it back.
#guard offered ([] ⨾ [p] ⟹ p ⊗ p) == ["tensorR p p []", "tensorR p p [p]"]
#guard leaves (.tensorR p p []) ([] ⨾ [p] ⟹ p ⊗ p) == some ["· ; · ⟹ p", "· ; p ⟹ p"]
#guard leaves (.tensorR p p [p]) ([] ⨾ [p] ⟹ p ⊗ p) == some ["· ; p ⟹ p", "· ; · ⟹ p"]
#guard offered ([] ⨾ [] ⟹ p) == []
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ p ⊗ p)) := by decide

/--
info:   · ; p ⟹ p ⊗ p   by ⊗R p ⊗ p [p]
    · ; p ⟹ p   by init
>   ? · ; · ⟹ p
  at 1: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove tensorR p p [p]
  dillmove init
  dillmove where
  all_goals leave_open

def b2 : Der S ([] ⨾ [!p] ⟹ p ⊗ p) := by
  dillmove bangL p
  dillmove tensorR p p []
  dillmove copy p
  dillmove init
  dillmove copy p
  dillmove init

-- B3: `!` on the right asks an empty linear zone.
#guard offered ([] ⨾ [p] ⟹ !p) == []
#guard refusal (.bangR p) ([] ⨾ [p] ⟹ !p)
  == some "!R: the linear zone is not empty"

/-- `· ; p ⟹ !p` has no derivation without cut: no rule concludes it. -/
theorem b3_not_cf : ¬ Nonempty (CF ([] ⨾ [p] ⟹ !p)) := by
  rintro ⟨d⟩
  cases d <;> first
    | contradiction
    | (have h' := Res.singleton_perm_cons (by assumption); cases h')
    | (have h' := perm_nil_eq (by assumption); cases h')

theorem b3 : ¬ Derivable ([] ⨾ [p] ⟹ !p) := fun h => b3_not_cf (cutEliminationProp _ h)

-- `· ; !p ⟹ !p` in two ways
def b3a : Der S ([] ⨾ [!p] ⟹ !p) := by
  dillmove init

def b3b : Der S ([] ⨾ [!p] ⟹ !p) := by
  dillmove bangL p
  dillmove bangR p
  dillmove copy p
  dillmove init

#guard offered ([] ⨾ [!p] ⟹ !p) == ["init", "bangL p"]
-- `· ; !p, q ⟹ !(p ⊗ q)`: after !L only copy is offered, and it never
-- empties the linear zone
#guard offered ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) == ["bangL p"]
#guard offered ([p] ⨾ [q] ⟹ !(p ⊗ q)) == ["copy p"]
#guard offered ([p] ⨾ [p, q] ⟹ !(p ⊗ q)) == ["copy p"]

-- B4: Pfenning's non-theorem (notes, p. 60).
#guard offered ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))
  == ["tensorR (p ⊸ q) (p ⊸ r) []", "tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)]",
      "lolliL p (q ⊗ r) []"]
#guard leaves (.tensorR (p ⊸ q) (p ⊸ r) []) ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))
  == some ["· ; · ⟹ p ⊸ q", "· ; p ⊸ (q ⊗ r) ⟹ p ⊸ r"]
#guard leaves (.lolliL p (q ⊗ r) []) ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))
  == some ["· ; · ⟹ p", "· ; q ⊗ r ⟹ (p ⊸ q) ⊗ (p ⊸ r)"]
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))) := by decide
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [] ⟹ p ⊸ q)) := by decide
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ p ⊸ r)) := by decide
-- with & in the place of ⊗ on the right it is derivable
def b4 : Der S ([] ⨾ [p ⊸ (q & r)] ⟹ (p ⊸ q) & (p ⊸ r)) := by
  dillmove withR (p ⊸ q) (p ⊸ r)
  dillmove lolliR p q
  dillmove lolliL p (q & r) [p]
  dillmove init
  dillmove withL₁ q r
  dillmove init
  dillmove lolliR p r
  dillmove lolliL p (q & r) [p]
  dillmove init
  dillmove withL₂ q r
  dillmove init

-- B5: copy is always offered, and an attempt does not end.
#guard offered ([p] ⨾ [] ⟹ q) == ["copy p"]
#guard offered ([p] ⨾ [p] ⟹ q) == ["copy p"]
#guard offered ([p] ⨾ [p, p] ⟹ q) == ["copy p"]

/-- **The counting model**: the natural numbers under addition, every set
closed, and the atom numbered `a` given the one phase `w a`. -/
def countModel (w : Nat → Nat) : PhaseModel where
  M := Nat
  mul := (· + ·)
  one := 0
  one_mul := Nat.zero_add
  mul_comm := Nat.add_comm
  mul_assoc := Nat.add_assoc
  Cl := fun X => X
  cl_ext := fun _ _ h => h
  cl_idem := fun _ _ h => h
  cl_mono := fun _ _ h p hp => h p hp
  cl_mul := fun _ _ _ h => h
  val := fun a n => n = w a
  val_closed := fun _ _ h => h

/-- The weights 0 for `p` and 1 for every other atom. -/
def w01 : Nat → Nat := fun a => if a = 0 then 0 else 1

/-- `p ; · ⟹ q` is not satisfied in the counting model with `p` of
weight 0 and `q` of weight 1. -/
theorem b5_not_sat : ¬ (countModel w01).Sat ([p] ⨾ [] ⟹ q) := by
  intro h
  have h1 : (0 : Nat) + 0 = w01 1 :=
    h (0 : Nat) ⟨(0 : Nat), (0 : Nat), ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
  exact absurd h1 (by decide)

theorem b5 : ¬ Derivable ([p] ⨾ [] ⟹ q) := fun h => b5_not_sat (soundness _ h _)

/-! ## Section 4: the structural properties -/

-- exchange in the linear zone, and weakening of the unrestricted zone,
-- applied to a derivation: the same rules, the same height
#guard sketch ((famOfDer a2a).exch (.swap _ _ _)) == sketch (famOfDer a2a)
#guard ((famOfDer a2a).exch (.swap _ _ _)).height == 2
#guard (weakeningU true [] [p, p ⊸ q] r q (famOfDer a2a)).height == 2
example : Fam true ([r] ⨾ [p, p ⊸ q] ⟹ q) := weakeningU true [] [p, p ⊸ q] r q (famOfDer a2a)
example : Fam true ([] ⨾ [p ⊸ q, p] ⟹ q) := (famOfDer a2a).exch (.swap _ _ _)
-- the two pairs that refute weakening and contraction of the linear zone
example : Nonempty (CF ([] ⨾ [] ⟹ 𝟏)) := ⟨.oneR (.refl _)⟩
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) := by decide
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p, p] ⟹ p ⊗ p)) := by decide
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ p ⊗ p)) := by decide

/-! ## Section 5: cut, the inversions, and what follows -/

-- the six sequents with the same connective on both sides (CCP Lemma 6)
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p ⊗ q] ⟹ p ⊗ q)) ∧ ¬ Nonempty (CF ([] ⨾ [] ⟹ q)) := by decide
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p ⊸ q] ⟹ p ⊸ q)) ∧ ¬ Nonempty (CF ([] ⨾ [] ⟹ p)) := by decide
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p & q] ⟹ p & q)) ∧ ¬ Nonempty (CF ([] ⨾ [p] ⟹ p & q)) ∧
    ¬ Nonempty (CF ([] ⨾ [q] ⟹ p & q)) := by decide
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p ⊕ q] ⟹ p ⊕ q)) ∧ ¬ Nonempty (CF ([] ⨾ [p ⊕ q] ⟹ p)) ∧
    ¬ Nonempty (CF ([] ⨾ [p ⊕ q] ⟹ q)) := by decide

-- the three derivations with a cut of `DILL/Cut.lean`, and what cut
-- elimination returns
#guard sketch Cut.exCut == "cut(⊗R(init, init), ⊗L(⊗R(init, init)))"
#guard sketch (cutElimination _ Cut.exCut) == "⊗R(init, init)"
#guard sketch Cut.exCutU == "cut!(⊸R(init), copy(⊸L(copy(⊸L(init, init)), init)))"
#guard sketch (cutElimination _ Cut.exCutU) == "init"
#guard sketch Cut.exBang
  == "cut(!L(!R(&R(copy(init), copy(init)))), !L(copy(copy(⊗R(&L₁(init), &L₂(init))))))"
#guard sketch (cutElimination _ Cut.exBang) == "!L(⊗R(copy(init), copy(init)))"
example : (cutElimination _ Cut.exBang).height = 4 := by decide +kernel

-- an inversion, applied: from `· ; p ⊗ q ⟹ q ⊗ p` to `· ; p, q ⟹ q ⊗ p`
def swapCF : CF ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) :=
  .tensorL p q [] (.refl _) (.tensorR [q] [p] (.swap _ _ _) (.init q (.refl _)) (.init p (.refl _)))

#guard sketch (tensorLInv [] [] p q (q ⊗ p) swapCF) == "⊗R(init, init)"
-- !L inverted: from `· ; !p ⟹ p ⊗ p` to `p ; · ⟹ p ⊗ p`
#guard sketch (bangLInv [] [] p (p ⊗ p) (cutElimination _ (famOfDer b2)))
  == "⊗R(copy(init), copy(init))"

-- consistency and the disjunction property, used
example : ¬ Derivable ([] ⨾ [] ⟹ 𝟎) := consistency
example : Derivable ([] ⨾ [] ⟹ 𝟏 ⊕ p) → Derivable ([] ⨾ [] ⟹ 𝟏) ∨ Derivable ([] ⨾ [] ⟹ p) :=
  disjunctionProperty 𝟏 p

/-! ## Part C: the theorems, used -/

-- C1: identity expansion at `!p ⊗ 1`.
def c1 : CF ([] ⨾ [(!p) ⊗ 𝟏] ⟹ (!p) ⊗ 𝟏) := .init _ (.refl _)

#guard c1.height == 1
#guard sketch (identityExpansion _ c1).1 == "⊗L(⊗R(!L(!R(copy(init))), 1L(1R)))"
#guard (identityExpansion _ c1).1.height == 6
example : (identityExpansion _ c1).1.height = 6 := by decide

-- C2: cut elimination on the two derivations of A8.
#guard sketch (famOfDer a8cut) == "cut(⊗R(init, init), ⊗L(⊗R(init, init)))"
#guard sketch (cutElimination _ (famOfDer a8cut)) == "⊗R(init, init)"
#guard (cutElimination _ (famOfDer a8cut)).height == 2
#guard sketch (cutElimination _ (famOfDer a8cutU)) == "⊗R(⊸R(init), ⊸R(init))"
#guard (cutElimination _ (famOfDer a8cutU)).height == 3

-- C3: modus ponens for ⊸, a derived rule.
def mp {Γ : List Form} {A B : Form} (d₁ : CF (Γ ⨾ [] ⟹ A ⊸ B)) (d₂ : CF (Γ ⨾ [] ⟹ A)) :
    CF (Γ ⨾ [] ⟹ B) :=
  cutAdmissible Γ [] [] A B d₂ (lolliRInv Γ [] A B d₁)

#guard sketch (mp (Γ := [p ⊸ q, p]) (.copy (p ⊸ q) (.head _) (.init _ (.refl _)))
    (.copy p (.tail _ (.head _)) (.init _ (.refl _))))
  == "copy(⊸L(copy(init), init))"

-- C4: `!` is a functor, with no cut.
def bangFunctor {Γ : List Form} {A B : Form} (d : CF (Γ ⨾ [A] ⟹ B)) : CF (Γ ⨾ [!A] ⟹ !B) :=
  .bangL A [] (.refl _) (.bangR (.refl _) (.copy A (.head _) (d.weakenU A)))

#guard sketch (bangFunctor (Γ := []) (.withL₁ p q [] (.refl _) (.init p (.refl _))))
  == "!L(!R(copy(&L₁(init))))"

-- C5: the disjunction property fails with a linear hypothesis.
open DILL.Dec in
theorem no_disjunction_in_context :
    ¬ ∀ (A B : Form) (Δ : List Form), Derivable ([] ⨾ Δ ⟹ A ⊕ B) →
      Derivable ([] ⨾ Δ ⟹ A) ∨ Derivable ([] ⨾ Δ ⟹ B) := fun h =>
  (h p q [p ⊕ q] ((Sem.derivable_iff_cf _).2 (by decide))).elim
    (fun h₁ => absurd ((Sem.derivable_iff_cf _).1 h₁) (by decide))
    (fun h₂ => absurd ((Sem.derivable_iff_cf _).1 h₂) (by decide))

-- C6: the translation.
/-- The rules of a one-zone derivation, from the last one up. -/
def sketchILL {c : Bool} : {Θ : List Form} → {C : Form} → ILL c Θ C → String
  | _, _, .id _ _ => "id"
  | _, _, .cut _ _ _ _ _ d₁ d₂ => "Cut(" ++ sketchILL d₁ ++ ", " ++ sketchILL d₂ ++ ")"
  | _, _, .tensorL _ _ _ _ d => "⊗l(" ++ sketchILL d ++ ")"
  | _, _, .tensorR _ _ _ d₁ d₂ => "⊗r(" ++ sketchILL d₁ ++ ", " ++ sketchILL d₂ ++ ")"
  | _, _, .oneL _ _ d => "1l(" ++ sketchILL d ++ ")"
  | _, _, .oneR _ => "1r"
  | _, _, .lolliL _ _ _ _ _ d₁ d₂ => "⊸l(" ++ sketchILL d₁ ++ ", " ++ sketchILL d₂ ++ ")"
  | _, _, .lolliR d => "⊸r(" ++ sketchILL d ++ ")"
  | _, _, .plusL _ _ _ _ d₁ d₂ => "⊕l(" ++ sketchILL d₁ ++ ", " ++ sketchILL d₂ ++ ")"
  | _, _, .plusR₁ d => "⊕r₁(" ++ sketchILL d ++ ")"
  | _, _, .plusR₂ d => "⊕r₂(" ++ sketchILL d ++ ")"
  | _, _, .zeroL _ _ => "0l"
  | _, _, .withL₁ _ _ _ _ d => "&l₁(" ++ sketchILL d ++ ")"
  | _, _, .withL₂ _ _ _ _ d => "&l₂(" ++ sketchILL d ++ ")"
  | _, _, .withR d₁ d₂ => "&r(" ++ sketchILL d₁ ++ ", " ++ sketchILL d₂ ++ ")"
  | _, _, .topR => "⊤r"
  | _, _, .bangD _ _ _ d => "!D(" ++ sketchILL d ++ ")"
  | _, _, .bangC _ _ _ d => "!C(" ++ sketchILL d ++ ")"
  | _, _, .bangW _ _ _ d => "!W(" ++ sketchILL d ++ ")"
  | _, _, .bangR _ _ d => "!r(" ++ sketchILL d ++ ")"

-- `p ; · ⟹ p` (copy, init) becomes `!p ⊢ p`
/-- info: "!C(!D(!W(id)))" -/
#guard_msgs in
#eval sketchILL (toILL true [p] [] p (famOfDer a3a))

-- `p ; · ⟹ p ⊗ p`, by ⊗R and a copy in each premise, becomes `!p ⊢ p ⊗ p`
/-- info: "!C(⊗r(!C(!D(!W(id))), !C(!D(!W(id)))))" -/
#guard_msgs in
#eval sketchILL (toILL true [p] [] (p ⊗ p) (famOfDer a3b'))

-- the worked derivation of `· ; !p ⟹ !p ⊗ !p`
/-- info: "!C(⊗r(!r(!C(!D(!W(id)))), !r(!C(!D(!W(id))))))" -/
#guard_msgs in
#eval sketchILL (toILL true [] [!p] ((!p) ⊗ (!p)) (famOfDer bangContract))

example : ILLDerivable [!p] (p ⊗ p) := (illEquivalence [p] [] (p ⊗ p)).1 ⟨famOfDer a3b⟩
/-- One sequent of the one-zone calculus is two sequents here. -/
theorem c6 : Derivable ([p] ⨾ [] ⟹ p ⊗ p) ↔ Derivable ([] ⨾ [!p] ⟹ p ⊗ p) :=
  (illEquivalence [p] [] (p ⊗ p)).trans (illEquivalence [] [!p] (p ⊗ p)).symm

-- C7: the counting model.
/-- Every atom of weight 1. -/
def w1 : Nat → Nat := fun _ => 1

/-- `· ; p ⟹ p ⊗ p` is not satisfied where `p` weighs 1: the hypothesis
weighs 1 and the conclusion 2. -/
theorem c7a : ¬ (countModel w1).Sat ([] ⨾ [p] ⟹ p ⊗ p) := by
  intro h
  obtain ⟨a, b, ha, hb, e⟩ : ∃ a b : Nat, a = 1 ∧ b = 1 ∧ (1 : Nat) + 0 = a + b :=
    h (1 : Nat) ⟨(1 : Nat), (0 : Nat), rfl, rfl, rfl⟩
  omega

/-- `· ; p ⟹ 1` is not satisfied there: 1 against 0. -/
theorem c7b : ¬ (countModel w1).Sat ([] ⨾ [p] ⟹ 𝟏) := by
  intro h
  have h1 : (1 : Nat) + 0 = 0 := h (1 : Nat) ⟨(1 : Nat), (0 : Nat), rfl, rfl, rfl⟩
  omega

/-- `· ; !p, q ⟹ !(p ⊗ q)` is not satisfied where `p` weighs 0 and `q`
weighs 1: the hypotheses have the phase 1, and a phase of `!A` is 0. -/
theorem c7c : ¬ (countModel w01).Sat ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) := by
  intro h
  have h1 : (countModel w01).interp (!(p ⊗ q)) ((1 : Nat) + (0 : Nat)) :=
    h (1 : Nat) ⟨(0 : Nat), (1 : Nat), ⟨rfl, rfl, rfl⟩, ⟨(1 : Nat), (0 : Nat), rfl, rfl, rfl⟩, rfl⟩
  have h2 : (1 : Nat) + 0 = 0 := h1.2.1
  omega

example : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) := fun h => c7a (soundness _ h _)
example : ¬ Derivable ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) := fun h => c7c (soundness _ h _)
example : ¬ Valid ([p] ⨾ [] ⟹ q) := fun h => b5_not_sat (h _)

-- C8: validity is closed under the cut on a linear hypothesis.
theorem valid_cut (Γ Δ Δ' : List Form) (A C : Form) (h₁ : Valid (Γ ⨾ Δ ⟹ A))
    (h₂ : Valid (Γ ⨾ A :: Δ' ⟹ C)) : Valid (Γ ⨾ Δ ++ Δ' ⟹ C) :=
  let ⟨d₁⟩ := completeness _ h₁
  let ⟨d₂⟩ := completeness _ h₂
  soundness _ ⟨(cutAdmissible Γ Δ Δ' A C d₁ d₂).lift⟩

-- validity does not depend on the order of the hypotheses
example : Valid ([] ⨾ [p, p ⊸ q] ⟹ q) ↔ Valid ([] ⨾ [p ⊸ q, p] ⟹ q) :=
  valid_perm (.refl _) (.swap _ _ _)

/-! ## The tutorial file, `Play/DILLTutorial.lean`: what each step shows -/

-- 2. a query at the root, a query after !L, and the attempt drawn
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove bangL p
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove tensorR (!p) (!p) [!p]
---
info: dillmove: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove copy p
---
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
>     ? p ; · ⟹ !p
      ? p ; · ⟹ !p
  at 0.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove
  dillmove bangL p
  dillmove
  dillmove tensorR (!p) (!p) []
  dillmove where
  all_goals leave_open

-- a query by the beginning of a name
/--
info: dillmove: at goal 0, 2 moves whose names begin with `te` apply; no move is made. Try these:
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove tensorR (!p) (!p) [!p]
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove te
  all_goals leave_open

-- 3. patterns: each is filled, and shown as "Try this"
/--
info: Try this:
  [apply] dillmove bangL p
---
info: Try this:
  [apply] dillmove tensorR (!p) (!p) []
---
info: Try this:
  [apply] dillmove bangR p
---
info: Try this:
  [apply] dillmove copy p
---
info: Try this:
  [apply] dillmove bangR p
---
info: Try this:
  [apply] dillmove copy p
-/
#guard_msgs in
def bangContractByPatterns : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove bangL
  dillmove tensorR _ _ []
  dillmove bangR
  dillmove copy
  dillmove init
  dillmove bangR
  dillmove copy
  dillmove init

#guard bangContractByPatterns.script == bangContract.script

-- a pattern that several moves match is not made: each is offered
/--
info: dillmove: 2 moves of this form apply at goal 0; no move is made. Try these:
  [apply] dillmove tensorR (!p) (!p) []
  [apply] dillmove tensorR (!p) (!p) [!p]
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove tensorR
  all_goals leave_open

-- 4. a script
#guard bangContract.script.length == 8
#guard derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContract.script
#guard !derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) (bangContract.script.take 7)

/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
>     ? p ; · ⟹ !p
      ? p ; · ⟹ !p
  at 0.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  apply_script bangContract.script.take 2
  dillmove where
  all_goals leave_open

example : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  apply_script bangContract.script.take 2
  dillmove bangR p
  dillmove copy p
  dillmove init
  dillmove bangR p
  dillmove copy p
  dillmove init

-- 5. a walk
set_option walk.offer false in
/--
info: > · ; !p ⟹ !p ⊗ !p   by !L !p
    0: p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []   [closed]
  at the root: 1 premise; no open goals
-/
#guard_msgs in
#walk bangContract

set_option walk.offer false in
/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
>     p ; · ⟹ !p   by !R !p
        0: p ; · ⟹ p   by copy p   [closed]
  at 0.1: 1 premise; no open goals
-/
#guard_msgs in
#walk bangContract down 0 down 1

/--
info:   · ; !p ⟹ !p ⊗ !p   by !L !p
    p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
      p ; · ⟹ !p   by !R !p
>       p ; · ⟹ p   by copy p
          0: p ; p ⟹ p   by init   [closed]
  at 0.1.0: 1 premise; no open goals
---
info: Motions from here:
  [apply] down 0
  [apply] up
  [apply] top
-/
#guard_msgs in
#walk bangContract down 0 down 1 down 0

/--
trace: ⊢ Walk bangContract
      · ; !p ⟹ !p ⊗ !p   by !L !p
        p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
    >     p ; · ⟹ !p   by !R !p
            0: p ; · ⟹ p   by copy p   [closed]
      at 0.1: 1 premise; no open goals
-/
#guard_msgs in
example : Walk bangContract := by
  down 0
  down 1
  down 0
  up
  trace_state

-- 6. a tree of moves, checked by the kernel
/-- The tree of moves of `bangContract`, written out. -/
def bangContractCert : Cert S :=
  .mk (.bangL p) [.mk (.tensorR (!p) (!p) [])
    [.mk (.bangR p) [.mk (.copy p) [.mk .init []]],
     .mk (.bangR p) [.mk (.copy p) [.mk .init []]]]]

example : bangContract.cert = bangContractCert := rfl
example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractCert = true := by decide +kernel
example : Der.ofCert ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContractCert (by decide +kernel)
    = bangContract := rfl
-- a tree with a wrong move (⊗R before !L), and one that stops early: rejected
def wrongCert : Cert S := .mk (.tensorR (!p) (!p) [!p]) [.mk .init [], .mk (.bangR p) []]
def shortCert : Cert S := .mk (.bangL p) [.mk (.tensorR (!p) (!p) []) []]

example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) wrongCert = false := by decide +kernel
example : Cert.check ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) shortCert = false := by decide +kernel
-- the script, checked by the kernel
example : derives S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) bangContract.script = true := by decide +kernel

-- 7. a non-theorem, as far as it goes
/--
info: dillmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] dillmove tensorR (p ⊸ q) (p ⊸ r) []
  [apply] dillmove tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)]
  [apply] dillmove lolliL p (q ⊗ r) []
---
info:   · ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)   by ⊸L p ⊸ (q ⊗ r) []
>   ? · ; · ⟹ p
    ? · ; q ⊗ r ⟹ (p ⊸ q) ⊗ (p ⊸ r)
  at 0: open goal 0; 2 open in all
---
error: dillmove: no move applies at goal 0
-/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove
  dillmove lolliL p (q ⊗ r) []
  dillmove where
  dillmove
  all_goals leave_open

/-- error: the move does not apply to goal 0: init: the linear zone is not exactly the conclusion -/
#guard_msgs in
example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove lolliL p (q ⊗ r) []
  dillmove init

-- 8. out to the mathematics
#guard (famOfDer bangContract).height == 5
example : Valid ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := soundness _ ⟨famOfDer bangContract⟩
example : Nonempty (CF ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))) :=
  completeness _ (soundness _ ⟨famOfDer bangContract⟩)
#guard sketch (cutElimination _ (famOfDer bangContract)) == sketch (famOfDer bangContract)
example : ILLDerivable [!p] ((!p) ⊗ (!p)) :=
  (illEquivalence [] [!p] _).1 ⟨famOfDer bangContract⟩

/-! ## The user's guide: every refusal, seen once -/

#guard refusal .init ([] ⨾ [p, q] ⟹ p) == some "init: the linear zone is not exactly the conclusion"
#guard refusal (.copy p) ([q] ⨾ [] ⟹ p) == some "copy: the formula is not in the unrestricted zone"
#guard refusal (.tensorL p q) ([] ⨾ [p] ⟹ p) == some "⊗L: the formula is not in the linear zone"
#guard refusal (.tensorR p q []) ([] ⨾ [p] ⟹ p) == some "⊗R: the conclusion is not this tensor"
#guard refusal (.tensorR p p [p, p]) ([] ⨾ [p] ⟹ p ⊗ p)
  == some "⊗R: the zone named for the first premise is not part of the linear zone"
#guard refusal .oneL ([] ⨾ [p] ⟹ p) == some "1L: 1 is not in the linear zone"
#guard refusal .oneR ([] ⨾ [] ⟹ p) == some "1R: the conclusion is not 1"
#guard refusal .oneR ([] ⨾ [p] ⟹ 𝟏) == some "1R: the linear zone is not empty"
#guard refusal (.lolliL p q []) ([] ⨾ [p] ⟹ q) == some "⊸L: the formula is not in the linear zone"
#guard refusal (.lolliL p q [r]) ([] ⨾ [p ⊸ q, p] ⟹ q)
  == some "⊸L: the zone named for the first premise is not part of the rest of the linear zone"
#guard refusal (.lolliR p q) ([] ⨾ [] ⟹ p) == some "⊸R: the conclusion is not this implication"
#guard refusal (.withL₁ p q) ([] ⨾ [p] ⟹ p) == some "&L₁: the formula is not in the linear zone"
#guard refusal (.withL₂ p q) ([] ⨾ [p] ⟹ p) == some "&L₂: the formula is not in the linear zone"
#guard refusal (.withR p q) ([] ⨾ [] ⟹ p) == some "&R: the conclusion is not this formula"
#guard refusal .topR ([] ⨾ [] ⟹ p) == some "⊤R: the conclusion is not ⊤"
#guard refusal .zeroL ([] ⨾ [p] ⟹ p) == some "0L: 0 is not in the linear zone"
#guard refusal (.plusL p q) ([] ⨾ [p] ⟹ p) == some "⊕L: the formula is not in the linear zone"
#guard refusal (.plusR₁ p q) ([] ⨾ [] ⟹ p) == some "⊕R₁: the conclusion is not this formula"
#guard refusal (.plusR₂ p q) ([] ⨾ [] ⟹ p) == some "⊕R₂: the conclusion is not this formula"
#guard refusal (.bangL p) ([] ⨾ [p] ⟹ p) == some "!L: the formula is not in the linear zone"
#guard refusal (.bangR p) ([] ⨾ [] ⟹ p) == some "!R: the conclusion is not this formula"
#guard refusal (.bangR p) ([] ⨾ [q] ⟹ !p) == some "!R: the linear zone is not empty"
#guard refusal (.cut r [q]) ([] ⨾ [p] ⟹ p)
  == some "cut: the zone named for the first premise is not part of the linear zone"
-- cut! applies to every sequent
#guard refusal (.cutU r) ([] ⨾ [] ⟹ p) == none
-- the order of a query: the rules that lose nothing, then the choices, then copy
#guard offered ([r] ⨾ [p ⊗ q, p & q, p ⊸ q, !p] ⟹ p ⊕ q)
  == ["tensorL p q", "bangL p", "plusR₁ p q", "plusR₂ p q", "withL₁ p q", "withL₂ p q",
      "lolliL p q []", "lolliL p q [!p]", "lolliL p q [p & q]", "lolliL p q [p & q, !p]",
      "lolliL p q [p ⊗ q]", "lolliL p q [p ⊗ q, !p]", "lolliL p q [p ⊗ q, p & q]",
      "lolliL p q [p ⊗ q, p & q, !p]", "copy r"]
-- a move at another goal, and a goal left open
/--
info:   · ; p, q ⟹ p ⊗ q   by ⊗R p ⊗ q [p]
>   ? · ; p ⟹ p
    · ; q ⟹ q   by init
  at 0: open goal 0; 1 open in all
-/
#guard_msgs in
example : Att S true ([] ⨾ [p, q] ⟹ p ⊗ q) := by
  dillmove tensorR p q [p]
  dillmove init at 1
  dillmove where
  all_goals leave_open

/-! ## Claims of the page's solutions, each checked -/

-- section 2: either ⊗R at the root of the first worked derivation leaves
-- `· ; · ⟹ !p`, which has no derivation
#guard leaves (.tensorR (!p) (!p) []) ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
  == some ["· ; · ⟹ !p", "· ; !p ⟹ !p"]
#guard leaves (.tensorR (!p) (!p) [!p]) ([] ⨾ [!p] ⟹ (!p) ⊗ (!p))
  == some ["· ; !p ⟹ !p", "· ; · ⟹ !p"]
theorem no_bang_p : ¬ Derivable ([] ⨾ [] ⟹ !p) :=
  noDerivableBySet.verdict _ [[] ⨾ [] ⟹ !p, [] ⨾ [] ⟹ p]

-- A2: the other division leaves two sequents with no derivation
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [] ⟹ p)) ∧ ¬ Nonempty (CF ([] ⨾ [q, p] ⟹ q)) := by decide
-- A6: of the four divisions, three leave a first premise with no derivation
#guard (leaves (.lolliL (p ⊗ q) r []) ([] ⨾ [q, p, (p ⊗ q) ⊸ r] ⟹ r)).map (·.head!)
  == some "· ; · ⟹ p ⊗ q"
#guard (leaves (.lolliL (p ⊗ q) r [p]) ([] ⨾ [q, p, (p ⊗ q) ⊸ r] ⟹ r)).map (·.head!)
  == some "· ; p ⟹ p ⊗ q"
#guard (leaves (.lolliL (p ⊗ q) r [q]) ([] ⨾ [q, p, (p ⊗ q) ⊸ r] ⟹ r)).map (·.head!)
  == some "· ; q ⟹ p ⊗ q"
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [] ⟹ p ⊗ q)) ∧ ¬ Nonempty (CF ([] ⨾ [p] ⟹ p ⊗ q)) ∧
    ¬ Nonempty (CF ([] ⨾ [q] ⟹ p ⊗ q)) := by decide
-- B4: the second division
#guard leaves (.tensorR (p ⊸ q) (p ⊸ r) [p ⊸ (q ⊗ r)])
    ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))
  == some ["· ; p ⊸ (q ⊗ r) ⟹ p ⊸ q", "· ; · ⟹ p ⊸ r"]
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [] ⟹ p ⊸ r)) := by decide

/-! ## Section 8: what runs -/

-- 8.1 a tree of moves, checked by the kernel: the verdict is a derivation
def bangContractByTree : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  treeCert.verdict _ bangContractCert

example : bangContractByTree = famOfDer bangContract := rfl
def bangContractByScript : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
  scriptCert.verdict _
    [⟨0, .bangL p⟩, ⟨0, .tensorR (!p) (!p) []⟩, ⟨0, .bangR p⟩, ⟨0, .copy p⟩, ⟨0, .init⟩,
     ⟨0, .bangR p⟩, ⟨0, .copy p⟩, ⟨0, .init⟩]

-- the search with a budget on copy: the second worked derivation
/-- info: [false, false, true, true] -/
#guard_msgs in
#eval (List.range 4).map fun n => (Run.proveLazy ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) n).isSome

-- the tree it finds is the tree of the worked derivation
/-- info: true -/
#guard_msgs in
#eval Run.proveLazy ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 2 == some bangMap.cert

/-- info: some true -/
#guard_msgs in
#eval (Run.proveLazy ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) 1).map fun c => c == bangContract.cert

/-- info: [false, true, true] -/
#guard_msgs in
#eval (List.range 3).map fun n => (Run.proveLazy ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) n).isSome

-- the S combinator of A9
/-- info: [false, false, false, true, true] -/
#guard_msgs in
#eval (List.range 5).map fun n =>
  (Run.proveLazy ([] ⨾ [!((!p) ⊸ ((!q) ⊸ r)), !((!p) ⊸ q), !p] ⟹ r) n).isSome

/-- info: some (true, true) -/
#guard_msgs in
#eval (Run.proveLazy ([] ⨾ [!((!p) ⊸ ((!q) ⊸ r)), !((!p) ⊸ q), !p] ⟹ r) 4).map
  fun c => (Cert.check ([] ⨾ [!((!p) ⊸ ((!q) ⊸ r)), !((!p) ⊸ q), !p] ⟹ r) c, c == a9.cert)

-- sequents with no derivation: nothing found at any budget tried, which is no proof
/-- info: [false, false, false, false, false, false] -/
#guard_msgs in
#eval (List.range 6).map fun n => (Run.proveLazy ([p] ⨾ [] ⟹ q) n).isSome

/-- info: [false, false, false, false, false, false] -/
#guard_msgs in
#eval (List.range 6).map fun n => (Run.proveLazy ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) n).isSome

-- 8.2 the decision where `!` does not occur and the unrestricted zone is empty
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r))) := by decide
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))) := by decide
open DILL.Dec in
example : Derivable ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r)) :=
  (Sem.derivable_iff_cf _).2 (by decide)
open DILL.Dec in
example : ¬ Derivable ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) :=
  fun h => absurd ((Sem.derivable_iff_cf _).1 h) (by decide)
-- the same through the certifier that carries no certificate
example : ¬ Derivable ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := noDerivableDec.verdict _ ()
-- with `!`, or a valid hypothesis, no instance is found
/--
error: failed to synthesize
  Decidable (Nonempty (CF ([] ⨾ [!p] ⟹ p)))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [!p] ⟹ p)) := by decide

example : noDerivableDec.check ([p] ⨾ [] ⟹ q) () = false := by decide +kernel
example : noDerivableDec.check ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) () = false := by decide +kernel
-- the search that is proved, as a function: it returns a derivation
#guard ((Dec.searchCF [(p ⊸ q) & (p ⊸ r)] (p ⊸ (q & r))).map sketch)
  == some "⊸R(&R(&L₁(⊸L(init, init)), &L₂(⊸L(init, init))))"
#guard (Dec.searchCF [p] (p ⊗ p)).isNone

-- 8.3 saturated sets
theorem d4a : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) :=
  noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]

theorem d4b : ¬ Derivable ([] ⨾ [p] ⟹ 𝟏) := noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ 𝟏]

theorem d4c : ¬ Derivable ([] ⨾ [p] ⟹ !p) := noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ !p]

-- the set without `· ; · ⟹ p` is not saturated; a set with an instance of init is not
example : refutedBy [[] ⨾ [p] ⟹ p ⊗ p] ([] ⨾ [p] ⟹ p ⊗ p) = false := by decide +kernel
example : refutedBy [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p, [] ⨾ [p] ⟹ p] ([] ⨾ [p] ⟹ p ⊗ p) = false := by
  decide +kernel
-- the sequent must be a member
example : refutedBy [[] ⨾ [] ⟹ p] ([] ⨾ [p] ⟹ p ⊗ p) = false := by decide +kernel
-- what the producer returns
/-- info: some "[[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]" -/
#guard_msgs in
#eval (refuteSet ([] ⨾ [p] ⟹ p ⊗ p)).map Refute.srcSet

/--
info: some
  "[[] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r), [] ⨾ [p ⊸ (q ⊗ r)] ⟹ p ⊸ q, [] ⨾ [] ⟹ p ⊸ q, [] ⨾ [] ⟹ p, [] ⨾ [p, p ⊸ (q ⊗ r)] ⟹ q, [] ⨾ [q ⊗ r] ⟹ q, [] ⨾ [q, r] ⟹ q, [] ⨾ [p] ⟹ q]"
-/
#guard_msgs in
#eval (refuteSet ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))).map Refute.srcSet

/-- info: some 8 -/
#guard_msgs in
#eval (refuteSet ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))).map (·.length)

-- no saturated set has a member with a valid hypothesis, or with `!` in its linear zone
#guard refuteSet ([p] ⨾ [] ⟹ q) == none
#guard refuteSet ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) == none
example : refutedBy [[p] ⨾ [] ⟹ q, [p] ⨾ [p] ⟹ q] ([p] ⨾ [] ⟹ q) = false := by decide +kernel
/-- info: "the unrestricted zone is not empty" -/
#guard_msgs in
#eval match Refute.outcome ([p] ⨾ [] ⟹ q) with
  | .noSet why => why
  | _ => "another answer"

/-- info: "1 sequent with ! in the linear zone was set aside" -/
#guard_msgs in
#eval match Refute.outcome ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) with
  | .noSet why => why
  | _ => "another answer"

-- 8.4 the engine's producer: for, against, or neither
/-- What the engine's producer answers, as a word. -/
def answer (j : Seq) (n : Nat) : String :=
  match produce j n with
  | .pass _ => "pass"
  | .fail _ => "fail"
  | .flag => "flag"

/-- info: ["pass", "fail", "flag", "flag", "flag", "pass"] -/
#guard_msgs in
#eval [answer ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) 2, answer ([] ⨾ [p] ⟹ p ⊗ p) 2,
  answer ([p] ⨾ [] ⟹ q) 2, answer ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) 2,
  answer ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 1, answer ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) 2]

/-! ## Part D: what runs -/

-- D1: as in 8.2.
open DILL.Dec in
example : Nonempty (CF ([] ⨾ [p, p ⊸ q] ⟹ q)) := by decide
open DILL.Dec in
example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) := by decide

-- D2: a tree of moves by hand, for `· ; !p ⟹ p ⊗ p` (B2).
def d2 : Fam true ([] ⨾ [!p] ⟹ p ⊗ p) :=
  treeCert.verdict _
    (.mk (.bangL p) [.mk (.tensorR p p [])
      [.mk (.copy p) [.mk .init []], .mk (.copy p) [.mk .init []]]])

example : d2 = famOfDer b2 := rfl
-- with the second copy left out the tree does not check
example : treeCert.check ([] ⨾ [!p] ⟹ p ⊗ p)
    (.mk (.bangL p) [.mk (.tensorR p p [])
      [.mk (.copy p) [.mk .init []], .mk .init []]]) = false := by decide +kernel

-- D3: budgets, pinned in 8.1 above.
-- D4: `d4a`, and a set for `· ; · ⟹ !p`: `no_bang_p` above.
-- D5: no saturated set, and what refutes instead: `b5`, `c7c`.
example : ¬ Derivable ([p] ⨾ [] ⟹ q) := b5
example : ¬ Derivable ([] ⨾ [!p, q] ⟹ !(p ⊗ q)) := fun h => c7c (soundness _ h _)

/-! ## The user's guide: the two traps, once more; a sequent typed -/

-- `⊕` beside `⊸` wants parentheses
/--
error: Application type mismatch: The argument
  p
has type
  Form
of sort `Type` but is expected to have type
  Type ?u.3
of sort `Type (?u.3 + 1)` in the application
  Sum p
-/
#guard_msgs in
#check (p ⊕ q ⊸ r : Form)

#guard ((p ⊕ q) ⊸ r) == Form.lolli (.plus p q) r
-- beside `⊗` and `&`, which bind tighter than Lean's `⊕`, it is read as the formula
#guard (p ⊗ q ⊕ r : Form) == Form.plus (.tensor p q) r
-- `!` last in a sequent, and under another `!`
#guard ([] ⨾ [!p, q] ⟹ !(p & q)) == Seq.mk [] [.bang p, q] (.bang (.wth p q))
#guard (!(!p) : Form) == Form.bang (.bang p)
-- how a sequent is shown
#guard showSeq ([p ⊸ q, p] ⨾ [!p, q ⊕ r] ⟹ (!p) ⊗ 𝟏) == "p ⊸ q, p ; !p, q ⊕ r ⟹ !p ⊗ 1"
#guard showSeq ([] ⨾ [] ⟹ ⊤) == "· ; · ⟹ ⊤"
-- a goal stated as `Der S j` is printed by Lean, as a term, until the first move
/-- trace: ⊢ Der S ([] ⨾ [p] ⟹ p) -/
#guard_msgs in
example : Der S ([] ⨾ [p] ⟹ p) := by
  trace_state
  dillmove init

/-- trace: ⊢ Att S   · ; p ⟹ p -/
#guard_msgs in
example : Att S true ([] ⨾ [p] ⟹ p) := by
  trace_state
  dillmove init

end DILL.TutorialTest
