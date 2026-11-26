/-
The solutions of the exercises of `tutorial.md`, and every claim that
page makes about a particular sequent, checked.  The sections are the
tutorial's parts.  Every message and every value was pasted from Lean's
output after reading it.

Code, not theory.
-/
import MALL.Explore
import MALL.ModelRun
import MALL.Refute
import MALL.Craig
import MALL.Uniform

namespace MALL.TutorialTest

open ProofTools ProofTools.Explore MALL List

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-- The moves that apply at a sequent, as the tactic writes them. -/
def offered (j : List Form) : List String :=
  ((candidates j).filter fun m => (S.step m j).toOption.isSome).map Move.src

/-- What a move leaves, as the goals are shown. -/
def leaves (m : Move) (j : List Form) : Option (List String) :=
  (S.step m j).toOption.map (·.map showSeq)

/-- What `step` says where a move does not apply. -/
def refusal (m : Move) (j : List Form) : Option String :=
  match S.step m j with
  | .error e => some e
  | .ok _ => none

/-- The moves offered at a sequent that begin a derivation: every premise
they leave is derivable. -/
def good (j : List Form) : List String :=
  ((candidates j).filter fun m =>
    match (S.step m j).toOption with
    | some ps => ps.all fun Γ => decide (Derivable Γ)
    | none => false).map Move.src

/-- The rules of a derivation without cut, from the last one up. -/
def sketch : {Ξ : List Form} → CF Ξ → String
  | _, .ax _ _ => "ax"
  | _, .top _ _ => "⊤"
  | _, .wth _ _ _ _ d₁ d₂ => "&(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .plus₁ _ _ _ _ d => "1⊕(" ++ sketch d ++ ")"
  | _, .plus₂ _ _ _ _ d => "2⊕(" ++ sketch d ++ ")"
  | _, .one _ => "1"
  | _, .bot _ _ d => "⊥(" ++ sketch d ++ ")"
  | _, .tensor _ _ _ _ _ d₁ d₂ => "⊗(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .par _ _ _ _ d => "⅋(" ++ sketch d ++ ")"

/-- A set of phases as text. -/
def sh (G : List Bool) : String := showPhases G

/-- The subsets of ℤ/m. -/
def subsets (m : Nat) : List (List Bool) := (List.range (2 ^ m)).map (bitsSet m)

/-! ## Section 1: neither conjunction implies the other -/

example : ¬ Derivable [(p ⊗ q)ᗮ ⅋ (p & q)] := by decide +kernel
example : ¬ Derivable [(p & q)ᗮ ⅋ (p ⊗ q)] := by decide +kernel

/-! ## Section 2: the rules, and the worked derivation -/

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

/--
info: ⊢ p⊥ ⅋ (q⊥ & r⊥), (p ⊗ q) ⊕ (p ⊗ r)   by ⅋ p⊥ ⅋ (q⊥ & r⊥)
  ⊢ p⊥, q⊥ & r⊥, (p ⊗ q) ⊕ (p ⊗ r)   by & q⊥ & r⊥
    ⊢ q⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   by 1⊕ (p ⊗ q) ⊕ (p ⊗ r)
      ⊢ p ⊗ q, q⊥, p⊥   by ⊗ p ⊗ q [p⊥]
        ⊢ p, p⊥   by ax p
        ⊢ q, q⊥   by ax q
    ⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   by 2⊕ (p ⊗ q) ⊕ (p ⊗ r)
      ⊢ p ⊗ r, r⊥, p⊥   by ⊗ p ⊗ r [p⊥]
        ⊢ p, p⊥   by ax p
        ⊢ r, r⊥   by ax r
-/
#guard_msgs in
#eval IO.println distrib.render

#guard (famOfDer distrib).height == 5

-- what a query says at the root of the worked derivation
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

-- the logical axiom takes no context; ⊤ takes any; 𝟎 has no rule
#guard offered [p, pᗮ, p] == []
#guard refusal (.ax p) [p, pᗮ, p] == some "ax: the sequent is not ⊢ A, A⊥"
#guard offered [⊤, p, q] == ["top"]
#guard offered [𝟎, p] == []
#guard offered [𝟎] == []
#guard offered [] == []
-- ⊗ splits the context, & shares it
#guard leaves (.tensor p q [pᗮ]) [p ⊗ q, qᗮ, pᗮ] == some ["⊢ p, p⊥", "⊢ q, q⊥"]
#guard leaves (.wth qᗮ rᗮ) [pᗮ, qᗮ & rᗮ, (p ⊗ q) ⊕ (p ⊗ r)]
  == some ["⊢ q⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)", "⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)"]

/-! ## Part A: derivations -/

-- A1: the three rules with no premise.
def a1a : Der S [p, pᗮ] := by
  mallmove ax p

def a1b : Der S [𝟏] := by
  mallmove one

def a1c : Der S [⊤, p, q] := by
  mallmove top

-- A2: `p ⊸ p`, `⊢ ⊥, 1`, and `0 ⊸ p`.
def a2a : Der S [pᗮ ⅋ p] := by
  mallmove par pᗮ p
  mallmove ax pᗮ

def a2b : Der S [⊥, 𝟏] := by
  mallmove bot
  mallmove one

def a2c : Der S [⊤ ⅋ p] := by
  mallmove par ⊤ p
  mallmove top

#guard leaves (.par pᗮ p) [pᗮ ⅋ p] == some ["⊢ p⊥, p"]
#guard leaves .bot [⊥, 𝟏] == some ["⊢ 1"]
#guard showSeq [𝟎ᗮ ⅋ p] == "⊢ ⊤ ⅋ p"

-- A3: the axiom at `p ⊗ q` from axioms at letters, and commutativity.
def a3a : Der S [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove par pᗮ qᗮ
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q

def a3b : Der S [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove par pᗮ qᗮ
  mallmove tensor q p [qᗮ]
  mallmove ax q
  mallmove ax p

#guard offered [pᗮ, qᗮ, q ⊗ p]
  == ["tensor q p []", "tensor q p [qᗮ]", "tensor q p [pᗮ]", "tensor q p [pᗮ, qᗮ]"]
#guard good [pᗮ, qᗮ, q ⊗ p] == ["tensor q p [qᗮ]"]
#guard leaves (.tensor q p [pᗮ]) [pᗮ, qᗮ, q ⊗ p] == some ["⊢ q, p⊥", "⊢ p, q⊥"]
#guard leaves (.tensor q p []) [pᗮ, qᗮ, q ⊗ p] == some ["⊢ q", "⊢ p, p⊥, q⊥"]
#guard leaves (.tensor q p [pᗮ, qᗮ]) [pᗮ, qᗮ, q ⊗ p] == some ["⊢ q, p⊥, q⊥", "⊢ p"]

-- A4: `1 ⊗ p` and `p`.
def a4a : Der S [(𝟏 ⊗ p)ᗮ, p] := by
  mallmove par ⊥ pᗮ
  mallmove bot
  mallmove ax pᗮ

def a4b : Der S [pᗮ, 𝟏 ⊗ p] := by
  mallmove tensor 𝟏 p []
  mallmove one
  mallmove ax p

-- A5: `p ⊸ p & p`, and `p & q ⊸ p`.
def a5a : Der S [pᗮ ⅋ (p & p)] := by
  mallmove par pᗮ (p & p)
  mallmove wth p p
  mallmove ax p
  mallmove ax p

def a5b : Der S [(p & q)ᗮ ⅋ p] := by
  mallmove par (pᗮ ⊕ qᗮ) p
  mallmove plus₁ pᗮ qᗮ
  mallmove ax pᗮ

#guard showSeq [(p & q)ᗮ ⅋ p] == "⊢ (p⊥ ⊕ q⊥) ⅋ p"

-- A6: ⅋ over &, the half where the order of the rules matters.
def a6 : Der S [((p ⅋ q) & (p ⅋ r))ᗮ, p ⅋ (q & r)] := by
  mallmove par p (q & r)
  mallmove wth q r
  mallmove plus₁ (pᗮ ⊗ qᗮ) (pᗮ ⊗ rᗮ)
  mallmove tensor pᗮ qᗮ [p]
  mallmove ax pᗮ
  mallmove ax qᗮ
  mallmove plus₂ (pᗮ ⊗ qᗮ) (pᗮ ⊗ rᗮ)
  mallmove tensor pᗮ rᗮ [p]
  mallmove ax pᗮ
  mallmove ax rᗮ

/--
info: ⊢ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥), p ⅋ (q & r)   by ⅋ p ⅋ (q & r)
  ⊢ p, q & r, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by & q & r
    ⊢ q, p, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by 1⊕ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)
      ⊢ p⊥ ⊗ q⊥, q, p   by ⊗ p⊥ ⊗ q⊥ [p]
        ⊢ p⊥, p   by ax p⊥
        ⊢ q⊥, q   by ax q⊥
    ⊢ r, p, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by 2⊕ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)
      ⊢ p⊥ ⊗ r⊥, r, p   by ⊗ p⊥ ⊗ r⊥ [p]
        ⊢ p⊥, p   by ax p⊥
        ⊢ r⊥, r   by ax r⊥
-/
#guard_msgs in
#eval IO.println a6.render

-- 1⊕ or 2⊕ as the first move loses the derivation
#guard leaves (.plus₁ (pᗮ ⊗ qᗮ) (pᗮ ⊗ rᗮ)) [((p ⅋ q) & (p ⅋ r))ᗮ, p ⅋ (q & r)]
  == some ["⊢ p⊥ ⊗ q⊥, p ⅋ (q & r)"]
example : ¬ Derivable [pᗮ ⊗ qᗮ, p ⅋ (q & r)] := by decide +kernel
example : ¬ Derivable [pᗮ ⊗ rᗮ, p ⅋ (q & r)] := by decide +kernel

-- A7: a cut, and the same sequent without one.
def a7 : Der S [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove par pᗮ qᗮ
  mallmove tensor q p [qᗮ]
  mallmove ax q
  mallmove ax p

def a7' : Der S [pᗮ, qᗮ, q ⊗ p] := by
  mallmove tensor q p [qᗮ]
  mallmove ax q
  mallmove ax p

/--
info: ⊢ p⊥, q⊥, q ⊗ p   by cut (p ⊗ q) [p⊥, q⊥]
  ⊢ p ⊗ q, p⊥, q⊥   by ⊗ p ⊗ q [p⊥]
    ⊢ p, p⊥   by ax p
    ⊢ q, q⊥   by ax q
  ⊢ p⊥ ⅋ q⊥, q ⊗ p   by ⅋ p⊥ ⅋ q⊥
    ⊢ p⊥, q⊥, q ⊗ p   by ⊗ q ⊗ p [q⊥]
      ⊢ q, q⊥   by ax q
      ⊢ p, p⊥   by ax p
-/
#guard_msgs in
#eval IO.println a7.render

#guard leaves (.cut (p ⊗ q) [pᗮ, qᗮ]) [pᗮ, qᗮ, q ⊗ p]
  == some ["⊢ p ⊗ q, p⊥, q⊥", "⊢ p⊥ ⅋ q⊥, q ⊗ p"]
#guard (famOfDer a7).height == 4
#guard (famOfDer a7').height == 2

/-! ## Part B: resources -/

-- B1: `⊢ 1, 1`.
#guard offered [𝟏, 𝟏] == []
#guard refusal .one [𝟏, 𝟏] == some "1: the sequent is not ⊢ 1"

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove

/-- error: the move does not apply to goal 0: 1: the sequent is not ⊢ 1 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove one

example : ¬ Derivable [𝟏, 𝟏] := by decide +kernel

-- B2: `p ⊸ p ⊗ p`.
#guard offered [pᗮ ⅋ (p ⊗ p)] == ["par pᗮ (p ⊗ p)"]
#guard offered [pᗮ, p ⊗ p] == ["tensor p p []", "tensor p p [pᗮ]"]
#guard leaves (.tensor p p []) [pᗮ, p ⊗ p] == some ["⊢ p", "⊢ p, p⊥"]
#guard leaves (.tensor p p [pᗮ]) [pᗮ, p ⊗ p] == some ["⊢ p, p⊥", "⊢ p"]
#guard offered [p] == []
example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := by decide +kernel

-- B3: no contraction.
#guard offered [p ⊕ pᗮ] == ["plus₁ p pᗮ", "plus₂ p pᗮ"]
#guard leaves (.plus₁ p pᗮ) [p ⊕ pᗮ] == some ["⊢ p"]
#guard leaves (.plus₂ p pᗮ) [p ⊕ pᗮ] == some ["⊢ p⊥"]

def b3 : Der S [p ⊕ pᗮ, p ⊕ pᗮ] := by
  mallmove plus₁ p pᗮ
  mallmove plus₂ p pᗮ
  mallmove ax p

example : ¬ Derivable [p ⊕ pᗮ] := by decide +kernel
-- the multiplicative disjunction of `p` and `p⊥` is derivable
example : Derivable [p ⅋ pᗮ] := by decide +kernel

-- B4: sixteen moves are offered, and two of them begin a derivation.
#guard showSeq [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r] == "⊢ p⊥, p ⊗ q⊥, q ⊗ r⊥, r"
#guard (offered [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r]).length == 16
#guard good [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r] == ["tensor p qᗮ [pᗮ]", "tensor q rᗮ [pᗮ, p ⊗ qᗮ]"]

def b4 : Der S [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r] := by
  mallmove tensor p qᗮ [pᗮ]
  mallmove ax p
  mallmove tensor q rᗮ [qᗮ]
  mallmove ax q
  mallmove ax r

def b4' : Der S [pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r] := by
  mallmove tensor q rᗮ [pᗮ, p ⊗ qᗮ]
  mallmove tensor p qᗮ [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove ax r

/--
info: ⊢ p⊥, p ⊗ q⊥, q ⊗ r⊥, r   by ⊗ p ⊗ q⊥ [p⊥]
  ⊢ p, p⊥   by ax p
  ⊢ q⊥, q ⊗ r⊥, r   by ⊗ q ⊗ r⊥ [q⊥]
    ⊢ q, q⊥   by ax q
    ⊢ r⊥, r   by ax r
-/
#guard_msgs in
#eval IO.println b4.render

/-! ## Section 4 and Part C: phase semantics -/

/-- ℤ/2 with the antiphases {1}. -/
def z21 : ZModel := ⟨1, [false, true], []⟩

-- the duals of the four subsets
#guard ((subsets 2).map fun G => (sh G, sh (z21.dualL G)))
  == [("{}", "{0, 1}"), ("{0}", "{1}"), ("{1}", "{0}"), ("{0, 1}", "{}")]
-- the constants, and `1 ⅋ 1`
#guard ([𝟏, ⊥, ⊤, 𝟎, 𝟏 ⅋ 𝟏].map fun A => (A.show, sh (z21.interpL A)))
  == [("1", "{0}"), ("⊥", "{1}"), ("⊤", "{0, 1}"), ("0", "{}"), ("1 ⅋ 1", "{1}")]
-- the steps of the worked computation: ⟦1⟧⊥, and its product with itself
#guard sh (z21.dualL (z21.interpL 𝟏)) == "{1}"
#guard sh (z21.prodL (z21.dualL (z21.interpL 𝟏)) (z21.dualL (z21.interpL 𝟏))) == "{0}"
#guard z21.refutes [𝟏, 𝟏]
#guard !z21.refutes [𝟏]

example : ¬ Derivable [𝟏, 𝟏] := noDerivableBy.verdict _ ⟨1, [false, true], []⟩
example : ¬ Valid [𝟏, 𝟏] := noValidBy.verdict _ ⟨1, [false, true], []⟩

/--
info: ⊢ 1, 1
  is not derivable (decided by the proved search)
  refuted in ℤ/2 with antiphases {1}, p = {0, 1}, q = {0, 1}
-/
#guard_msgs in
#eval IO.println (explain [𝟏, 𝟏])

-- C1: ℤ/3 with the antiphases {0}: the duals, the closures, the facts.
def z30 : ZModel := ⟨2, [true, false, false], []⟩

#guard ((subsets 3).map fun G => (sh G, sh (z30.dualL G), sh (z30.dualL (z30.dualL G))))
  == [("{}", "{0, 1, 2}", "{}"), ("{0}", "{0}", "{0}"), ("{1}", "{2}", "{1}"),
      ("{0, 1}", "{}", "{0, 1, 2}"), ("{2}", "{1}", "{2}"), ("{0, 2}", "{}", "{0, 1, 2}"),
      ("{1, 2}", "{}", "{0, 1, 2}"), ("{0, 1, 2}", "{}", "{0, 1, 2}")]
#guard ((subsets 3).filter fun G => z30.dualL (z30.dualL G) == G).map sh
  == ["{}", "{0}", "{1}", "{2}", "{0, 1, 2}"]

-- C2: ℤ/2 with the antiphases {0} does not refute `⊢ 1, 1`.
def z20 : ZModel := ⟨1, [true, false], []⟩

#guard ([𝟏, ⊥, 𝟏 ⅋ 𝟏].map fun A => (A.show, sh (z20.interpL A)))
  == [("1", "{0}"), ("⊥", "{0}"), ("1 ⅋ 1", "{0}")]
#guard !z20.refutes [𝟏, 𝟏]
example : noDerivableBy.check [𝟏, 𝟏] ⟨1, [true, false], []⟩ = false := by decide +kernel

-- C3: weights in ℤ/2: the antiphases {0}, and `p` = {1}.
def w2 : ZModel := ⟨1, [true, false], [[false, true]]⟩

#guard ([p, pᗮ, p ⊗ p, pᗮ ⅋ (p ⊗ p), p ⊕ pᗮ, p ⅋ pᗮ].map fun A => (A.show, sh (w2.interpL A)))
  == [("p", "{1}"), ("p⊥", "{1}"), ("p ⊗ p", "{0}"), ("p⊥ ⅋ (p ⊗ p)", "{1}"),
      ("p ⊕ p⊥", "{1}"), ("p ⅋ p⊥", "{0}")]

example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
  noDerivableBy.verdict _ ⟨1, [true, false], [[false, true]]⟩
example : ¬ Derivable [p ⊕ pᗮ] :=
  noDerivableBy.verdict _ ⟨1, [true, false], [[false, true]]⟩

-- the producer finds that structure for both
#guard refuteBy [pᗮ ⅋ (p ⊗ p)] == some ⟨1, [true, false], [[false, true]]⟩
#guard refuteBy [p ⊕ pᗮ] == some ⟨1, [true, false], [[false, true]]⟩

-- C4: `p ⊸ p ⊗ (p ⊗ p)`: no structure on ℤ/1 or ℤ/2, and twelve of the
-- sixty-four on ℤ/3.
#guard showSeq [pᗮ ⅋ (p ⊗ (p ⊗ p))] == "⊢ p⊥ ⅋ (p ⊗ (p ⊗ p))"
example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] := by decide +kernel
#guard (allOn 1 1).length == 4
#guard (allOn 2 1).length == 16
#guard (allOn 3 1).length == 64
#guard ((allOn 1 1).filter fun z => z.refutes [pᗮ ⅋ (p ⊗ (p ⊗ p))]).length == 0
#guard ((allOn 2 1).filter fun z => z.refutes [pᗮ ⅋ (p ⊗ (p ⊗ p))]).length == 0
#guard ((allOn 3 1).filter fun z => z.refutes [pᗮ ⅋ (p ⊗ (p ⊗ p))]).length == 12

/-- Weights in ℤ/3: the antiphases {0}, and `p` = {1}. -/
def w3 : ZModel := ⟨2, [true, false, false], [[false, true, false]]⟩

#guard ([p, pᗮ, p ⊗ p, p ⊗ (p ⊗ p), pᗮ ⅋ (p ⊗ (p ⊗ p))].map fun A =>
    (A.show, sh (w3.interpL A)))
  == [("p", "{1}"), ("p⊥", "{2}"), ("p ⊗ p", "{2}"), ("p ⊗ (p ⊗ p)", "{0}"),
      ("p⊥ ⅋ (p ⊗ (p ⊗ p))", "{2}")]

example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] :=
  noDerivableBy.verdict _ ⟨2, [true, false, false], [[false, true, false]]⟩

#guard refuteBy [pᗮ ⅋ (p ⊗ (p ⊗ p))] == some ⟨2, [true, false, false], [[false, true, false]]⟩

-- The producer is not complete: a sequent with no derivation for which it
-- finds no structure (the converse of half-distributivity, three letters).
example : ¬ Derivable [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] := by decide +kernel
#guard refuteBy [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] == none

/-! ### The second certificate: a saturated set of sequents -/

-- the example of the text: `⊢ p ⊕ p⊥`, with the premises of its two rules
example : ¬ Derivable [p ⊕ pᗮ] := noDerivableBySet.verdict _ [[pᗮ], [p ⊕ pᗮ], [p]]
example : ¬ Valid [p ⊕ pᗮ] := noValidBySet.verdict _ [[pᗮ], [p ⊕ pᗮ], [p]]
-- without the premise of 2⊕ the set is not saturated
#guard !refutedBy [[p ⊕ pᗮ], [p]] [p ⊕ pᗮ]
-- `⊢ 1, 1`: the set of that one sequent
example : ¬ Derivable [𝟏, 𝟏] := noDerivableBySet.verdict _ [[𝟏, 𝟏]]

/--
info: ⊢ p ⊕ p⊥
  is refuted by a saturated set of 3 sequents:
    ⊢ p⊥
    ⊢ p ⊕ p⊥
    ⊢ p
  It presents a phase structure of 5 phases: the parts of those sequents, and ∞ for every other sequent.
  The antiphases are the phases that are not among the 3.
  Computed in it, the sequent holds: false.
-/
#guard_msgs in
#eval IO.println (describeCountermodel [p ⊕ pᗮ])

-- C5: sets written by hand.
example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
  noDerivableBySet.verdict _ [[pᗮ ⅋ (p ⊗ p)], [pᗮ, p ⊗ p], [p]]
-- without `⊢ p` the condition at ⊗ fails
#guard !refutedBy [[pᗮ ⅋ (p ⊗ p)], [pᗮ, p ⊗ p]] [pᗮ ⅋ (p ⊗ p)]

example : ¬ Derivable [p & q, pᗮ] := noDerivableBySet.verdict _ [[p & q, pᗮ], [q, pᗮ]]
-- the other premise of & is a logical axiom: a set that has it is rejected
#guard !refutedBy [[p & q, pᗮ], [q, pᗮ], [p, pᗮ]] [p & q, pᗮ]
-- and & asks for one premise at least
#guard !refutedBy [[p & q, pᗮ]] [p & q, pᗮ]

-- C6: the sequent of C4, which needs ℤ/3 among the cyclic groups: four sequents.
example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] :=
  noDerivableBySet.verdict _ [[pᗮ ⅋ (p ⊗ (p ⊗ p))], [pᗮ, p ⊗ (p ⊗ p)], [p ⊗ p], [p]]

-- The converse of half-distributivity, for which `refuteBy` finds no
-- structure: the producer of sets returns seventeen sequents, and the check
-- accepts them.  (Compiled evaluation: the producer is code.)
#guard (refuteSet [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]).map (·.length) == some 17
#guard (refuteSet [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]).map
  (fun D => refutedBy D [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]) == some true
-- the producer returns nothing for a sequent that has a derivation
#guard (refuteSet [pᗮ ⅋ (p & p)]).isNone
-- and a set for each sequent of Parts B and C that has none
#guard [[𝟏, 𝟏], [pᗮ ⅋ (p ⊗ p)], [p ⊕ pᗮ], [pᗮ ⅋ (p ⊗ (p ⊗ p))]].all fun Γ =>
  match refuteSet Γ with
  | some D => refutedBy D Γ
  | none => false

/-! ## Section 5 and Part D: the theorems, used -/

-- 5.2: the pairs that refute weakening and contraction
example : Derivable [𝟏] := by decide +kernel
example : Derivable [p ⊕ pᗮ, p ⊕ pᗮ] := by decide +kernel

-- 5.6: ⊕ and ⊗ are not invertible
example : Derivable [p ⊕ q, pᗮ & qᗮ] := by decide +kernel
example : ¬ Derivable [p, pᗮ & qᗮ] := by decide +kernel
example : ¬ Derivable [q, pᗮ & qᗮ] := by decide +kernel
#guard leaves (.tensor p q [qᗮ]) [p ⊗ q, pᗮ, qᗮ] == some ["⊢ p, q⊥", "⊢ q, p⊥"]
example : ¬ Derivable [p, qᗮ] := by decide +kernel

-- D1: the axiom, from axioms at letters.
#guard ([p, 𝟏, ⊤, p ⊗ q, p & q].map fun A => (A.show, (idExp A).height, sketch (idExp A)))
  == [("p", 1, "ax"), ("1", 2, "⊥(1)"), ("⊤", 1, "⊤"), ("p ⊗ q", 3, "⅋(⊗(ax, ax))"),
      ("p & q", 3, "&(1⊕(ax), 2⊕(ax))")]

def d1 : CF [(p ⊗ q) & 𝟏, ((p ⊗ q) & 𝟏)ᗮ] := .ax _ (.refl _)

#guard showSeq [(p ⊗ q) & 𝟏, ((p ⊗ q) & 𝟏)ᗮ] == "⊢ (p ⊗ q) & 1, (p⊥ ⅋ q⊥) ⊕ ⊥"
#guard d1.height == 1
#guard (identityExpansion _ d1).1.height == 5
#guard sketch (identityExpansion _ d1).1 == "&(1⊕(⅋(⊗(ax, ax))), 2⊕(⊥(1)))"

-- D2: the cut of A7, eliminated.
def d2 : CF [pᗮ, qᗮ, q ⊗ p] := cutElimination _ (famOfDer a7)

#guard d2.height == 2
#guard sketch d2 == "⊗(ax, ax)"

-- D3: modus ponens for ⊸, by an inversion and a cut.
def mp {A B : Form} (d₁ : CF [Aᗮ ⅋ B]) (d₂ : CF [A]) : CF [B] :=
  cutAdmissible A [] [B] d₂ (parInversion Aᗮ B [] d₁)

/-- `⊢ 1 ⊸ (1 ⊕ p)`. -/
def d3 : CF [𝟏ᗮ ⅋ (𝟏 ⊕ p)] :=
  .par ⊥ (𝟏 ⊕ p) [] (.refl _)
    (.bot [𝟏 ⊕ p] (.refl _) (.plus₁ 𝟏 p [] (.refl _) (.one (.refl _))))

-- from it and `⊢ 1`: a derivation of `⊢ 1 ⊕ p`
#guard sketch (mp d3 (.one (.refl _))) == "1⊕(1)"

-- D4: consistency, with no model.
theorem empty_not_cf : CF [] → False := by
  intro d
  cases d with
  | ax _ h => exact nomatch perm_nil_eq h.symm
  | top _ h => exact nomatch perm_nil_eq h.symm
  | wth _ _ _ h _ _ => exact nomatch perm_nil_eq h.symm
  | plus₁ _ _ _ h _ => exact nomatch perm_nil_eq h.symm
  | plus₂ _ _ _ h _ => exact nomatch perm_nil_eq h.symm
  | one h => exact nomatch perm_nil_eq h.symm
  | bot _ h _ => exact nomatch perm_nil_eq h.symm
  | tensor _ _ _ _ h _ _ => exact nomatch perm_nil_eq h.symm
  | par _ _ _ h _ => exact nomatch perm_nil_eq h.symm

theorem consistent : Fam [] → False := fun d => empty_not_cf (cutElimination _ d)

-- D5: the disjunction property, and its failure in a context.
example : Derivable [𝟏 ⊕ p] → Derivable [𝟏] ∨ Derivable [p] := disjunctionProperty 𝟏 p

theorem no_disjunction_in_context :
    ¬ ∀ (A B : Form) (Γ : List Form),
      Derivable ((A ⊕ B) :: Γ) → Derivable (A :: Γ) ∨ Derivable (B :: Γ) := fun h =>
  (h p q [pᗮ & qᗮ] (by decide +kernel)).elim (by decide +kernel) (by decide +kernel)

/-! ## Section 5.8 and D6 to D8: interpolation -/

/-- The derivation without cut that the proved search returns. -/
def cfOf (Γ : List Form) (h : (searchCF Γ).isSome = true := by decide +kernel) : CF Γ :=
  (searchCF Γ).get h

-- The two interpolants displayed in 5.8.
example : (craigInterpolation [(p ⊗ (q ⊕ r))ᗮ] [(p ⊗ q) ⊕ (p ⊗ r)] (cfOf _)).C
    = (p ⊗ q) ⊕ (p ⊗ r) := by decide +kernel
example : (craigInterpolation [(p ⊗ q)ᗮ] [(p ⊗ ⊤) ⊕ r] (cfOf _)).C = p ⊗ ⊤ := by decide +kernel

-- D6.
example : (craigInterpolation [(p & q)ᗮ] [p ⊕ r] (cfOf _)).C = p := by decide +kernel

-- The six uniform interpolants displayed in 5.8, and D7.
example : forallP 0 (p ⅋ pᗮ) = 𝟏 := by decide +kernel
example : existsP 0 (p ⊗ pᗮ) = ⊥ := by decide +kernel
example : forallP 0 (pᗮ ⅋ (p ⊗ q)) = q := by decide +kernel
example : existsP 0 (p ⊗ (pᗮ ⅋ q)) = q := by decide +kernel
example : forallP 0 (p ⅋ p) = 𝟎 := by decide +kernel
example : existsP 0 (p ⊗ q) = ⊤ ⊗ q := by decide +kernel
example : existsP 0 (p & q) = q := by decide +kernel

-- D8.
example : Derivable [forallP 0 ((p ⊗ q) ⅋ pᗮ), qᗮ] :=
  (ui_spec 0 [(p ⊗ q) ⅋ pᗮ]).2.2 [qᗮ] (by decide) (by decide +kernel)

/-! ## Section 6 and Part E: the semantics, in Lean -/

-- E1
example : Valid [pᗮ ⅋ (p & p)] := by decide +kernel
example : ¬ Valid [pᗮ ⅋ (p ⊗ p)] := by decide +kernel

-- E2: from the definitions: `G ⊂ G⊥⊥`, and every dual is a fact.
theorem sub_dual_dual (P : PhaseSpace) (G : P.M → Prop) (m : P.M) (h : G m) :
    P.dual (P.dual G) m := fun n hn => by
  rw [P.mul_comm]
  exact hn m h

theorem dual_is_fact (P : PhaseSpace) (G : P.M → Prop) : P.IsFact (P.dual G) := fun m =>
  ⟨fun h n hn => h n (sub_dual_dual P G n hn), sub_dual_dual P (P.dual G) m⟩

-- E3: validity is closed under cut.
theorem valid_cut (A : Form) (Γ Δ : List Form) (h₁ : Valid (A :: Γ)) (h₂ : Valid (Aᗮ :: Δ)) :
    Valid (Γ ++ Δ) :=
  let ⟨d₁⟩ := completeness _ h₁
  let ⟨d₂⟩ := completeness _ h₂
  soundness _ ⟨(cutAdmissible A Γ Δ d₁ d₂).toFam⟩

-- 6.3: a finite structure, where there is no derivation
example : ∃ M : PhaseStructure, M.Finite ∧ ¬ M.Sat [pᗮ ⅋ (p ⊗ p)] :=
  finite_countermodel _ (by decide +kernel)

/-- info: 'MALL.TutorialTest.mp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mp

/-- info: 'MALL.TutorialTest.consistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms consistent

/--
info: 'MALL.TutorialTest.no_disjunction_in_context' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms no_disjunction_in_context

/-- info: 'MALL.TutorialTest.sub_dual_dual' does not depend on any axioms -/
#guard_msgs in
#print axioms sub_dual_dual

/-- info: 'MALL.TutorialTest.dual_is_fact' does not depend on any axioms -/
#guard_msgs in
#print axioms dual_is_fact

/-- info: 'MALL.TutorialTest.valid_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valid_cut

end MALL.TutorialTest
