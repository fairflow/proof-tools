/-
The solutions of the exercises of `tutorial.md`, and every claim that
page makes about a particular sequent, checked.  The sections are the
tutorial's parts.  Every message is pasted from Lean's output.
-/
import GLS.Explore
import GLS.CutRule
import GLS.PS

namespace GLS.TutorialTest

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1
abbrev r : Form := .var 2

/-- `¬A`, as the tutorial writes it. -/
abbrev neg (A : Form) : Form := A ⟶ ⊥

/-- The moves that apply at a sequent, as the tactic writes them. -/
def offered (j : Seq) : List String :=
  ((candidates j).filter fun m => (S.step m j).toOption.isSome).map Move.src

/-- What a move leaves, as the goals are shown. -/
def leaves (m : Move) (j : Seq) : Option (List String) :=
  (S.step m j).toOption.map (·.map Seq.show)

instance (s : Seq) : Decidable (Valid s) := validDecidable s

/-! ## The worked example of section 2: Löb's axiom -/

def lob : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
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
#eval IO.println lob.render

#guard leaves (.impR □(□p ⟶ p) □p) ([] ⇒ [□(□p ⟶ p) ⟶ □p]) == some ["□(□p → p) ⇒ □p"]
#guard leaves (.glr p) ([□(□p ⟶ p)] ⇒ [□p]) == some ["□p → p, □(□p → p), □p ⇒ p"]
#guard leaves (.impL □p p) ([□p ⟶ p, □(□p ⟶ p), □p] ⇒ [p])
  == some ["□(□p → p), □p ⇒ □p, p", "p, □(□p → p), □p ⇒ p"]
#guard leaves (.glr p) ([□(□p ⟶ p), □p] ⇒ [□p, p])
  == some ["□p → p, □(□p → p), p, □p, □p ⇒ p"]
#guard (famOfDer lob).height == 5

/-! ## Part A: the propositional rules -/

-- A1
def a1a : Der S ([p] ⇒ [p]) := by
  glsmove idP 0

def a1b : Der S ([⊥] ⇒ [q]) := by
  glsmove botL

-- A2
def a2 : Der S ([] ⇒ [p ⟶ q ⟶ p]) := by
  glsmove impR p (q ⟶ p)
  glsmove impR q p
  glsmove idP 0

-- A3: Peirce's law.  The succedent holds two formulas after the second move.
def a3 : Der S ([] ⇒ [((p ⟶ q) ⟶ p) ⟶ p]) := by
  glsmove impR ((p ⟶ q) ⟶ p) p
  glsmove impL (p ⟶ q) p
  glsmove impR p q
  glsmove idP 0
  glsmove idP 0

#guard leaves (.impL (p ⟶ q) p) ([(p ⟶ q) ⟶ p] ⇒ [p]) == some ["⇒ p → q, p", "p ⇒ p"]
#guard leaves (.impR p q) ([] ⇒ [p ⟶ q, p]) == some ["p ⇒ q, p"]

-- A4: double negation.
def a4 : Der S ([] ⇒ [neg (neg p) ⟶ p]) := by
  glsmove impR (neg (neg p)) p
  glsmove impL (neg p) ⊥
  glsmove impR p ⊥
  glsmove idP 0
  glsmove botL

-- A5: `⇒ p → q` has no derivation.
#guard leaves (.impR p q) ([] ⇒ [p ⟶ q]) == some ["p ⇒ q"]
#guard offered ([p] ⇒ [q]) == []
example : ¬ Derivable ([] ⇒ [p ⟶ q]) := noDerivable.verdict _ (.node [0] [])

/-! ## Part B: the modal rule -/

-- B1: the identity on a boxed variable.
def b1 : Der S ([□p] ⇒ [□p]) := by
  glsmove glr p
  glsmove idP 0

#guard leaves (.glr p) ([□p] ⇒ [□p]) == some ["p, □p, □p ⇒ p"]

-- B2: a box on a theorem.
def b2 : Der S ([] ⇒ [□(p ⟶ p)]) := by
  glsmove glr (p ⟶ p)
  glsmove impR p p
  glsmove idP 0

#guard leaves (.glr (p ⟶ p)) ([] ⇒ [□(p ⟶ p)]) == some ["□(p → p) ⇒ p → p"]

-- B3: K.
def b3 : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove impR □(p ⟶ q) (□p ⟶ □q)
  glsmove impR □p □q
  glsmove glr q
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

#guard leaves (.glr q) ([□p, □(p ⟶ q)] ⇒ [□q]) == some ["p, □p, p → q, □(p → q), □q ⇒ q"]

-- B4: 4.
def b4 : Der S ([] ⇒ [□p ⟶ □□p]) := by
  glsmove impR □p □□p
  glsmove glr □p
  glsmove glr p
  glsmove idP 0

#guard leaves (.glr □p) ([□p] ⇒ [□□p]) == some ["p, □p, □□p ⇒ □p"]

-- B5: `□⊥ → □p`.
def b5 : Der S ([] ⇒ [□⊥ ⟶ □p]) := by
  glsmove impR □⊥ □p
  glsmove glr p
  glsmove botL

-- B6: Löb's axiom is `lob` above.

-- B7: the second incompleteness theorem, formalised: `¬□⊥ → ¬□¬□⊥`.
def b7 : Der S ([] ⇒ [neg □⊥ ⟶ neg □(neg □⊥)]) := by
  glsmove impR (neg □⊥) (neg □(neg □⊥))
  glsmove impR □(neg □⊥) ⊥
  glsmove impL □⊥ ⊥
  glsmove glr ⊥
  glsmove impL □⊥ ⊥
  glsmove glr ⊥
  glsmove botL
  glsmove botL
  glsmove botL

/--
info: ⇒ (□⊥ → ⊥) → □(□⊥ → ⊥) → ⊥   by ImpR (□⊥ → ⊥) → □(□⊥ → ⊥) → ⊥
  □⊥ → ⊥ ⇒ □(□⊥ → ⊥) → ⊥   by ImpR □(□⊥ → ⊥) → ⊥
    □(□⊥ → ⊥), □⊥ → ⊥ ⇒ ⊥   by ImpL □⊥ → ⊥
      □(□⊥ → ⊥) ⇒ □⊥, ⊥   by GLR □⊥
        □⊥ → ⊥, □(□⊥ → ⊥), □⊥ ⇒ ⊥   by ImpL □⊥ → ⊥
          □(□⊥ → ⊥), □⊥ ⇒ □⊥, ⊥   by GLR □⊥
            □⊥ → ⊥, □(□⊥ → ⊥), ⊥, □⊥, □⊥ ⇒ ⊥   by BotL
          ⊥, □(□⊥ → ⊥), □⊥ ⇒ ⊥   by BotL
      ⊥, □(□⊥ → ⊥) ⇒ ⊥   by BotL
-/
#guard_msgs in
#eval IO.println b7.render

-- Section 2: GLR is not invertible.  `⇒ □p, □(p → p)` is derivable, and
-- the premise of GLR on `□p` is not.
#guard (proofOrRef ([] ⇒ [□p, □(p ⟶ p)])).isLeft
#guard leaves (.glr p) ([] ⇒ [□p, □(p ⟶ p)]) == some ["□p ⇒ p"]
#guard (proofOrRef ([□p] ⇒ [p])).isRight

/-! ## Part C: countermodels -/

/--
info: ⇒ □p → p
  is not derivable in GLS: it is false at the root of
{}
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [□p ⟶ p]))

-- C1
#guard leaves (.impR □p p) ([] ⇒ [□p ⟶ p]) == some ["□p ⇒ p"]
#guard offered ([□p] ⇒ [p]) == []
example : ¬ Derivable ([] ⇒ [□p ⟶ p]) := noDerivable.verdict _ (.node [] [])

-- C2: `□□p → □p`: a root that sees one world, where p is false.
example : ¬ Derivable ([] ⇒ [□□p ⟶ □p]) := noDerivable.verdict _ (.node [] [.node [] []])
-- a single world does not do: there `□p` is true
#guard !(([] : List Form) ⇒ [□□p ⟶ □p]).refutedAt (.node [] [])

/--
info: ⇒ □□p → □p
  is not derivable in GLS: it is false at the root of
{}
  {}
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [□□p ⟶ □p]))

/--
info: ⇒ (□p → □q) → □(p → q)
  is not derivable in GLS: it is false at the root of
{}
  {}
  {p}
-/
#guard_msgs in
#eval IO.println (explain ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]))

-- C3: the converse of K.
example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (.node [] [.node [] [], .node [0] []])
-- one world below the root does not do, whether p is true there or not
#guard !(([] : List Form) ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]).refutedAt (.node [] [.node [0] []])
#guard !(([] : List Form) ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]).refutedAt (.node [] [.node [] []])
-- the two need not be siblings: a chain refutes it too
example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (.node [] [.node [] [.node [0] []]])

-- C4: consistency is not derivable: `¬□⊥` is false at a world that sees nothing.
example : ¬ Derivable ([] ⇒ [neg □⊥]) := noDerivable.verdict _ (.node [] [])

-- C5: Löb's axiom is about provability: `□(□p → p) ⇒ p` is not derivable.
example : ¬ Derivable ([□(□p ⟶ p)] ⇒ [p]) := noDerivable.verdict _ (.node [] [])

-- C6: `□□□⊥ → □□⊥`: a chain of three worlds, and no shorter one.
def chain : Nat → Tree
  | 0 => .node [] []
  | n + 1 => .node [] [chain n]

example : ¬ Derivable ([] ⇒ [□□□⊥ ⟶ □□⊥]) := noDerivable.verdict _ (chain 2)
#guard !(([] : List Form) ⇒ [□□□⊥ ⟶ □□⊥]).refutedAt (chain 1)
#guard !(([] : List Form) ⇒ [□□□⊥ ⟶ □□⊥]).refutedAt (chain 0)

/-- `□ⁿ⊥`. -/
def boxes : Nat → Form → Form
  | 0, A => A
  | n + 1, A => □(boxes n A)

-- `□ⁿ⊥` is true at the top of a chain of k+1 worlds exactly when k < n
#guard (List.range 5).all fun n => (List.range 5).all fun k =>
  (boxes n ⊥).holds (chain k) == decide (k < n)

/-! ## Part D: the theorems, used -/

-- D1: the height of the identity.
def d1 : Fam ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) := Fam.id (□(p ⟶ q)) (by decide) (by decide)
#guard d1.height == 4

-- D2: necessitation.
def nec {A : Form} (d : Fam ([] ⇒ [A])) : Fam ([] ⇒ [□A]) :=
  .glr A (List.mem_singleton.2 rfl) (weakeningL (□A) (Γ0 := []) (Γ1 := []) d).1

-- D3: modus ponens.
def mp {A B : Form} (d₁ : Fam ([] ⇒ [A ⟶ B])) (d₂ : Fam ([] ⇒ [A])) : Fam ([] ⇒ [B]) :=
  let i : Fam ([A] ⇒ [B]) := by
    simpa using (inversionImpR A B d₁ (List.mem_singleton.2 rfl)).1
  cutBySource A [] [] [] [B] (weakeningR B (Δ0 := [A]) (Δ1 := []) d₂).1 i

-- D4: Löb's rule.
def lobRule {A : Form} (d : Fam ([] ⇒ [□A ⟶ A])) : Fam ([] ⇒ [A]) :=
  let i : Fam ([□A] ⇒ [A]) := by
    simpa using (inversionImpR (□A) A d (List.mem_singleton.2 rfl)).1
  cutBySource (□A) [] [] [] [A] (.glr A (List.mem_cons_self ..) i) i

-- the three, run
def idp : Fam ([] ⇒ [p ⟶ p]) := famOfDer (by glsmove impR p p; glsmove idP 0)
#guard (nec idp).height == 3
def a2' : Der S ([] ⇒ [(p ⟶ p) ⟶ q ⟶ p ⟶ p]) := by
  apply_script (found ([] ⇒ [(p ⟶ p) ⟶ q ⟶ p ⟶ p])).getD []
-- from  ⇒ (p → p) → q → p → p  and  ⇒ p → p:  a derivation of  ⇒ q → p → p
#guard (mp (famOfDer a2') idp).height == 3

def lobPremise : Der S ([] ⇒ [□(p ⟶ p) ⟶ p ⟶ p]) := by
  apply_script (found ([] ⇒ [□(p ⟶ p) ⟶ p ⟶ p])).getD []
-- from  ⇒ □(p → p) → p → p:  a derivation of  ⇒ p → p
#guard (lobRule (famOfDer lobPremise)).height == 2

-- D5: a cut in GLS + (cut), eliminated.
def byTheSearch (s : Seq) : Option (Fam s) :=
  match proofOrRef s with
  | .inl d => some d
  | .inr _ => none

def withCut : Option (FamCut ([□p] ⇒ [□□□p])) :=
  match byTheSearch ([□p] ⇒ [□□p, □□□p]), byTheSearch ([□□p, □p] ⇒ [□□□p]) with
  | some d₁, some d₂ => some (.cut (□□p) d₁.toCut d₂.toCut)
  | _, _ => none

#guard (withCut.map fun d =>
  ((cutElimination _ d).height, (cutEliminationBySearch _ d).height)) == some (4, 4)

-- D6: consistency, with no model.
theorem empty_not_derivable : Fam ([] ⇒ []) → False := fun d => nomatch d

theorem consistent : FamCut ([] ⇒ []) → False := fun d =>
  empty_not_derivable (cutElimination _ d)

-- D7: GLS does not derive `□⊥`, with no model.
theorem box_bot_not_derivable : Fam ([] ⇒ [□⊥]) → False := by
  intro d
  cases d with
  | idP _ h => simp at h
  | botL h => simp at h
  | impR _ _ h => simp at h
  | impL _ _ h => simp at h
  | glr A h d =>
    simp at h
    subst h
    cases d with
    | idP _ h => simp [xbox] at h
    | botL h => simp [xbox] at h
    | impR _ _ h => simp at h
    | impL _ _ h => simp [xbox] at h
    | glr _ h => simp at h

-- D8: what GLR does to a multiset.
/-- The antecedents met when GLR is used `k` times, each time on the one
formula of the succedent, from `□ⁿp ⇒ □ⁿ⁺¹p`: their lengths. -/
def glrLengths (n k : Nat) : List Nat :=
  let rec go : Nat → Seq → List Nat
    | 0, s => [s.ant.length]
    | k + 1, s =>
      match s.suc with
      | [□A] => s.ant.length :: go k (xbox s.ant ++ [□A] ⇒ [A])
      | _ => [s.ant.length]
  go k ([boxes n p] ⇒ [boxes (n + 1) p])

#guard glrLengths 6 6 == [1, 3, 7, 15, 31, 63, 127]
#guard (xbox [□□p, □q, r, p ⟶ q]).map Form.show == ["□p", "□□p", "q", "□q"]

/-! ## Part E: the semantics, in Lean -/

-- E1
example : Valid ([] ⇒ [□p ⟶ □□p]) := by decide +kernel
example : ¬ Valid ([] ⇒ [□p ⟶ p]) := by decide +kernel

-- E2: no world of a model of GL sees itself.
theorem irrefl (M : Model) (h : M.GL) (w : M.W) : ¬ M.R w w := by
  induction w using h.cwf.induction with
  | _ w ih => exact fun hww => ih w hww hww

-- E3: Löb's axiom is true at every world of every model of GL, two-valued
-- or not.
theorem lob_true (M : Model) (h : M.GL) (A : Form) (w : M.W) :
    M.sat w (□(□A ⟶ A) ⟶ □A) := by
  intro hbox v hwv
  induction v using h.cwf.induction with
  | _ v ih => exact hbox v hwv fun u hvu => ih u hvu (h.trans _ _ _ hwv hvu)

-- E4: the axiom T fails in a model of GL: by soundness and one tree.
example : ¬ Valid ([] ⇒ [□p ⟶ p]) := noValid.verdict _ (.node [] [])

/-- info: 'GLS.TutorialTest.nec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nec

/-- info: 'GLS.TutorialTest.mp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mp

/-- info: 'GLS.TutorialTest.lobRule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lobRule

/-- info: 'GLS.TutorialTest.consistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms consistent

/-- info: 'GLS.TutorialTest.box_bot_not_derivable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms box_bot_not_derivable

/-- info: 'GLS.TutorialTest.irrefl' does not depend on any axioms -/
#guard_msgs in
#print axioms irrefl

/-- info: 'GLS.TutorialTest.lob_true' does not depend on any axioms -/
#guard_msgs in
#print axioms lob_true

end GLS.TutorialTest
