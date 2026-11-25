/-
Screens of the statements of `GLS/Semantics.lean`, on small cases, by
evaluation: run before the proofs (`campaign/statements.md` says what each
showed).  Code, not theory: an untrusted bounded search and an enumeration
of small trees.  A screen that fails is a `#guard` that fails the build.
-/
import GLS.Tactic
import GLS.Semantics

namespace GLS.Screen

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-- Derivable in GLS by a derivation of height at most `n`: every rule
tried at every principal formula.  Not trusted. -/
def within : Nat → Seq → Bool
  | 0, _ => false
  | n + 1, s =>
    (candidates s).any fun m =>
      match (S.step m s).toOption with
      | some ps => ps.all (within n)
      | none => false

/-- The least height of a derivation, up to the bound. -/
def minHeight (bound : Nat) (s : Seq) : Option Nat :=
  (List.range (bound + 1)).find? (fun n => within n s)

/-- Small formulas: over `p`, `q`, `⊥`, one connective, and a few of two. -/
def forms0 : List Form := [p, q, ⊥]
def forms1 : List Form :=
  forms0 ++ [□p, □q, □⊥, p ⟶ q, q ⟶ p, p ⟶ ⊥, p ⟶ p]
def forms2 : List Form :=
  forms1 ++ [□□p, □(p ⟶ q), □p ⟶ p, □p ⟶ q, p ⟶ □p, □p ⟶ □q, □(□p ⟶ p), (p ⟶ q) ⟶ p, □(p ⟶ ⊥)]

/-- Lists of at most two members of a list. -/
def upTo2 (l : List Form) : List (List Form) :=
  [[]] ++ l.map (fun a => [a]) ++ (l.flatMap fun a => l.map fun b => [a, b])

/-- Small sequents. -/
def seqs1 : List Seq := (upTo2 forms1).flatMap fun Γ => (upTo2 forms1).map fun Δ => Γ ⇒ Δ
def seqsSmall : List Seq :=
  ((upTo2 forms0 ++ forms2.map (fun a => [a])).flatMap fun Γ =>
    (upTo2 forms0 ++ forms2.map (fun a => [a])).map fun Δ => Γ ⇒ Δ)

/-- Small trees over `p`, `q`: of depth at most 2, at most two children. -/
def vals : List (List Nat) := [[], [0], [1], [0, 1]]
def trees0 : List Tree := vals.map fun v => .node v []
def trees1 : List Tree :=
  trees0 ++ (vals.flatMap fun v => trees0.map fun t => .node v [t]) ++
    (vals.flatMap fun v => trees0.flatMap fun t => trees0.map fun u => .node v [t, u])
def trees2 : List Tree :=
  trees1 ++ (vals.flatMap fun v => (trees1.take 20).map fun t => .node v [t]) ++
    ([[], [0]].flatMap fun v => (trees1.take 8).flatMap fun t => (trees1.take 8).map fun u => .node v [t, u])

/-- Every proper descendant too: the worlds a tree gives. -/
def worlds (ts : List Tree) : List Tree := ts.flatMap fun t => t :: t.desc

/-! ## Soundness, rule by rule

For each small sequent and each move that applies, and each small tree
and each of its subtrees as a world: the world does not refute the
conclusion while refuting no premise. -/

def soundAt (s : Seq) (ws : List Tree) : Bool :=
  (candidates s).all fun m =>
    match (S.step m s).toOption with
    | some ps => ws.all fun w => !(s.refutedAt w) || ps.any (fun pr => pr.refutedAt w)
    | none => true

-- The propositional rules and the axioms: at each world separately.
#guard seqs1.all fun s =>
  (candidates s).all fun m =>
    match m, (S.step m s).toOption with
    | .glr _, _ => true
    | _, some ps => (worlds trees1).all fun w => !(s.refutedAt w) || ps.any (fun pr => pr.refutedAt w)
    | _, none => true

-- GLR: a world refutes its conclusion only if a descendant refutes its premise.
#guard (seqsSmall ++ seqs1.take 400).all fun s =>
  (candidates s).all fun m =>
    match m, (S.step m s).toOption with
    | .glr _, some ps => (worlds trees2).all fun w =>
        !(s.refutedAt w) || ps.any (fun pr => w.desc.any fun u => pr.refutedAt u)
    | _, _ => true

/-! ## Soundness and completeness, on the whole

A small sequent that the bounded search derives is refuted at no small
tree; one that it does not derive within height 8 is refuted at one. -/

def refuted (s : Seq) : Bool := (worlds trees2).any fun w => s.refutedAt w

#guard seqsSmall.all fun s => !(within 8 s) || !(refuted s)
#guard (seqsSmall.filter fun s => !(within 8 s) && !(refuted s)).length == 0

-- the known theorems and non-theorems of the plan
#guard within 8 ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q])
#guard within 8 ([] ⇒ [□p ⟶ □□p])
#guard within 8 ([] ⇒ [□(□p ⟶ p) ⟶ □p])
#guard !(within 10 ([] ⇒ [□p ⟶ p])) && refuted ([] ⇒ [□p ⟶ p])
#guard !(within 10 ([] ⇒ [p])) && refuted ([] ⇒ [p])
#guard !(within 10 ([] ⇒ [□⊥ ⟶ ⊥])) && refuted ([] ⇒ [□⊥ ⟶ ⊥])
#guard !(within 10 ([] ⇒ [□(□p ⟶ p)])) && refuted ([] ⇒ [□(□p ⟶ p)])
#guard !(within 10 ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)])) && refuted ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)])

/-! ## The identity, cut, and the structural statements with heights -/

-- identity: every small formula on both sides
#guard forms2.all fun A => within 8 ([A] ⇒ [A])

-- cut, at the head and inside: if both premises are derivable so is the conclusion
#guard (upTo2 forms0 ++ [[□p], [p ⟶ q], [□p, p]]).all fun Γ =>
  (upTo2 forms0 ++ [[□p], [□q, q]]).all fun Δ =>
    forms2.all fun A =>
      !(within 7 (Γ ⇒ A :: Δ) && within 7 (A :: Γ ⇒ Δ)) || within 9 (Γ ⇒ Δ)

/-- `a ≤ b` for least heights, where `none` is "no derivation within the bound". -/
def le (a b : Option Nat) : Bool :=
  match a, b with
  | _, none => true
  | some m, some n => m ≤ n
  | none, some _ => false

-- weakening on the left and on the right, no higher
#guard seqsSmall.all fun s =>
  forms1.all fun A =>
    le (minHeight 7 (A :: s.ant ⇒ s.suc)) (minHeight 7 s) &&
    le (minHeight 7 (s.ant ⇒ A :: s.suc)) (minHeight 7 s)

-- a control: the converse fails (a weakened sequent can be lower), so the
-- comparison of least heights is able to say no
#guard !(seqsSmall.all fun s =>
  forms1.all fun A => le (minHeight 7 s) (minHeight 7 (A :: s.ant ⇒ s.suc)))

-- exchange: a sequent and its two lists reversed have the same least height
#guard seqsSmall.all fun s => minHeight 7 s == minHeight 7 (s.ant.reverse ⇒ s.suc.reverse)

-- contraction on the left and on the right, no higher
#guard seqsSmall.all fun s =>
  forms2.all fun A =>
    le (minHeight 7 (A :: s.ant ⇒ s.suc)) (minHeight 7 (A :: A :: s.ant ⇒ s.suc)) &&
    le (minHeight 7 (s.ant ⇒ A :: s.suc)) (minHeight 7 (s.ant ⇒ A :: A :: s.suc))

-- the inversions, no higher
#guard (seqsSmall ++ seqs1.take 300).all fun s =>
  (s.suc.all fun C => match C with
    | A ⟶ B => le (minHeight 7 (A :: s.ant ⇒ B :: s.suc.erase (A ⟶ B))) (minHeight 7 s)
    | _ => true) &&
  (s.ant.all fun C => match C with
    | A ⟶ B => le (minHeight 7 (s.ant.erase (A ⟶ B) ⇒ A :: s.suc)) (minHeight 7 s) &&
               le (minHeight 7 (B :: s.ant.erase (A ⟶ B) ⇒ s.suc)) (minHeight 7 s)
    | _ => true)

#eval (seqsSmall.length, seqs1.length, (worlds trees2).length, (seqsSmall.filter (within 8)).length)

end GLS.Screen
