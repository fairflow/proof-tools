/-
Tests of the uniform interpolants (`GLS/Interpolation.lean`) and of the
defined connectives (`GLS/Connectives.lean`, `GLS/ConnectiveRules.lean`),
by the search: equivalences in GL decided, countermodels shown, and a
battery of random formulas against a pool of consequences.  Code: every
answer is pinned.
-/
import GLS.ConnectiveRules
import GLS.InterpolationVars
import GLS.SearchTest

namespace GLS.InterpolationTest

open GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1
abbrev r : Form := .var 2

/-- The search derives the sequent. -/
def proves (s : Seq) : Bool := (proofOrRef s).isLeft

/-- `A` and `B` are equivalent in GL. -/
def equiv (A B : Form) : Bool := proves ([A] ⇒ [B]) && proves ([B] ⇒ [A])

/-- The tree the search returns, if it refutes the sequent. -/
def counter (s : Seq) : Option Tree :=
  match proofOrRef s with
  | .inl _ => none
  | .inr r => some r.1

/-! ## Uniform interpolants of a few formulas, `p` the variable 0 -/

-- ∃p.(p ∧ ¬p) ≡ ⊥
#guard equiv (uiExists 0 (p ⋏ p.neg)) ⊥
-- ∃p.(p ∧ □¬p) ≡ ⊤: a root where p holds, and no p below
#guard equiv (uiExists 0 (p ⋏ □p.neg)) Form.top
-- ∃p.(□(p → q) ∧ □p) ≡ □q
#guard equiv (uiExists 0 (□(p ⟶ q) ⋏ □p)) (□q)
-- ∃p.(□(p ↔ q) ∧ ◇p) ≡ ◇q, with p ↔ q written as two implications
#guard equiv (uiExists 0 (□((p ⟶ q) ⋏ (q ⟶ p)) ⋏ p.dia)) q.dia
-- ∃p.(□p ∧ ◇¬p) ≡ ⊥, and ∃p.(□p ∧ ¬p) ≡ ⊤
#guard equiv (uiExists 0 (□p ⋏ p.neg.dia)) ⊥
#guard equiv (uiExists 0 (□p ⋏ p.neg)) Form.top
-- ∀p.(□p → p) ≡ ⊥: p false at the root, true below, refutes it at every tree
#guard equiv (uiForall 0 (□p ⟶ p)) ⊥
-- ∀p of Löb's axiom ≡ ⊤
#guard equiv (uiForall 0 (□(□p ⟶ p) ⟶ □p)) Form.top
-- ∀p.(q → □p) ≡ q → □⊥
#guard equiv (uiForall 0 (q ⟶ □p)) (q ⟶ □⊥)
-- no p in the interpolants
#guard !(uiExists 0 (□(p ⟶ q) ⋏ □p)).occ 0
#guard !(uiForall 0 (q ⟶ □p)).occ 0

/-! ## A battery: random formulas, and every consequence from a pool -/

/-- All formulas up to a depth over the variables `vs`. -/
def pool (vs : List Nat) : Nat → List Form
  | 0 => ⊥ :: vs.map Form.var
  | n + 1 =>
    let P := pool vs n
    P ++ P.map Form.box ++ P.flatMap fun A => P.map fun B => A ⟶ B

/-- The consequences tried: formulas in `q`, `r` of depth one, and some
of their boxes and diamonds. -/
def consequences : List Form :=
  let P := pool [1, 2] 1
  P ++ P.map (fun A => □□A) ++ P.map (fun A => (□A).dia) ++ P.map (fun A => □(A ⟶ □A)) ++
    P.map (fun A => □(□A ⟶ A) ⟶ □A)

/-- A step of a linear congruential generator. -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A random formula of depth at most `d` over `vs`. -/
def rnd (vs : List Nat) : Nat → Nat → Form × Nat
  | 0, s =>
    let s1 := lcg s
    let k := s1 % (vs.length + 1)
    (if h : k < vs.length then .var vs[k] else ⊥, s1)
  | d + 1, s =>
    let s1 := lcg s
    if s1 % 5 == 0 then rnd vs 0 s1
    else if s1 % 5 == 1 || s1 % 5 == 2 then
      let (A, s2) := rnd vs d s1
      (□A, s2)
    else
      let (A, s2) := rnd vs d s1
      let (B, s3) := rnd vs d s2
      (A ⟶ B, s3)

/-- For each formula: `A ⇒ ∃p.A`, `∃p.A` free of `p`, and every consequence
`B` in the pool with `A ⇒ B` has `∃p.A ⇒ B`.  The failures, the number of
consequences checked, the number of formulas. -/
def battery (vs : List Nat) (d n seed : Nat) : List Form × Nat × Nat :=
  let tests := (List.range n).map fun i => (rnd vs d (i * 7919 + seed)).1
  let res := tests.map fun A =>
    let E := uiExists 0 A
    let cons := consequences.filter fun B => proves ([A] ⇒ [B])
    (A, proves ([A] ⇒ [E]) && !E.occ 0 && cons.all (fun B => proves ([E] ⇒ [B])), cons.length)
  ((res.filter fun x => !x.2.1).map (·.1), (res.map (·.2.2)).sum, res.length)

/-- info: ([], 1527, 40) -/
#guard_msgs in
#eval battery [0, 1, 2] 3 40 977

/-! ## The size of the interpolant, simplified -/

/-- The largest interpolant over a battery, and the mean size. -/
def sizes (f : Form → Form) (d n seed : Nat) : Nat × Nat :=
  let xs := (List.range n).map fun i => (f (rnd [0, 1, 2] d (i * 7919 + seed)).1).size
  (xs.foldl max 0, xs.sum / n)

-- simplified (`uiExists`) and without the shortcut (`uiSeqRaw`, which has
-- the depth bound), on the battery above
/-- info: ((33, 4), 109, 10) -/
#guard_msgs in
#eval (sizes (uiExists 0) 3 40 977, sizes (fun A => uiSeqRaw 0 [A] []) 3 40 977)

-- the formula with no `p` whose interpolant had 11 010 757 nodes before
-- the simplification
#guard (uiExists 0 (□□q ⟶ (q.neg ⟶ □r))).size == 10
#guard equiv (uiExists 0 (□□q ⟶ (q.neg ⟶ □r))) (□□q ⟶ (q.neg ⟶ □r))

-- the simplified and the raw interpolant are equivalent, as `holds_uiSeq_raw` says
#guard (List.range 20).all fun i =>
  let A := (rnd [0, 1, 2] 3 (i * 7919 + 977)).1
  equiv (uiExists 0 A) (uiSeqRaw 0 [A] [])

/-! ## The defined connectives under the box -/

#guard proves ([] ⇒ [□(p ⋏ q) ⟶ (□p ⋏ □q)])
#guard proves ([] ⇒ [(□p ⋏ □q) ⟶ □(p ⋏ q)])
#guard proves ([] ⇒ [(□p ⋎ □q) ⟶ □(p ⋎ q)])
#guard !proves ([] ⇒ [□(p ⋎ q) ⟶ (□p ⋎ □q)])
#guard proves ([] ⇒ [(p ⋎ q).dia ⟶ (p.dia ⋎ q.dia)])
#guard proves ([] ⇒ [(p.dia ⋎ q.dia) ⟶ (p ⋎ q).dia])
-- GL's diamond: a last world where p holds
#guard proves ([] ⇒ [p.dia ⟶ (p ⋏ □p.neg).dia])
-- the comma: `p, q ⇒ r` iff `⇒ p ∧ q → r`; `p ⇒ q, r` iff `⇒ p → q ∨ r`
#guard proves ([p, q] ⇒ [p ⋏ q]) && proves ([p ⋎ q] ⇒ [p, q])
#guard !proves ([p ⋎ q] ⇒ [p]) && !proves ([q] ⇒ [p ⋏ q])
-- Peirce's law, classical
#guard proves ([] ⇒ [((p ⟶ q) ⟶ p) ⟶ p])

-- The countermodel to `□(p ∨ q) → □p ∨ □q`: two children, one with `q`
-- and one with `p`.
/-- info: some (Tree.node [] [Tree.node [1] [], Tree.node [0] []]) -/
#guard_msgs in
#eval counter ([] ⇒ [□(p ⋎ q) ⟶ (□p ⋎ □q)])

/-! ## The intuitionistic variants, read classically (`campaign/2026-11-26-intuitionistic.md`) -/

-- strong Löb, (□A → A) → A, is classically □A ∨ A; at A := ⊥ it is □⊥
#guard equiv ((□p ⟶ p) ⟶ p) (□p ⋎ p)
#guard equiv ((□⊥ ⟶ ⊥) ⟶ ⊥) (□⊥)
-- GL proves neither □⊥, nor ¬¬□⊥, nor p → □p, nor Leivant's principle
#guard !proves ([] ⇒ [□⊥]) && !proves ([] ⇒ [(□⊥).neg.neg]) && !proves ([] ⇒ [p ⟶ □p])
#guard !proves ([] ⇒ [□(p ⋎ q) ⟶ □(□p ⋎ q)])
-- one instance of p → □p, at p := ¬□⊥, already gives □⊥ in GL
#guard proves ([] ⇒ [((□⊥).neg ⟶ □(□⊥).neg) ⟶ □⊥])
-- with □⊥, every instance of strong Löb and of p → □p holds
#guard proves ([□⊥] ⇒ [(□p ⟶ p) ⟶ p]) && proves ([□⊥] ⇒ [p ⟶ □p])


/-! ## The statements of the reports, pinned (`campaign/2026-11-26-*.md` quote these) -/

/--
info: def GLS.uniformInterpolation : UniformInterpolation
  where GLS.UniformInterpolation :=
    (p : Nat) → (A : Form) → UIFor p A
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uniformInterpolation

/--
info: def GLS.uniformInterpolationSeq : UniformInterpolationSeq
  where GLS.UniformInterpolationSeq :=
    (p : Nat) → (Γ Δ : List Form) → UISeqFor p Γ Δ
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uniformInterpolationSeq

/--
info: theorem GLS.uiSeq_iff (p : Nat) (Γ Δ : List Form) (t : Tree) :
  (uiSeq p Γ Δ).holds t = true ↔ ∃ t', Bisim p t t' ∧ (Γ ⇒ Δ).refutedAt t' = true
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uiSeq_iff

/--
info: theorem GLS.uiSeq_free (p : Nat) (Γ Δ : List Form) : Form.occ p (uiSeq p Γ Δ) = false
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uiSeq_free

/--
info: theorem GLS.uiSeqRaw_mdepth (p : Nat) (Γ Δ : List Form) : (uiSeqRaw p Γ Δ).mdepth ≤ 2 * (Γ ⇒ Δ).boxes.length
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uiSeqRaw_mdepth

/--
info: theorem GLS.holds_bisim {p : Nat} (B : Form) (hB : Form.occ p B = false) {a b : Tree} :
  Bisim p a b → B.holds a = B.holds b
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.holds_bisim

/--
info: def GLS.Fam.andL (A B : Form) {Γ Δ : List Form} (d : Fam (A :: B :: Γ ⇒ Δ)) : Fam ((A ⋏ B) :: Γ ⇒ Δ)
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.Fam.andL

/--
info: def GLS.Fam.andR (A B : Form) {Γ Δ : List Form} (d₁ : Fam (Γ ⇒ A :: Δ)) (d₂ : Fam (Γ ⇒ B :: Δ)) : Fam (Γ ⇒ (A ⋏ B) :: Δ)
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.Fam.andR

/--
info: def GLS.Fam.orL (A B : Form) {Γ Δ : List Form} (d₁ : Fam (A :: Γ ⇒ Δ)) (d₂ : Fam (B :: Γ ⇒ Δ)) : Fam ((A ⋎ B) :: Γ ⇒ Δ)
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.Fam.orL

/--
info: def GLS.Fam.orR (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A :: B :: Δ)) : Fam (Γ ⇒ (A ⋎ B) :: Δ)
PROVED · axioms: propext
-/
#guard_msgs in #statement GLS.Fam.orR

/--
info: def GLS.Fam.diaL (A : Form) {Γ Δ : List Form} (d : Fam (A :: (xbox Γ ++ [□(A ⟶ ⊥)]) ⇒ [])) : Fam (A.dia :: Γ ⇒ Δ)
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.Fam.diaL

/--
info: def GLS.switchRL (A : Form) {Γ Δ : List Form} :
  (Fam (Γ ⇒ A :: Δ) → Fam (A.neg :: Γ ⇒ Δ)) × (Fam (A.neg :: Γ ⇒ Δ) → Fam (Γ ⇒ A :: Δ))
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.switchRL

/--
info: def GLS.switchLR (A : Form) {Γ Δ : List Form} :
  (Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ A.neg :: Δ)) × (Fam (Γ ⇒ A.neg :: Δ) → Fam (A :: Γ ⇒ Δ))
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.switchLR

/--
info: def GLS.seqFormula (Γ Δ : List Form) :
  (Fam (Γ ⇒ Δ) → Fam ([] ⇒ [conjL Γ ⟶ disjL Δ])) × (Fam ([] ⇒ [conjL Γ ⟶ disjL Δ]) → Fam (Γ ⇒ Δ))
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.seqFormula

/--
info: def GLS.peirce (p q : Nat) : Fam ([] ⇒ [((Form.var p ⟶ Form.var q) ⟶ Form.var p) ⟶ Form.var p])
PROVED · axioms: propext
-/
#guard_msgs in #statement GLS.peirce

/-! ## The condition on variables (`GLS/InterpolationVars.lean`) -/

/-- The variables of a formula, by a second definition (`Form.occ` is the
one the statements use). -/
def vars : Form → List Nat
  | .var q => [q]
  | ⊥ => []
  | A ⟶ B => vars A ++ vars B
  | □A => vars A

/-- Every formula over `p`, `q`, `r` built in at most `d` layers. -/
def layers : Nat → List Form
  | 0 => [p, q, r, ⊥]
  | d + 1 =>
    let fs := layers d
    fs ++ fs.map Form.box ++ (fs.flatMap fun A => fs.map fun B => A ⟶ B)

/-- Every variable of `E` is one of `A`, and is not the variable `x`. -/
def varsOK (x : Nat) (A E : Form) : Bool :=
  (vars E).all fun y => y != x && (vars A).contains y

-- the screen of the statements, run before their proofs: the 624 formulas
-- of at most two layers, each of the three variables, both quantifiers
#guard (layers 2).length == 624
#guard (layers 2).all fun A =>
  [0, 1, 2].all fun x => varsOK x A (uiExists x A) && varsOK x A (uiForall x A)

-- a variable of the formula that the interpolant does lose, and one it keeps
#guard vars (uiExists 0 (p ⋏ q)) == [1]
#guard vars (uiExists 0 ((p ⟶ q) ⋏ (r ⟶ p))) |>.all fun y => y == 1 || y == 2

/--
info: theorem GLS.uiSeq_vars : UiSeqVars
  where GLS.UiSeqVars :=
    ∀ (p q : Nat) (Γ Δ : List Form),
      (∀ (A : Form), A ∈ Γ ++ Δ → Form.occ q A = false) → Form.occ q (uiSeq p Γ Δ) = false
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uiSeq_vars

/--
info: def GLS.uniformInterpolationVars : UniformInterpolationVars
  where GLS.UniformInterpolationVars :=
    (p : Nat) →
      (A : Form) →
        { u //
          ∀ (q : Nat),
            (Form.occ q u.ex = true → Form.occ q A = true) ∧ (Form.occ q u.all = true → Form.occ q A = true) }
PROVED · axioms: Quot.sound, propext
-/
#guard_msgs in #statement GLS.uniformInterpolationVars

end GLS.InterpolationTest
