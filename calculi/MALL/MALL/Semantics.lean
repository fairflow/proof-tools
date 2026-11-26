/-
The phase semantics of the multiplicatives and additives.

Source: J.-Y. Girard, *Linear logic*, TCS 50 (1987), Section 1:
Definitions 1.1 (phase space), 1.2 (dual), 1.3 (fact), 1.8 (the
multiplicatives), 1.11 (the additives), 1.14 (phase structure,
interpretation, validity), and the reading of a sequent in the proof of
Proposition 1.16, p. 23.  A set of phases is a predicate.  Theory file: it
ends with its bound on axioms.
-/
import MALL.System

namespace MALL

/-- **A phase space** (Definition 1.1): "(i) a monoid … supposed to be
commutative, i.e., neutrality: 1p = p1 = p …, commutativity: pq = qp …,
associativity: (pq)r = p(qr) …; (ii) a set ⊥, the set of antiphases". -/
structure PhaseSpace where
  /-- The phases. -/
  M : Type
  /-- The product of two phases. -/
  mul : M → M → M
  /-- The unit phase, the source's `1`. -/
  one : M
  /-- Neutrality, on the left. -/
  one_mul : ∀ p, mul one p = p
  /-- Neutrality, on the right. -/
  mul_one : ∀ p, mul p one = p
  /-- Commutativity. -/
  mul_comm : ∀ p q, mul p q = mul q p
  /-- Associativity. -/
  mul_assoc : ∀ p q r, mul (mul p q) r = mul p (mul q r)
  /-- The antiphases, the source's `⊥`. -/
  bot : M → Prop

namespace PhaseSpace

variable (P : PhaseSpace)

/-- **The dual** of a set of phases (Definition 1.2):
`G⊥ = {p ; ∀q (q ∈ G → pq ∈ ⊥)}`. -/
def dual (G : P.M → Prop) : P.M → Prop := fun p => ∀ q, G q → P.bot (P.mul p q)

/-- **A fact** (Definition 1.3): "a subset G of P such that G⊥⊥ = G". -/
def IsFact (G : P.M → Prop) : Prop := ∀ p, P.dual (P.dual G) p ↔ G p

/-- The product of two sets of phases (Definition 1.8):
`GH = {pq ; p ∈ G and q ∈ H}`. -/
def prod (G H : P.M → Prop) : P.M → Prop := fun r => ∃ p q, G p ∧ H q ∧ r = P.mul p q

end PhaseSpace

/-- **A phase structure** (Definition 1.14(i)): "a phase space and, for
each propositional letter a, a fact a_S". -/
structure PhaseStructure extends PhaseSpace where
  /-- The fact of each letter. -/
  val : Nat → M → Prop
  /-- It is a fact. -/
  val_fact : ∀ a, toPhaseSpace.IsFact (val a)

namespace PhaseStructure

variable (S : PhaseStructure)

/-- **The interpretation of a proposition** (Definition 1.14(ii): "in a
completely straightforward way"), by the definitions on facts: the dual of
a letter is the dual of its fact (1.7); `1 = ⊥⊥` (1.5(ii)), `⊤ = P`
(1.5(iii)), `0 = ⊤⊥` (1.5(iv)); `G ⊗ H = (G.H)⊥⊥` and
`G ⅋ H = (G⊥.H⊥)⊥` (1.8); `G & H = G ∩ H` and `G ⊕ H = (G ∪ H)⊥⊥`
(1.11). -/
def interp : Form → S.M → Prop
  | .atom a => S.val a
  | .natom a => S.dual (S.val a)
  | .one => S.dual S.bot
  | .bot => S.bot
  | .top => fun _ => True
  | .zero => S.dual (fun _ => True)
  | .tensor A B => S.dual (S.dual (S.prod (interp A) (interp B)))
  | .par A B => S.dual (S.prod (S.dual (interp A)) (S.dual (interp B)))
  | .wth A B => fun p => interp A p ∧ interp B p
  | .plus A B => S.dual (S.dual (fun p => interp A p ∨ interp B p))

end PhaseStructure

/-- **A sequent as a formula** (the proof of 1.16, p. 23): "⊢ A must be
read as the *par* of its components (and, when the list is void, as
⊥)". -/
def parAll : List Form → Form
  | [] => ⊥
  | [A] => A
  | A :: B :: Γ => A ⅋ parAll (B :: Γ)

/-- The sequent is **valid in the phase structure** (Definition
1.14(iii)): the unit phase is in its interpretation. -/
def PhaseStructure.Sat (S : PhaseStructure) (Γ : List Form) : Prop :=
  S.interp (parAll Γ) S.one

/-- **A linear tautology** (Definition 1.14(iv)): valid in every phase
structure. -/
def Valid (Γ : List Form) : Prop := ∀ S : PhaseStructure, S.Sat Γ

/-- The phase structure is **finite**: a list has every phase. -/
def PhaseStructure.Finite (S : PhaseStructure) : Prop := ∃ l : List S.M, ∀ m : S.M, m ∈ l

end MALL

#axioms_within_file [propext, Quot.sound]
