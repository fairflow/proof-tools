/-
Finite phase structures as certificates: the certifiers, and a producer
that looks for a structure among a few small ones.

* `noValidBy.verdict Γ z : ¬ Valid Γ` and
  `noDerivableBy.verdict Γ z : ¬ Derivable Γ`: the kernel computes the
  interpretation of `Γ` in the structure `z` (`MALL/Model.lean`).
* `refuteBy Γ` is the producer: not trusted, and not complete.  It tries
  every structure on ℤ/1, ℤ/2, ℤ/3 where the sequent has at most two
  letters, and otherwise "weights": ℤ/2 or ℤ/3 with the antiphases {0}
  and a letter's fact one phase, so that a sequent of letters, ⊗ and ⅋
  holds exactly if its weights sum to 0.

Theory file for the certifiers (it ends with its bound on axioms); the
producer is code.
-/
import MALL.Model
import MALL.Results
import LeanCertify

namespace MALL

/-- **Finite phase structures, checked against validity.** -/
def noValidBy : Certify.Certifier (List Form) ZModel (fun Γ => Valid Γ → False) where
  check Γ z := z.refutes Γ
  sound _ z h := z.not_valid_of_refutes h

/-- The same against derivability: by soundness. -/
def noDerivableBy : Certify.Certifier (List Form) ZModel (fun Γ => Derivable Γ → False) where
  check Γ z := z.refutes Γ
  sound _ z h := z.not_derivable_of_refutes h

#certify_structural MALL.noValidBy
#certify_statement MALL.noValidBy
#certify_structural MALL.noDerivableBy
#certify_statement MALL.noDerivableBy

/-! ## The producer -/

/-- The subset of `0, …, m−1` whose members are the bits of `b`. -/
def bitsSet (m b : Nat) : List Bool := (List.range m).map fun i => b.testBit i

/-- The set of one phase. -/
def single (m w : Nat) : List Bool := (List.range m).map fun i => i == w

/-- Every structure on ℤ/m for letters numbered below `n`. -/
def allOn (m n : Nat) : List ZModel := Id.run do
  let sets := (List.range (2 ^ m)).map (bitsSet m)
  let mut vals : List (List (List Bool)) := [[]]
  for _ in List.range n do
    vals := vals.flatMap fun v => sets.map fun s => s :: v
  return sets.flatMap fun b => vals.map fun v => ⟨m - 1, b, v⟩

/-- The structures of weights on ℤ/m for letters numbered below `n`: the
antiphases {0}; all weights 0 but one letter's, or all weights 1. -/
def weightsOn (m n : Nat) : List ZModel :=
  let mk (w : Nat → Nat) : ZModel := ⟨m - 1, single m 0, (List.range n).map fun a => single m (w a)⟩
  mk (fun _ => 1) :: (List.range n).map fun a => mk fun b => if b == a then 1 else 0

/-- **The producer of countermodels**: the first of the structures tried
that refutes the sequent. -/
def refuteBy (Γ : List Form) : Option ZModel :=
  let n := ((Γ.flatMap Form.letters).foldl max 0) + 1
  let small := if n ≤ 2 then [1, 2, 3].flatMap fun m => allOn m n else []
  let cands := small ++ [2, 3].flatMap fun m => weightsOn m n
  cands.find? fun z => z.refutes Γ

end MALL

#axioms_within_file [propext, Quot.sound]
