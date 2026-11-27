/-
The producer of saturated sets, and the phase structure of a set,
computed.

Code: nothing here is trusted, and the file has no bound on axioms.

* `Refute.search Γ` is a search for a derivation without cut that
  remembers every sequent it has settled.  Where it settles that `Γ` has
  no derivation, the sequents it settled so are, by the way it works, a
  saturated set: it says "no" of a sequent only after trying every rule
  instance and finding a premise of which it has said "no".
* `refuteSet Γ` is that set, cut down to the members that the witnesses
  need.  The kernel checks it (`noDerivableBySet`, `MALL/SatRun.lean`).
* `Table` is the phase structure that a set presents
  (`MALL/Saturated.lean`, `satModel`), with its phases listed and its
  product tabulated, and the interpretation of Definition 1.14 computed in
  it.  This is not needed by any proof: it is there so that the
  countermodel can be looked at, and so that the theorem
  `satModel_refutes` can be seen to hold of what is computed.
-/
import MALL.SatRun
import MALL.Tactic
import Std.Data.HashMap

namespace MALL

deriving instance Ord for Form
deriving instance Hashable for Form

namespace Refute

/-- A sequent in a fixed order of its formulas. -/
def canon (Γ : List Form) : List Form :=
  (Γ.toArray.qsort fun a b => compare a b == .lt).toList

abbrev Memo := Std.HashMap (List Form) Bool

/-- The logical axiom, at any formula. -/
def isAx : List Form → Bool
  | [A, B] => B == Aᗮ
  | _ => false

/-- The ways to divide a list in which equal formulas stand together, each
way once: `k` copies of a formula are divided in `k + 1` ways, where
`splits` (`MALL/Decide.lean`) gives the same pairs `2 ^ k` times over. -/
partial def msplits : List Form → List (List Form × List Form)
  | [] => [([], [])]
  | a :: l =>
    let k := (l.takeWhile (· == a)).length + 1
    let sub := msplits (l.dropWhile (· == a))
    (List.range (k + 1)).flatMap fun j =>
      sub.map fun (p, q) => (List.replicate j a ++ p, List.replicate (k - j) a ++ q)

mutual
/-- Has the sequent a derivation without cut?  Every answer is kept. -/
partial def der (Γ : List Form) : StateM Memo Bool := do
  let k := canon Γ
  match (← get)[k]? with
  | some b => return b
  | none =>
    let b ← if isAx k || k == [𝟏] || k.contains ⊤ then pure true else derAt k (picks k)
    modify (·.insert k b)
    return b

/-- Each formula of the sequent in turn as the principal one. -/
partial def derAt (k : List Form) : List (Form × List Form) → StateM Memo Bool
  | [] => return false
  | (X, Γ) :: ps => do
    let here ← match X with
      | .bot => der Γ
      | .par A C => der (A :: C :: Γ)
      | .wth A C => do if ← der (A :: Γ) then der (C :: Γ) else pure false
      | .plus A C => do if ← der (A :: Γ) then pure true else der (C :: Γ)
      | .tensor A C => derSplits A C (msplits Γ)
      | _ => pure false
    if here then return true else derAt k ps

/-- Each way to divide the context of a ⊗. -/
partial def derSplits (A C : Form) : List (List Form × List Form) → StateM Memo Bool
  | [] => return false
  | (Γ, Δ) :: qs => do
    let here ← do if ← der (A :: Γ) then der (C :: Δ) else pure false
    if here then return true else derSplits A C qs
end

/-- The answer for a sequent, with everything settled on the way. -/
def search (Γ : List Form) : Bool × Memo := (der Γ).run {}

/-- Is the sequent among those settled "no"? -/
def no (m : Memo) (Γ : List Form) : Bool := m[canon Γ]? == some false

/-- The premises that witness that a sequent settled "no" satisfies the
condition of saturation: for each rule instance, the first premise settled
"no". -/
def witnesses (m : Memo) (d : List Form) : List (List Form) :=
  (picks d).flatMap fun (X, Γ) =>
    match X with
    | .bot => [Γ]
    | .par A C => [A :: C :: Γ]
    | .wth A C => if no m (A :: Γ) then [A :: Γ] else [C :: Γ]
    | .plus A C => [A :: Γ, C :: Γ]
    | .tensor A C => (msplits Γ).map fun (Γ₁, Γ₂) =>
        if no m (A :: Γ₁) then A :: Γ₁ else C :: Γ₂
    | _ => []

/-- The members that the witnesses need, from the sequent on. -/
partial def closure (m : Memo) (todo : List (List Form)) (seen : Std.HashMap (List Form) Unit) :
    List (List Form) :=
  match todo with
  | [] => seen.toList.map (·.1)
  | d :: rest =>
    let k := canon d
    if seen.contains k then closure m rest seen
    else closure m (witnesses m k ++ rest) (seen.insert k ())

end Refute

/-- **The producer of saturated sets**: for a sequent with no derivation,
a saturated set of which it is a member.  Not trusted: the kernel checks
the set. -/
def refuteSet (Γ : List Form) : Option (List (List Form)) :=
  let (b, m) := Refute.search Γ
  if b then none else some (Refute.closure m [Γ] {})

/-! ## The phase structure of a set, computed -/

/-- The phase structure presented by a set of sequents, as tables.  The
phases are numbered: the parts of the members, in a fixed order, and last
the phase of every other sequent. -/
structure Table where
  /-- The parts of the members. -/
  parts : Array (List Form)
  /-- The product of two phases. -/
  mul : Array (Array Nat)
  /-- The antiphases. -/
  bot : Array Bool

namespace Table

/-- The sublists of a list. -/
def sublists : List Form → List (List Form)
  | [] => [[]]
  | a :: l => let r := sublists l; r ++ r.map (a :: ·)

/-- The structure of a set. -/
def ofSet (D : List (List Form)) : Table := Id.run do
  let mut idx : Std.HashMap (List Form) Nat := {}
  let mut parts : Array (List Form) := #[]
  for d in D do
    for s in sublists d do
      let k := Refute.canon s
      if !idx.contains k then
        idx := idx.insert k parts.size
        parts := parts.push k
  let n := parts.size
  let members : Std.HashMap (List Form) Unit := D.foldl (fun h d => h.insert (Refute.canon d) ()) {}
  let mul := (Array.range (n + 1)).map fun i => (Array.range (n + 1)).map fun j =>
    if i == n || j == n then n
    else (idx[Refute.canon (parts[i]! ++ parts[j]!)]?).getD n
  let bot := (Array.range (n + 1)).map fun i => i == n || !members.contains parts[i]!
  return ⟨parts, mul, bot⟩

variable (T : Table)

/-- The number of phases. -/
def card : Nat := T.parts.size + 1

/-- The number of a sequent's phase. -/
def phase (Γ : List Form) : Nat :=
  (T.parts.findIdx? (· == Refute.canon Γ)).getD T.parts.size

def times (i j : Nat) : Nat := (T.mul[i]!)[j]!

/-- The dual of a set of phases (Definition 1.2). -/
def dual (G : Array Bool) : Array Bool :=
  (Array.range T.card).map fun p => (Array.range T.card).all fun q => !G[q]! || T.bot[T.times p q]!

/-- The product of two sets of phases. -/
def prod (G H : Array Bool) : Array Bool := Id.run do
  let mut out := Array.replicate T.card false
  for p in Array.range T.card do
    if G[p]! then
      for q in Array.range T.card do
        if H[q]! then out := out.set! (T.times p q) true
  return out

/-- The fact of a letter: `{a}⊥`. -/
def val (a : Nat) : Array Bool :=
  let e := T.phase [.atom a]
  (Array.range T.card).map fun p => T.bot[T.times e p]!

/-- The interpretation of a formula, by the clauses of
`PhaseStructure.interp`. -/
def interp : Form → Array Bool
  | .atom a => T.val a
  | .natom a => T.dual (T.val a)
  | .one => T.dual T.bot
  | .bot => T.bot
  | .top => Array.replicate T.card true
  | .zero => T.dual (Array.replicate T.card true)
  | .tensor A B => T.dual (T.dual (T.prod (interp A) (interp B)))
  | .par A B => T.dual (T.prod (T.dual (interp A)) (T.dual (interp B)))
  | .wth A B => (Array.range T.card).map fun p => (interp A)[p]! && (interp B)[p]!
  | .plus A B =>
    T.dual (T.dual ((Array.range T.card).map fun p => (interp A)[p]! || (interp B)[p]!))

/-- The sequent holds in the structure: the unit is in the interpretation
of its par. -/
def holds (Γ : List Form) : Bool := (T.interp (parAll Γ))[T.phase []]!

/-- A set of phases, as text. -/
def showSet (G : Array Bool) : String :=
  "{" ++ ", ".intercalate
    (((List.range T.card).filter fun i => G[i]!).map fun i =>
      if i == T.parts.size then "∞" else showSeq T.parts[i]!) ++ "}"

end Table

/-- The countermodel of a sequent, described: the set, the phases, the
antiphases among them, and that the sequent does not hold. -/
def describeCountermodel (Γ : List Form) : String :=
  match refuteSet Γ with
  | none => showSeq Γ ++ " has a derivation"
  | some D =>
    let T := Table.ofSet D
    showSeq Γ ++ s!"\n  is refuted by a saturated set of {D.length} sequents:\n    " ++
      "\n    ".intercalate (D.map showSeq) ++
      s!"\n  It presents a phase structure of {T.card} phases: the parts of those sequents, and ∞ for every other sequent." ++
      s!"\n  The antiphases are the phases that are not among the {D.length}." ++
      s!"\n  Computed in it, the sequent holds: {T.holds Γ}."

end MALL
