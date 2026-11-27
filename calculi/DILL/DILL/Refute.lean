/-
The producer of saturated sets.

Code: nothing here is trusted, and the file has no bound on axioms.  The
kernel checks what it returns (`noCFBySet`, `DILL/SatRun.lean`).

* `Refute.der Δ C` is a search, upwards from `· ; Δ ⟹ C`, that remembers
  every sequent it settles.  It answers `false` of a sequent ("no") only
  after it has tried every instance of every rule that concludes it and
  found, for each, a premise of which it has answered `false`.  So the
  sequents settled "no" are, by the way the search works, a saturated set
  (`DILL/Saturated.lean`).
* The search has no copy and no !L, and its unrestricted zone is always
  empty.  A sequent that is no axiom and has `!A` in its linear zone is
  **set aside**: it is a member of no saturated set (the premise of !L
  has `A` in the unrestricted zone, and then the premise of copy is asked
  for without end), so the search answers `true` of it, which here means
  "not a member of a saturated set", and counts it.  Every premise of the
  other rules is smaller than its conclusion, so the search ends.
* `refuteSet j` is the set of the sequents settled "no", cut down to the
  members that the witnesses need from `j` on, and checked with
  `refutedFast` (the certifiers' check) before it is handed on.  It is `none` at once where the
  unrestricted zone of `j` is not empty, and `none` where the search
  answers `true` of `j`: then `j` has a derivation without cut, or a
  sequent was set aside on the way and `j` has no saturated set.
  `Refute.outcome` says which.

Not proved, and not needed by any fact: that the search finds a set
whenever one exists (the saturated sets are closed under union, and the
search computes membership in the largest).
-/
import DILL.SatFast
import DILL.Tactic
import Std.Data.HashMap

namespace DILL

namespace Refute

/-! ## Sequents in a fixed order, as keys -/

/-- A formula as a list of numbers, in prefix order: the key of a
formula in the tables, and what the formulas of a zone are sorted by. -/
def code : Form → List Nat → List Nat
  | .atom n, acc => 0 :: n :: acc
  | .one, acc => 1 :: acc
  | .top, acc => 2 :: acc
  | .zero, acc => 3 :: acc
  | .tensor A B, acc => 4 :: code A (code B acc)
  | .lolli A B, acc => 5 :: code A (code B acc)
  | .wth A B, acc => 6 :: code A (code B acc)
  | .plus A B, acc => 7 :: code A (code B acc)
  | .bang A, acc => 8 :: code A acc

/-- The order of the dictionary on lists of numbers. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => a < b || (a == b && lexLt l m)

/-- A zone in a fixed order of its formulas. -/
def canon (Δ : List Form) : List Form :=
  ((Δ.toArray.map fun A => (code A [], A)).qsort fun a b => lexLt a.1 b.1).toList.map (·.2)

/-- The key of a sequent with an empty unrestricted zone: its linear zone
in the fixed order, and its conclusion. -/
abbrev Key := List (List Nat) × List Nat

def key (Δ : List Form) (C : Form) : Key :=
  (((Δ.toArray.map fun A => code A []).qsort lexLt).toList, code C [])

def keyOf (j : Seq) : Key := key j.lin j.goal

/-! ## The search -/

/-- What the search holds: the answer for every sequent it has settled,
and the number of sequents set aside for a `!` in the linear zone. -/
structure St where
  memo : Std.HashMap Key Bool := {}
  aside : Nat := 0

def isBang : Form → Bool
  | .bang _ => true
  | _ => false

/-- Is `· ; Δ ⟹ C` outside every saturated set?  `true`: it has a
derivation without cut, or it was set aside, or one of its rule
instances has only such premises.  `false`: every rule instance that
concludes it has a premise settled `false`.  Every answer is kept. -/
partial def der (Δ : List Form) (C : Form) : StateM St Bool := do
  let Δ := canon Δ
  let k := key Δ C
  match (← get).memo[k]? with
  | some b => return b
  | none =>
    let b ←
      if Sat.isAxiom ([] ⨾ Δ ⟹ C) then pure true
      else if Δ.any isBang then do
        modify fun s => { s with aside := s.aside + 1 }
        pure true
      else do
        let right ← match C with
          | .lolli A B => der (A :: Δ) B
          | .wth A B => der Δ A <&&> der Δ B
          | .plus A B => der Δ A <||> der Δ B
          | .bang A => if Δ.isEmpty then der [] A else pure false
          | .tensor A B => (Dec.splits Δ).anyM fun p => der p.1 A <&&> der p.2 B
          | _ => pure false
        if right then pure true
        else (Dec.picks Δ).anyM fun (X, Γ) =>
          match X with
          | .tensor A B => der (A :: B :: Γ) C
          | .one => der Γ C
          | .plus A B => der (A :: Γ) C <&&> der (B :: Γ) C
          | .wth A B => der (A :: Γ) C <||> der (B :: Γ) C
          | .lolli A B => (Dec.splits Γ).anyM fun p => der p.1 A <&&> der (B :: p.2) C
          | _ => pure false
    modify fun s => { s with memo := s.memo.insert k b }
    return b

/-- The answer for a sequent, with everything settled on the way. -/
def search (Δ : List Form) (C : Form) : Bool × St := (der Δ C).run {}

/-- Is the sequent among those settled "no"? -/
def no (s : St) (j : Seq) : Bool := s.memo[keyOf j]? == some false

/-! ## The set, from the sequent on -/

/-- **The rule instances that conclude `· ; Δ ⟹ C`**, each as the list of
its premises of which one is to be a member of the set.  Where a rule
asks for both of two premises (⊕R₁ and ⊕R₂, &L₁ and &L₂) each is a list
of its own.  As `Sat.satR` and `Sat.satL` read them. -/
def instances (Δ : List Form) (C : Form) : List (List Seq) :=
  (match C with
    | .lolli A B => [[[] ⨾ A :: Δ ⟹ B]]
    | .wth A B => [[[] ⨾ Δ ⟹ A, [] ⨾ Δ ⟹ B]]
    | .plus A B => [[[] ⨾ Δ ⟹ A], [[] ⨾ Δ ⟹ B]]
    | .bang A => if Δ.isEmpty then [[[] ⨾ [] ⟹ A]] else []
    | .tensor A B => (Dec.splits Δ).map fun p => [[] ⨾ p.1 ⟹ A, [] ⨾ p.2 ⟹ B]
    | _ => []) ++
  (Dec.picks Δ).flatMap fun (X, Γ) =>
    match X with
    | .tensor A B => [[[] ⨾ A :: B :: Γ ⟹ C]]
    | .one => [[[] ⨾ Γ ⟹ C]]
    | .plus A B => [[[] ⨾ A :: Γ ⟹ C, [] ⨾ B :: Γ ⟹ C]]
    | .wth A B => [[[] ⨾ A :: Γ ⟹ C], [[] ⨾ B :: Γ ⟹ C]]
    | .lolli A B => (Dec.splits Γ).map fun p => [[] ⨾ p.1 ⟹ A, [] ⨾ B :: p.2 ⟹ C]
    | _ => []

/-- A sequent with its linear zone in the fixed order. -/
def canonSeq (j : Seq) : Seq := j.unr ⨾ canon j.lin ⟹ j.goal

/-- How a premise is chosen where a rule instance has two settled "no"
and neither is in the set yet: the first, or the one with the shorter
linear zone. -/
inductive Choice where
  | first
  | shortest
  deriving Repr, BEq

def pick (s : St) (ch : Choice) (g : List Seq) : Option Seq :=
  let nos := g.filter (no s)
  match ch with
  | .first => nos.head?
  | .shortest => nos.foldl (fun best c =>
      match best with
      | none => some c
      | some b => if c.lin.length < b.lin.length then some c else some b) none

/-- **The members that the witnesses need.**  For each rule instance that
concludes a member: nothing, where a premise is a member already; else a
premise settled "no" becomes a member.  The members are kept in the order
in which they were added. -/
partial def closure (s : St) (ch : Choice) (todo : List Seq)
    (seen : Std.HashMap Key Unit) (out : Array Seq) : Array Seq :=
  match todo with
  | [] => out
  | d :: rest =>
    let (seen, out, new) := (instances d.lin d.goal).foldl
      (fun (acc : Std.HashMap Key Unit × Array Seq × List Seq) g =>
        let (seen, out, new) := acc
        if g.any fun c => seen.contains (keyOf c) then acc
        else match pick s ch g with
          | some c =>
            let c := canonSeq c
            (seen.insert (keyOf c) (), out.push c, c :: new)
          | none => acc)
      (seen, out, [])
    closure s ch (new.reverse ++ rest) seen out

/-- The set for a sequent settled "no", not checked. -/
def setOf (s : St) (ch : Choice) (j : Seq) : List Seq :=
  let j := canonSeq j
  (closure s ch [j] (({} : Std.HashMap Key Unit).insert (keyOf j) ()) #[j]).toList

/-- What the producer found. -/
inductive Outcome where
  /-- A saturated set of which the sequent is a member; `refutedFast`
  accepts it. -/
  | refuted (D : List Seq)
  /-- The search found a derivation without cut, and set nothing aside. -/
  | derivable
  /-- No saturated set: the unrestricted zone is not empty, or the search
  answered `true` with sequents set aside for a `!` in the linear zone. -/
  | noSet (why : String)
  /-- The set made does not check: a defect of this file. -/
  | defect (D : List Seq)

/-- The producer, with the reason where it gives no set. -/
def outcome (j : Seq) (ch : Choice := .first) : Outcome :=
  if !j.unr.isEmpty then .noSet "the unrestricted zone is not empty"
  else
    let (b, s) := search j.lin j.goal
    if b then
      if s.aside == 0 then .derivable
      else .noSet (if s.aside == 1 then "1 sequent with ! in the linear zone was set aside"
        else s!"{s.aside} sequents with ! in the linear zone were set aside")
    else
      let D := setOf s ch j
      if refutedFast D j then .refuted D else .defect D

/-! ## Printing -/

/-- A sequent as Lean source, with the notations of `DILL.Form` (the
atoms 0 to 3 are written `p q r s`). -/
def srcSeq (j : Seq) : String :=
  srcForms j.unr ++ " ⨾ " ++ srcForms j.lin ++ " ⟹ " ++ j.goal.srcIn false

/-- A set of sequents as Lean source. -/
def srcSet (D : List Seq) : String := "[" ++ ", ".intercalate (D.map srcSeq) ++ "]"

end Refute

/-- **The producer of saturated sets**: for a sequent with an empty
unrestricted zone whose failed search needs no sequent with `!` in a
linear zone, a saturated set of which it is a member.  Not trusted: the
kernel checks the set. -/
def refuteSet (j : Seq) : Option (List Seq) :=
  match Refute.outcome j with
  | .refuted D => some D
  | _ => none

end DILL
