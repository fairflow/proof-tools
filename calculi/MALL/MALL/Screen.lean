/-
Screens of the statements, kept so that they can be run again: the phase
semantics evaluated in small finite phase structures, by a Boolean
evaluator that is not proved (it is a screen, not a certifier), and the
decision procedure beside it.

The structures are the cyclic groups ℤ/n for n ≤ 4, with every set of
antiphases and every assignment of facts to the letters `p`, `q`.  A set
of phases is a list of Booleans.

What is screened.  *Soundness and completeness* (S4, S5 of
`campaign/statements.md`): every sequent of the first list is valid in
all of these structures and is decided derivable; every sequent of the
second list is refuted by one of them and is decided not derivable.
*What "valid" means* (the plan, stage 0): the same lists.  A control is at
the end.

Code, not theory.
-/
import MALL.Results

namespace MALL.Screen

open MALL

/-- A set of phases of ℤ/n, as a list of `n` Booleans. -/
abbrev SetB := List Bool

/-- Membership. -/
def mem (G : SetB) (i : Nat) : Bool := G.getD i false

/-- A phase structure on ℤ/n: the antiphases, and a set for each letter. -/
structure Z where
  n : Nat
  bot : SetB
  val : List SetB

def Z.tab (z : Z) (f : Nat → Bool) : SetB := (List.range z.n).map f

def Z.dual (z : Z) (G : SetB) : SetB :=
  z.tab fun p => (List.range z.n).all fun q => !mem G q || mem z.bot ((p + q) % z.n)

def Z.prod (z : Z) (G H : SetB) : SetB :=
  z.tab fun r => (List.range z.n).any fun p => (List.range z.n).any fun q =>
    mem G p && mem H q && (r == (p + q) % z.n)

/-- The clauses of `PhaseStructure.interp`, on lists of Booleans. -/
def Z.interp (z : Z) : Form → SetB
  | .atom a => z.val.getD a []
  | .natom a => z.dual (z.val.getD a [])
  | .one => z.dual z.bot
  | .bot => z.bot
  | .top => z.tab fun _ => true
  | .zero => z.dual (z.tab fun _ => true)
  | .tensor A B => z.dual (z.dual (z.prod (z.interp A) (z.interp B)))
  | .par A B => z.dual (z.prod (z.dual (z.interp A)) (z.dual (z.interp B)))
  | .wth A B => let a := z.interp A; let b := z.interp B; z.tab fun p => mem a p && mem b p
  | .plus A B =>
      let a := z.interp A; let b := z.interp B
      z.dual (z.dual (z.tab fun p => mem a p || mem b p))

/-- The clause of `PhaseStructure.Sat`: the unit, 0, is in the
interpretation of the par of the sequent. -/
def Z.sat (z : Z) (Γ : List Form) : Bool := mem (z.interp (parAll Γ)) 0

def ofBits (n k : Nat) : SetB := (List.range n).map fun i => k.testBit i

def Z.isFact (z : Z) (G : SetB) : Bool := z.dual (z.dual G) == G

/-- Every structure on ℤ/n, for two letters. -/
def structs (n : Nat) : List Z := Id.run do
  let mut out := []
  for b in List.range (2 ^ n) do
    let z0 : Z := ⟨n, ofBits n b, []⟩
    let facts := ((List.range (2 ^ n)).map (ofBits n)).filter z0.isFact
    for v0 in facts do
      for v1 in facts do
        out := ⟨n, ofBits n b, [v0, v1]⟩ :: out
  return out

/-- Valid in every structure on ℤ/n, n ≤ 4. -/
def allValid (Γ : List Form) : Bool := [1, 2, 3, 4].all fun n => (structs n).all (·.sat Γ)

/-- The first structure on ℤ/n, n ≤ 4, that refutes the sequent: `n`, the
antiphases, the sets of `p` and `q`. -/
def countermodel (Γ : List Form) : Option (Nat × SetB × List SetB) :=
  ([1, 2, 3, 4].flatMap structs).findSome? fun z =>
    if z.sat Γ then none else some (z.n, z.bot, z.val)

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1

/-- Sequents that the source, or its semantics, makes derivable. -/
def derivable : List (List Form) :=
  [[p, pᗮ], [𝟏], [pᗮ ⅋ p], [⊤, p, q], [⊥, 𝟏], [pᗮ ⅋ (p & p)], [p ⊕ pᗮ, p ⊕ pᗮ],
   [p ⊗ q, pᗮ, qᗮ], [(p ⊗ (q ⊕ 𝟏))ᗮ, (p ⊗ q) ⊕ (p ⊗ 𝟏)],
   [(p ⊗ (q & 𝟏))ᗮ, (p ⊗ q) & (p ⊗ 𝟏)]]

/-- Sequents that must not be: weakening, the empty sequent, `⊢ 0`,
contraction, p. 5 of the source, a letter, `⊢ ⊥`, weakening by 1, the
converse of half-distributivity, the mix rule, `⊢ p ⊗ p⊥`. -/
def notDerivable : List (List Form) :=
  [[𝟏, 𝟏], [], [𝟎], [p ⊕ pᗮ], [pᗮ ⅋ (p ⊗ p)], [p], [⊥], [𝟏, p, pᗮ],
   [((p ⊗ q) & (p ⊗ 𝟏))ᗮ, p ⊗ (q & 𝟏)], [p ⅋ pᗮ, q ⅋ qᗮ], [p ⊗ pᗮ]]

#guard (structs 4).length == 1605

-- soundness, on these: what is derivable is valid in every structure
#guard derivable.all fun Γ => decide (Derivable Γ) && allValid Γ
-- completeness, on these: what is not derivable is refuted by a structure
#guard notDerivable.all fun Γ => !decide (Derivable Γ) && (countermodel Γ).isSome
-- the decision of validity agrees
#guard derivable.all fun Γ => decide (Valid Γ)
#guard notDerivable.all fun Γ => !decide (Valid Γ)

-- the countermodel of `⊢ 1, 1`: ℤ/2 with antiphases {1} (the value is Lean's output)
#guard countermodel [𝟏, 𝟏] == some (2, [false, true], [[true, true], [true, true]])

-- control: the screen can say no (a derivable sequent has no countermodel
-- here, and a sequent that is not derivable is not valid in all)
#guard (countermodel [p, pᗮ]).isNone
#guard !allValid [𝟏, 𝟏]

end MALL.Screen
