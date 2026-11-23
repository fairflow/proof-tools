/-
Nested sequents, and the functions that the rules use on them.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, §2.1.1,
"Nested sequents" and "Sequent contexts, unary", pp. 6–8; Definition 2.12
(subtree) and Definition 2.13 (set sequent), p. 14.  Theory file: it ends
with its bound on axioms.
-/
import BrunnlerK.Form

namespace BrunnlerK

/-- **Nested sequents** (source pp. 6–7).  The source's sequent is a finite
multiset of formulas and boxed sequents, "so it is of the form"

    A₁, …, Aₘ, [Δ₁], …, [Δₙ]

Here it is that form with lists for the two multisets: the boxes one at a
time, and then the formulas.

* `leaf [A₁, …, Aₘ]` is the sequent `A₁, …, Aₘ`, with no box;
* `cons Δ Γ` is the sequent `[Δ], Γ`: the sequent `Γ` with the box `[Δ]`
  put in front of its boxes.

So the sequent displayed above is
`cons Δ₁ (cons Δ₂ (… (cons Δₙ (leaf [A₁, …, Aₘ]))))`.  The empty sequent
is `leaf []`, and an empty box is a box: `cons (leaf []) Γ` is `[∅], Γ`,
which is not `Γ`. -/
inductive NSeq where
  | leaf (fs : List Form)
  | cons (inner : NSeq) (rest : NSeq)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A path into a sequent: positions of boxes, from the root.  The path
`[]` is the root; `[1, 0]` is box 0 of box 1 of the root. -/
abbrev Path := List Nat

namespace NSeq

/-! ## A sequent as a node: its formulas and its boxes -/

/-- The formulas of a sequent: `A₁, …, Aₘ`.  The source's "`A` is *in* `Γ`"
(Definition 2.12) is `A ∈ Γ.forms`. -/
def forms : NSeq → List Form
  | leaf fs => fs
  | cons _ r => r.forms

/-- The boxes of a sequent: `Δ₁, …, Δₙ`, its immediate subtrees
(Definition 2.12). -/
def boxes : NSeq → List NSeq
  | leaf _ => []
  | cons Δ r => Δ :: r.boxes

/-- `Γ.add A` is the sequent `Γ, A`: the formula is put in front of the
formulas of `Γ`. -/
def add : NSeq → Form → NSeq
  | leaf fs, A => leaf (A :: fs)
  | cons Δ r, A => cons Δ (r.add A)

/-- `Γ.erase A` is `Γ` with one `A` taken out of its formulas: the first,
where there are several.  Where `A` is not in `Γ`, it is `Γ`. -/
def erase : NSeq → Form → NSeq
  | leaf fs, A => leaf (fs.erase A)
  | cons Δ r, A => cons Δ (r.erase A)

/-- `Γ.addBox Λ` is the sequent `Γ, [Λ]`: the new box is put after the
boxes of `Γ`, so that the positions of those do not change. -/
def addBox : NSeq → NSeq → NSeq
  | leaf fs, Λ => cons Λ (leaf fs)
  | cons Δ r, Λ => cons Δ (r.addBox Λ)

/-- The box at position `i` of a sequent, counted from 0. -/
def box? : NSeq → Nat → Option NSeq
  | leaf _, _ => none
  | cons Δ _, 0 => some Δ
  | cons _ r, i + 1 => r.box? i

/-- `Γ.setBox i Λ` is `Γ` with the box at position `i` replaced by `[Λ]`.
Where there is no such box, it is `Γ`. -/
def setBox : NSeq → Nat → NSeq → NSeq
  | leaf fs, _, _ => leaf fs
  | cons _ r, 0, Λ => cons Λ r
  | cons Δ r, i + 1, Λ => cons Δ (r.setBox i Λ)

/-! ## A place inside a sequent

The source states every rule for a context `Γ{ }`, a sequent with a hole
(pp. 7–8).  Here the place of the hole is a **path**: the positions of the
boxes entered, from the root.  The path `[]` is the root; `[1, 0]` is box 0
of box 1 of the root.  The depth of the context (source p. 8) is the length
of the path. -/

/-- `Γ.node? a` is the sequent at the path `a` of `Γ`, a subtree of `Γ`
(Definition 2.12): where `Γ` is `Γ{Δ}` and `a` is the place of the hole,
it is `Δ` together with everything else at that node.  `none` where the
path leaves `Γ`. -/
def node? : NSeq → Path → Option NSeq
  | Γ, [] => some Γ
  | Γ, i :: a =>
    match Γ.box? i with
    | some Δ => Δ.node? a
    | none => none

/-- `Γ.setNode a Θ` is `Γ` with the sequent at the path `a` replaced by
`Θ`.  Where the path leaves `Γ`, it is `Γ`. -/
def setNode : NSeq → Path → NSeq → NSeq
  | _, [], Θ => Θ
  | Γ, i :: a, Θ =>
    match Γ.box? i with
    | some Δ => Γ.setBox i (Δ.setNode a Θ)
    | none => Γ

/-! ## Set sequents (Definition 2.13, p. 14)

"The set sequent of the sequent `A₁, …, Aₘ, [Δ₁], …, [Δₙ]` is the
underlying set of `A₁, …, Aₘ, [Λ₁], …, [Λₙ]`, where `Λ₁ … Λₙ` are the set
sequents of `Δ₁ … Δₙ`."  The system `K°` asks whether two sequents have the
same set sequent.  `sameSet` answers that, without building the set. -/

/-- Two lists of formulas with the same underlying set. -/
def sameForms (fs gs : List Form) : Bool :=
  fs.all (fun A => gs.contains A) && gs.all (fun A => fs.contains A)

mutual

/-- `Γ.sameSet Γ'`: the set sequents of `Γ` and `Γ'` are equal.  That is:
they have the same set of formulas; each box of `Γ` has the set sequent of
some box of `Γ'`; and each box of `Γ'` has the set sequent of some box of
`Γ`. -/
def sameSet : NSeq → NSeq → Bool
  | leaf fs, Γ' => sameForms fs Γ'.forms && Γ'.boxes.isEmpty
  | cons Δ r, Γ' =>
    sameForms r.forms Γ'.forms
      && (Γ'.boxes.any (fun Δ' => sameSet Δ Δ') && boxesIn r Γ')
      && Γ'.boxes.all (fun Δ' => sameSet Δ Δ' || hasBox r Δ')

/-- `Γ.boxesIn Γ'`: each box of `Γ` has the set sequent of some box of
`Γ'`. -/
def boxesIn : NSeq → NSeq → Bool
  | leaf _, _ => true
  | cons Δ r, Γ' => Γ'.boxes.any (fun Δ' => sameSet Δ Δ') && boxesIn r Γ'

/-- `Γ.hasBox Δ'`: some box of `Γ` has the set sequent of `Δ'`. -/
def hasBox : NSeq → NSeq → Bool
  | leaf _, _ => false
  | cons Δ r, Δ' => sameSet Δ Δ' || hasBox r Δ'

end

end NSeq

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
