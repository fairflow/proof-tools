/-
The source's own worked derivations, as terms of the family.

Two sources.  First (written before the thesis could be read): the Coq
file's `Id_all_form`.  Second (added 2026-11-25, when the thesis was
read): the thesis's Examples 12.4.1 and 12.4.2, p. 171, at the end of
this file.

The Coq file `GL/GLS_PSGLS_calcs.v` (of `ianshil/CE_GLS`, commit
`3dd8619`) has one: `Id_all_form` (l. 331), the identity on every formula,
`Γ0, A, Γ1 ⇒ Δ0, A, Δ1`, by induction on `A`.  Its four cases are written
here with the constructors of `GLS.Fam`, each at the smallest formula of
its kind, and then once at a formula that uses three of them.  This is a
check of the transcription: it imports the theory file only.

Where the Coq proof puts a formula at a place in a list, the family puts
it at the head (`campaign/rule-table.md`, the divergence log).
-/
import GLS.System

namespace GLS.Source

open GLS

/-- The variable `p`. -/
abbrev p : Form := .var 0
/-- The variable `q`. -/
abbrev q : Form := .var 1

/-- `Id_all_form` at a variable (l. 343): IdP. -/
def idVar : Fam ([q, p] ⇒ [p, q]) := .idP 0 (by decide) (by decide)

/-- `Id_all_form` at `⊥` (l. 346): BotL. -/
def idBot : Fam ([q, ⊥] ⇒ [⊥, q]) := .botL (by decide)

/-- `Id_all_form` at `A1 → A2` (l. 349): ImpR, then ImpL, then the
identity on `A1` and on `A2`.  Here `A1 = p`, `A2 = q`. -/
def idImp : Fam ([p ⟶ q] ⇒ [p ⟶ q]) :=
  .impR p q (by decide)                      -- p, p → q ⇒ q
    (.impL p q (by decide)
      (.idP 0 (by decide) (by decide))       -- p ⇒ p, q
      (.idP 1 (by decide) (by decide)))      -- q, p ⇒ q

/-- `Id_all_form` at `Box A` (l. 362): GLR, then the identity on `A`.
Here `A = p`: the premise of GLR is `p, □p, □p ⇒ p`. -/
def idBox : Fam ([□p] ⇒ [□p]) :=
  .glr p (by decide) (.idP 0 (by decide) (by decide))

/-- The premise of GLR at an antecedent that mixes boxed formulas and
others, with a boxed formula twice: each boxed formula gives its body and
itself, in order, and the others give nothing. -/
example : xbox [□p, q, □(p ⟶ q), p ⟶ q, □p, ⊥] ++ [□q]
    = [p, □p, p ⟶ q, □(p ⟶ q), p, □p, □q] := rfl

/-- `Id_all_form` at `□(p → q)`: GLR, then the case of an implication. -/
def idBoxImp : Fam ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) :=
  .glr (p ⟶ q) (by decide)                    -- p → q, □(p → q), □(p → q) ⇒ p → q
    (.impR p q (by decide)                   -- p, p → q, □(p → q), □(p → q) ⇒ q
      (.impL p q (by decide)
        (.idP 0 (by decide) (by decide))     -- p, □(p → q), □(p → q) ⇒ p, q
        (.idP 1 (by decide) (by decide))))   -- q, p, □(p → q), □(p → q) ⇒ q

example : idBoxImp.height = 4 := rfl

/-! ## The thesis's examples (I. Shillito, PhD thesis, ANU 2023, p. 171)

A sequent of the thesis is a multiset: the lists here have its formulas,
in the order the family gives them.  `r` is a third variable. -/

/-- The variable `r`. -/
abbrev r : Form := .var 2

/-- Example 12.4.1, second derivation: (→R) from `p, q ⇒ r, □r` to
`p ⇒ q → r, □r`.  The premise is not an axiom: the example is a derivation
with an open leaf, so here it is the rule as a function of a derivation of
its premise. -/
def ex1241b (d : Fam ([q, p] ⇒ [r, □r])) : Fam ([p] ⇒ [q ⟶ r, □r]) :=
  .impR q r (by decide) d

/-- Example 12.4.1, third derivation, "a proof": (GLR) from
`□p, p, □p ⇒ p`, an instance of (IdP), to `□p ⇒ □p, q`.  The premise of
the family's GLR is `p, □p, □p ⇒ p`: the same multiset. -/
def ex1241c : Fam ([□p] ⇒ [□p, q]) :=
  .glr p (by decide) (.idP 0 (by decide) (by decide))

example : xbox [□p] ++ [□p] = [p, □p, □p] := rfl

/-- Example 12.4.2, at `ϕ := p`: (→L) on `□p → p` and then (GLR) on `□p`
in its first premise.  The top sequent is the bottom one with more copies
of its formulas, which is why "the naive backward proof-search … does not
terminate".  As a function of derivations of the two open leaves. -/
def ex1242
    (d₁ : Fam ([□p ⟶ p, □(□p ⟶ p), p, □p, p, □p, □p] ⇒ [p]))
    (d₂ : Fam ([p, □(□p ⟶ p), p, □p, □p] ⇒ [p])) :
    Fam ([□p ⟶ p, □(□p ⟶ p), p, □p, □p] ⇒ [p]) :=
  .impL □p p (by decide)
    (.glr p (by decide) d₁)       -- □(□p → p), p, □p, □p ⇒ □p, p
    d₂

/-- The premise of that GLR, computed: the thesis prints
`□ϕ → ϕ, □(□ϕ → ϕ), ϕ, ϕ, □ϕ, □ϕ, □ϕ ⇒ ϕ`, the same multiset. -/
example : xbox [□(□p ⟶ p), p, □p, □p] ++ [□p] = [□p ⟶ p, □(□p ⟶ p), p, □p, p, □p, □p] := rfl

example : ([□p ⟶ p, □(□p ⟶ p), p, □p, p, □p, □p] : List Form).isPerm
    [□p ⟶ p, □(□p ⟶ p), p, p, □p, □p, □p] = true := by decide

end GLS.Source

#axioms_within_file [propext, Quot.sound]
