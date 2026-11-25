/-
The source's own worked derivation, as terms of the family.

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

end GLS.Source

#axioms_within_file [propext, Quot.sound]
