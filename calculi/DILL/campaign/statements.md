# DILL: the statements

Every statement the campaign cites, displayed as Lean, with its status.
Each was fixed as a named Lean type in `DILL/Statements.lean` (commit
`477cd38`, 15:20 GMT) before any proof of it was begun; this document
was first written at 15:27, while the proofs were being made by agents,
and its statuses are those of the commit it is in.

Status is exactly one of **PROVED** (checked by the kernel, no `sorry`,
within the bound of its file), **REFUTED** (its negation is proved),
**OPEN** (everything else).

The axiom policy: every theory file within `[propext, Quot.sound]`.

Sources: CCP is Chang, Chaudhuri, Pfenning, CMU-CS-03-131R (2003);
Pfenning is the lecture notes *Linear Logic* (draft of January 2002,
read, not the source of record); KOT is Kanovich, Okada, Terui (2006).
`Fam true` is the calculus with the two cuts, `CF = Fam false` the
figure; `Derivable j := Nonempty (Fam true j)`; `~` is `List.Perm`.

## Definitions the statements are about

No tool checks that these say what the source means.

| definition | Lean name, file | the source's item | read back |
|---|---|---|---|
| formulas | `Form`, `DILL/Form.lean` | CCP p. 1, p. 3 | see "The reading back" |
| judgments | `Seq`, `Γ ⨾ Δ ⟹ C`, `DILL/Form.lean` | CCP pp. 10-11 | the same |
| the family of rules | `Fam`, `DILL/System.lean` | CCP Figure 2, p. 12; Principle 7, p. 11 | the second transcription (`rule-table.md`), and the reading back |
| what holds | `Fam true`; `Derivable` | | |
| the models | `PhaseSpace`, `PhaseModel`, `DILL/Semantics.lean` | KOT Definitions 2.2, 2.6 | the reading back |
| truth in a model | `PhaseModel.interp`, `Seq.form`, `PhaseModel.Sat`, `Valid`, `DILL/Semantics.lean` | KOT Definitions 2.4, 2.6; the formula of a sequent is ours | the reading back |
| the one-zone calculus | `ILL`, `DILL/ILL.lean` | KOT Figure 1, p. 4, without `⊥` | its own table in `rule-table.md` |
| a saturated set, and `refutedBy` (stage 3) | see S-R below | ours | not read back |

## The statements

### S1. The soundness of the moves

    S.SoundT (Fam true)

`step_sound`, `DILL/Proof.lean`. Source: none. A definition (the family
is into `Type`). **PROVED** (the file builds within its bound).

### S2. Every derivation of the family is a derivation of the proof system

    ∀ j, Fam true j → Nonempty (Der S j)

`famToDer : FamToDer`, `DILL/Proof.lean`. Source: none. By induction,
generalised over a permutation of the linear zone. **PROVED**.

### S3. Soundness for the phase semantics

    ∀ j, Derivable j → Valid j

`Soundness`. Source: KOT Theorem 2.9, "only if" (for one-zone ILL;
attributed there to Abrusci 1990 and Troelstra 1992): holds of the
logic, proved elsewhere. Screened: in scratch, with the model
`(ℕ, +, 0, identity)`, three sequents that are not derivable are not
satisfied, and copy is valid (the plan). STATUS-S3

### S4. Completeness, without cut

    ∀ j, Valid j → Nonempty (CF j)

`Completeness`. Source: KOT Theorem 2.9 "if", with Remark 2.11 for the
form without cut. STATUS-S4

    ∀ j, Derivable j → Nonempty (CF j)

`CutEliminationProp`: cut elimination a second time, by S3 then S4.
STATUS-S4b

### S5. The structural properties of the unrestricted zone

    (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)
    (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (A :: A :: Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

`WeakeningU`, `ContractionU`. Source: CCP Theorem 2 (p. 11). Both are
instances of `Fam.mono` (`DILL/System.lean`): a derivation at `Γ` is one
at every `Γ'` that has the members of `Γ`. STATUS-S5

### S6. Exchange

    ∀ c Γ Δ Δ' C (e : Δ ~ Δ') (d : Fam c (Γ ⨾ Δ ⟹ C)), (d.exch e).height = d.height
    ∀ c Γ Γ' Δ C, Γ ~ Γ' → ∀ d : Fam c (Γ ⨾ Δ ⟹ C), ∃ d' : Fam c (Γ' ⨾ Δ ⟹ C), d'.height = d.height

`ExchangeKeepsHeight`, `ExchangeUKeepsHeight`. Source: CCP p. 2;
Pfenning p. 46. Trivial by the encoding: a rule asks for its formula up
to a permutation (linear zone) or by membership (unrestricted zone).
STATUS-S6

### S7. Weakening and contraction of the linear zone

    ∀ Γ Δ A C, Derivable (Γ ⨾ Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)
    ∀ Γ Δ A C, Derivable (Γ ⨾ A :: A :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)

`WeakeningL`, `ContractionL`. Source: CCP p. 2, "disallowing weakening
and contraction". Expected REFUTED. STATUS-S7

### S8. The two cuts are admissible without cut; cut elimination

    (Γ Δ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ Δ ⟹ A) → CF (Γ ⨾ A :: Δ' ⟹ C) → CF (Γ ⨾ Δ ++ Δ' ⟹ C)
    (Γ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ [] ⟹ A) → CF (A :: Γ ⨾ Δ' ⟹ C) → CF (Γ ⨾ Δ' ⟹ C)
    (j : Seq) → Fam true j → CF j

`CutAdmissible`, `CutUAdmissible`, `CutElimination`. Source: CCP
Principle 7.2 and 7.1, Theorem 3 (p. 12); Pfenning 3.8, 3.9. Standing
entry 1. Functions on derivations: what the types do not say is which
function; it is the source's procedure (the cut pushed upwards, by
recursion on the cut formula and the derivations), not the composite of
S3 and S4. STATUS-S8

### S9. The invertible rules, and the deduction theorems

    CF (Γ ⨾ A ⊗ B :: Δ ⟹ C) → CF (Γ ⨾ A :: B :: Δ ⟹ C)                      TensorLInv
    CF (Γ ⨾ 𝟏 :: Δ ⟹ C) → CF (Γ ⨾ Δ ⟹ C)                                    OneLInv
    CF (Γ ⨾ Δ ⟹ A ⊸ B) → CF (Γ ⨾ A :: Δ ⟹ B)                                LolliRInv
    CF (Γ ⨾ Δ ⟹ A & B) → CF (Γ ⨾ Δ ⟹ A) × CF (Γ ⨾ Δ ⟹ B)                   WithRInv
    CF (Γ ⨾ (A ⊕ B) :: Δ ⟹ C) → CF (Γ ⨾ A :: Δ ⟹ C) × CF (Γ ⨾ B :: Δ ⟹ C)   PlusLInv
    CF (Γ ⨾ (!A) :: Δ ⟹ C) → CF (A :: Γ ⨾ Δ ⟹ C)                            BangLInv
    CF (Γ ⨾ [] ⟹ !A) → CF (Γ ⨾ [] ⟹ A)                                      BangRInv
    ∀ Γ Δ A B, Derivable (Γ ⨾ A :: Δ ⟹ B) ↔ Derivable (Γ ⨾ Δ ⟹ A ⊸ B)        DeductionLinear
    ∀ Γ Δ A C, Derivable (A :: Γ ⨾ Δ ⟹ C) ↔ Derivable (Γ ⨾ (!A) :: Δ ⟹ C)    DeductionUnrestricted

(each of the first seven for all `Γ Δ A B C`). Source: CCP Lemma 6
(p. 17). The last two are standing entry 3, in the form the calculus
has it. STATUS-S9

### S10. The rules that are not invertible

    ∀ Γ Δ Δ' A B, Derivable (Γ ⨾ Δ ++ Δ' ⟹ A ⊗ B) → Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ Δ' ⟹ B)          TensorRInv
    ∀ Γ Δ Δ' A B C, Derivable (Γ ⨾ A ⊸ B :: (Δ ++ Δ') ⟹ C) → Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ B :: Δ' ⟹ C)  LolliLInv
    ∀ Γ Δ A B C, Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)                               WithL₁Inv
    ∀ Γ Δ A B C, Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ B :: Δ ⟹ C)                               WithL₂Inv
    ∀ Γ Δ A B, Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ A)                                           PlusR₁Inv
    ∀ Γ Δ A B, Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ B)                                           PlusR₂Inv

Source: CCP Lemma 6: "non-invertible", by "a counter-example which has
the identical principal connective on both sides of the arrow". Expected
REFUTED. STATUS-S10

### S11. init at atoms only

    (j : Seq) → CF j → { d : CF j // d.Atomic }

`IdentityExpansion`; `d.Atomic` says that every instance of init in `d`
is at an atom. Source: Pfenning Theorem 4.2 (p. 71, by the survey's
reading); CCP's init is general. STATUS-S11

### S12. The subformula property

    ∀ (j : Seq) (d : CF j), d.All fun j' => ∀ C ∈ j'.forms, ∃ D ∈ j.forms, C.IsSub D

`SubformulaProperty`; `j.forms` is the conclusion and both zones.
Source: CCP p. 10; Pfenning p. 56 (remarks, not numbered). STATUS-S12

### S13. Consistency, and the disjunction property

    ¬ Derivable ([] ⨾ [] ⟹ 𝟎)
    ∀ A B, Derivable ([] ⨾ [] ⟹ A ⊕ B) → Derivable ([] ⨾ [] ⟹ A) ∨ Derivable ([] ⨾ [] ⟹ B)

`Consistency`, `DisjunctionProperty`. Source: Pfenning 3.11 and 3.12
(pp. 59-60), stated there for natural deduction. Standing entry 6.
STATUS-S13

### S14. The translation to and from one-zone ILL

    (c : Bool) → (Γ Δ : List Form) → (C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → ILL c (Γ.map Form.bang ++ Δ) C
    (Γ Δ : List Form) → (C : Form) → ILL true (Γ.map Form.bang ++ Δ) C → Fam true (Γ ⨾ Δ ⟹ C)
    ∀ Γ Δ C, Derivable (Γ ⨾ Δ ⟹ C) ↔ ILLDerivable (Γ.map Form.bang ++ Δ) C

`toILL : ToILL`, `ofILL : OfILL`, `illEquivalence : ILLEquivalence`,
`DILL/Translate.lean`. Source: CCP Theorem 7, items 3 and 1 (p. 20).
The first keeps a derivation without cut without cut; the second is
with cut on both sides (the inversion of !L it uses is by a cut).
Screened by the agent on empty zones, the constants, a formula twice in
`Γ`, and a `!`-formula left in `Δ`. **PROVED**, within
`[propext, Quot.sound]` (built by the operator, 15:24).

### S15. Decidability without `!`

    (Δ : List Form) → (C : Form) → (∀ A ∈ C :: Δ, A.bangFree = true) → Decidable (Derivable ([] ⨾ Δ ⟹ C))

`BangFreeDecidable`. Source: Lincoln, Mitchell, Scedrov, Shankar 1992
(the survey: intuitionistic MALL is PSPACE-complete "only as an
unnumbered sentence after 2.12"). The form without cut,

    (Δ : List Form) → (C : Form) → (∀ A ∈ C :: Δ, A.bangFree = true) → Decidable (Nonempty (CF ([] ⨾ Δ ⟹ C)))

is `decideCF`, `DILL/Decide.lean`: a search that returns a derivation,
proved complete, by structural recursion, run by the kernel.
**PROVED** (built by the operator, 15:26). STATUS-S15

## The reading back

READBACK

## Refuted

| statement | the proof of the negation | where | what replaced it |
|---|---|---|---|
REFUTED-ROWS

## Not goals, and set aside

| result | not a goal: the plan's reason |
|---|---|
| soundness and completeness against natural deduction (CCP Theorems 4, 5) | about Figure 1, another system, left out at the first act |
| the finite model property | fails with `!` (Lafont 1997: an undecidable logic "cannot satisfy a finite model property"; the survey found no place that says it of ILL in so many words); for the fragment without `!`, the budget |
| undecidability with `!` (Lincoln et al. 1992, Corollary 3.8) | needs a theory of machines |
| normalisation, confluence | the sequent calculus has no terms |
| the existence property | propositional |
| the possibility judgment, `?`, the classical interpretation (CCP §2.3, §4) | outside the fragment |
| a phase model from a saturated set | beyond the plan's level for Run |

## Summary

SUMMARY
