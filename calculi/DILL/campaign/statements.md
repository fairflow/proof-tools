# DILL: the statements

Every statement the campaign cites, displayed as Lean, with its status.
Each was fixed as a named Lean type in `DILL/Statements.lean` (commit
`584b842` on `main`, 15:20 GMT) before any proof of it was begun; this document
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
satisfied, and copy is valid (the plan). Read back: agrees
("soundness of the calculus with both cuts for the phase semantics").
**PROVED**: `soundness`, `DILL/Soundness.lean` (agent B; built by the
operator 15:29). By induction on the derivation, after a lemma
(`Sem.sat_iff_holds`) that takes the formula of the sequent apart into a
product of phases; no excluded middle.

### S4. Completeness, without cut

    ∀ j, Valid j → Nonempty (CF j)

`Completeness`. Source: KOT Theorem 2.9 "if", with Remark 2.11 for the
form without cut. Read back: agrees ("completeness, with a cut-free
derivation as conclusion"). **PROVED**: `completeness`,
`DILL/Completeness.lean` (agent B). The canonical model is built on the
two-zone calculus itself: phases are pairs of a list `Γ` and a list `Δ`,
up to "the same members" and a permutation (a `Quotient`), so that
`(Γ, [])` is a strict idempotent; the closed sets are the intersections
of the sets `{(Γ, Δ) | Γ ++ Γ' ; Δ ++ Δ' ⟹ C has a derivation without
cut}` (KOT Theorem 2.8); the main lemma is KOT's Lemma 2.10
(`Sem.okada`). No source read builds the model from a two-zone
calculus: the construction is the operator's, after KOT's for one zone.

    ∀ j, Derivable j → Nonempty (CF j)

`CutEliminationProp`: cut elimination a second time, by S3 then S4.
**PROVED**: `cutEliminationProp`, `DILL/Completeness.lean`. With it,
`Sem.valid_iff_derivable : Valid j ↔ Derivable j`.

### S5. The structural properties of the unrestricted zone

    (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)
    (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (A :: A :: Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

`WeakeningU`, `ContractionU`. Source: CCP Theorem 2 (p. 11). Both are
instances of `Fam.mono` (`DILL/System.lean`): a derivation at `Γ` is one
at every `Γ'` that has the members of `Γ`. Read back: agrees, with the remark
that both are instances of `Fam.mono`. **PROVED**: `weakeningU`,
`contractionU`, `DILL/Results.lean` (agent C).

### S6. Exchange

    ∀ c Γ Δ Δ' C (e : Δ ~ Δ') (d : Fam c (Γ ⨾ Δ ⟹ C)), (d.exch e).height = d.height
    ∀ c Γ Γ' Δ C, Γ ~ Γ' → ∀ d : Fam c (Γ ⨾ Δ ⟹ C), ∃ d' : Fam c (Γ' ⨾ Δ ⟹ C), d'.height = d.height

`ExchangeKeepsHeight`, `ExchangeUKeepsHeight`. Source: CCP p. 2;
Pfenning p. 46. Trivial by the encoding: a rule asks for its formula up
to a permutation (linear zone) or by membership (unrestricted zone).
Read back: the first "is about the function `Fam.exch`, whose
definition is not in the extract: it cannot be read back, only
believed"; the second assumes more than it needs (a permutation, where
"every member of `Γ` is in `Γ'`" suffices: that is `Fam.height_mono`).
**PROVED**: `exchangeKeepsHeight`, `exchangeUKeepsHeight`,
`DILL/Results.lean`.

### S7. Weakening and contraction of the linear zone

    ∀ Γ Δ A C, Derivable (Γ ⨾ Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)
    ∀ Γ Δ A C, Derivable (Γ ⨾ A :: A :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)

`WeakeningL`, `ContractionL`. Source: CCP p. 2, "disallowing weakening
and contraction". Expected REFUTED. Read back: both believed false,
with the instances below, unprompted. **REFUTED**: `not_weakeningL`,
`not_contractionL`, `DILL/Goals.lean`: `· ; · ⟹ 1` is derivable and
`· ; a ⟹ 1` is not; `· ; a, a ⟹ a ⊗ a` is derivable and `· ; a ⟹ a ⊗ a`
is not. Nothing replaces them.

### S8. The two cuts are admissible without cut; cut elimination

    (Γ Δ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ Δ ⟹ A) → CF (Γ ⨾ A :: Δ' ⟹ C) → CF (Γ ⨾ Δ ++ Δ' ⟹ C)
    (Γ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ [] ⟹ A) → CF (A :: Γ ⨾ Δ' ⟹ C) → CF (Γ ⨾ Δ' ⟹ C)
    (j : Seq) → Fam true j → CF j

`CutAdmissible`, `CutUAdmissible`, `CutElimination`. Source: CCP
Principle 7.2 and 7.1, Theorem 3 (p. 12); Pfenning 3.8, 3.9. Standing
entry 1. Functions on derivations: what the types do not say is which
function; it is the source's procedure (the cut pushed upwards, by
recursion on the cut formula and the derivations), not the composite of
S3 and S4. Read back: agrees; the reader
remarks that a type of functions says no more than its `Nonempty` form
unless the function is shown to compute (below). **PROVED**:
`cutAdmissible`, `cutUAdmissible`, `cutElimination`, `DILL/Cut.lean`
(agent A; built by the operator 15:33). By structural recursion on a
bound of the cut formula's size, the linear cut at a formula before the
unrestricted one; the statement proved inside the recursion has three
unrestricted zones (`Γ₁` and `Γ₂` included in `Γ'`), so that no
derivation is weakened on the way. They compute: the kernel evaluates
`(cutElimination _ d).height` on three derivations with a cut each
(2, 1, 4; `decide +kernel`, run by the operator after the repair of
`Fam.exch`, 15:33).

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
has it. Read back: agrees; the reader
remarks that `BangRInv` holds for every linear zone, not only the empty
one (true: cut against `Γ ; !A ⟹ A`); the statement is the inversion of
the rule as the figure has it, whose conclusion has an empty zone.
**PROVED**: `tensorLInv`, `oneLInv`, `lolliRInv`, `withRInv`,
`plusLInv`, `bangLInv`, `bangRInv`, `deductionLinear`,
`deductionUnrestricted`, `DILL/Invert.lean` (agent A), each by one
admissible cut, as the source proves them.

### S10. The rules that are not invertible

    ∀ Γ Δ Δ' A B, Derivable (Γ ⨾ Δ ++ Δ' ⟹ A ⊗ B) → Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ Δ' ⟹ B)          TensorRInv
    ∀ Γ Δ Δ' A B C, Derivable (Γ ⨾ A ⊸ B :: (Δ ++ Δ') ⟹ C) → Derivable (Γ ⨾ Δ ⟹ A) ∧ Derivable (Γ ⨾ B :: Δ' ⟹ C)  LolliLInv
    ∀ Γ Δ A B C, Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ A :: Δ ⟹ C)                               WithL₁Inv
    ∀ Γ Δ A B C, Derivable (Γ ⨾ A & B :: Δ ⟹ C) → Derivable (Γ ⨾ B :: Δ ⟹ C)                               WithL₂Inv
    ∀ Γ Δ A B, Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ A)                                           PlusR₁Inv
    ∀ Γ Δ A B, Derivable (Γ ⨾ Δ ⟹ A ⊕ B) → Derivable (Γ ⨾ Δ ⟹ B)                                           PlusR₂Inv

Source: CCP Lemma 6: "non-invertible", by "a counter-example which has
the identical principal connective on both sides of the arrow". Expected
REFUTED. Read back: all six believed false, with instances. **REFUTED**,
`DILL/Goals.lean`, each by a sequent with the same connective on both
sides, as the source says, decided by the kernel through
`DILL/Decide.lean`: `not_tensorRInv`, `not_lolliLInv`, `not_withL₁Inv`,
`not_withL₂Inv`, `not_plusR₁Inv`, `not_plusR₂Inv` (the table "Refuted"
has the sequents). Nothing replaces them.

### S11. init at atoms only

    (j : Seq) → CF j → { d : CF j // d.Atomic }

`IdentityExpansion`; `d.Atomic` says that every instance of init in `d`
is at an atom. Source: Pfenning Theorem 4.2 (p. 71, by the survey's
reading); CCP's init is general. Read back: agrees; "does
not relate the output derivation to the input" (so: it says that a
derivation with init at atoms exists and is computed, no more).
**PROVED**: `identityExpansion`, `DILL/Results.lean` (agent C).

### S12. The subformula property

    ∀ (j : Seq) (d : CF j), d.All fun j' => ∀ C ∈ j'.forms, ∃ D ∈ j.forms, C.IsSub D

`SubformulaProperty`; `j.forms` is the conclusion and both zones.
Source: CCP p. 10; Pfenning p. 56 (remarks, not numbered). Read back:
agrees ("the plain subformula property: zones are pooled with the goal
and polarity is not tracked"). **PROVED**: `subformulaProperty`,
`DILL/Results.lean`.

### S13. Consistency, and the disjunction property

    ¬ Derivable ([] ⨾ [] ⟹ 𝟎)
    ∀ A B, Derivable ([] ⨾ [] ⟹ A ⊕ B) → Derivable ([] ⨾ [] ⟹ A) ∨ Derivable ([] ⨾ [] ⟹ B)

`Consistency`, `DisjunctionProperty`. Source: Pfenning 3.11 and 3.12
(pp. 59-60), stated there for natural deduction. Standing entry 6.
Read back: agrees; the reader notes that the disjunction property
needs both zones empty (`· ; p ⊕ q ⟹ p ⊕ q`). **PROVED**:
`consistency`, `disjunctionProperty`, `DILL/Goals.lean`, from the forms
without cut of `DILL/Results.lean` and `cutEliminationProp`.

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
**PROVED** (built by the operator, 15:26).
And `bangFreeDecidable : BangFreeDecidable`, `DILL/Goals.lean`, joins it
to cut elimination. **PROVED**. Read back: "inhabited with no proof
search at all" by `Classical.propDecidable`; so what the statement says
is in its bound on axioms (no `Classical.choice`) and in that the kernel
runs it: the eight refutations of `DILL/Goals.lean` are `by decide`
through it. Both zones' restrictions are needed (a formula of `Γ` is
under an implicit `!`).

### S16. A saturated set of sequents refutes its members (stage 3; ours)

    refutedBy : List Seq → Seq → Bool
    ∀ (D : List Seq) (j : Seq), refutedBy D j = true → ¬ Nonempty (CF j)
    noCFBySet : Certify.Certifier Seq (List Seq) (fun j => Nonempty (CF j) → False)

`refutedBy D j`: `j` is a member of `D` (up to a permutation of the
linear zone and the members of the unrestricted one), no member of `D`
is the conclusion of a rule with no premise, and every instance of a
rule of `CF` that concludes a member has a premise in `D`
(`brief-3-1.md`, H, has the conditions rule by rule). Source: none; the
form is MALL's second certificate, with the soundness proved from the
rules alone. Fixed 15:28, before its proof. Screened: by the negative
tests of `DILL/SatTest.lean`. Not read back (a certifier's statement).
**PROVED**: `not_cf_of_refutedBy`, `DILL/Saturated.lean`; `noCFBySet` and,
through `cutElimination`,

    noDerivableBySet : Certify.Certifier Seq (List Seq) (fun j => Derivable j → False)

`DILL/SatRun.lean` (agent H; built by the operator 16:03, after the
restart). Proved with it: a saturated set has no member with a
non-empty unrestricted zone (`Sat.unr_nil`) and none with `!A` in its
linear zone (`Sat.no_bang`), so the certificate exists only for the
sequents whose failed search meets neither. Sixteen negative tests in
the kernel (`DILL/SatTest.lean`).

### S18. The engine, and one side always answering without `!` (stage 3; ours)

    dillEngine : Certify.Engine Seq (Script S) (List Seq) Derivable
    noDerivableDec : Certify.Certifier Seq Unit (fun j => Derivable j → False)
    ∀ Δ C, (∀ A ∈ C :: Δ, A.bangFree = true) →
      (∃ c, treeCert.check ([] ⨾ Δ ⟹ C) c = true) ∨ noDerivableDec.check ([] ⨾ Δ ⟹ C) () = true

`DILL/Engine.lean`. The engine joins the certifier of scripts, the
certifier of saturated sets (S16) and a producer that answers `flag`
where the search finds nothing at its budget and no set is found: level
2. `noDerivableDec` has no certificate: its check is the decision of S15,
and it refuses every sequent outside that fragment. The last statement
(`decidedBangFree`) is level 3 for the fragment with an empty
unrestricted zone and no `!`, and for nothing more: with `!` no such
statement can hold of sound checks with computable producers. Source:
none. Entered 16:05, before the file was built. Not read back.
**PROVED**: `dillEngine`, `noDerivableDec`, `decidedBangFree`,
`DILL/Engine.lean` (built by the operator 16:23; the lints R2 and R3
of `lean-certify` pass on `noDerivableDec`, and the file is within its
bound on axioms).

### S17. Validity does not depend on the order of the hypotheses (ours)

    Γ ~ Γ' → Δ ~ Δ' → (Valid (Γ ⨾ Δ ⟹ C) ↔ Valid (Γ' ⨾ Δ' ⟹ C))

`valid_perm`, `DILL/Goals.lean`. Entered because the reading back found
that `Seq.form` is written through an order of the hypotheses.
**PROVED**, from `Sem.valid_iff_derivable`.

## The reading back

Run 2026-11-26 15:21 to 15:28 GMT by a cold reader (an agent given one
file: an extract of 491 lines with the definitions and the 35 named
statements, comments removed and the statements' names replaced by
`T01` to `T35`; told to open nothing else). Its reading of each
definition and statement agrees with the source's item: the formulas,
the sequent, the twenty rules (with "`Ξ ~ [A]` is just `Ξ = [A]`"), the
phase spaces and the interpretation, the twenty rules of the one-zone
calculus. What it marked, and how each was settled:

* the eight statements S7 and S10 are false, each with an instance: the
  refutations, as expected;
* a statement that is a type of functions, and a `Decidable`, has a
  classical inhabitant: what such a statement says is in its bound on
  axioms and in that it computes. Said at S8 and S15;
* `Valid` quantifies over models whose carrier is in the lowest
  universe: enough for completeness; soundness says nothing of larger
  models. Left so (MALL did the same);
* the formula of a sequent depends on the order of its hypotheses and
  ends in `⊗ 1`: S17 was added;
* the semantics takes all idempotents of `1` for `!`, not a chosen
  submonoid (so does KOT; Okada and Terui's has the submonoid: the
  decisions, 15:19);
* `PhaseSpace` has `one_mul` and no `mul_one` (it follows);
  `CFDerivable` is defined and `Nonempty (CF j)` is spelt out in the
  statements (left so).

No definition and no statement was changed after the reading.

## Refuted

| statement | the proof of the negation | where | what replaced it |
|---|---|---|---|
| `WeakeningL` | `· ; · ⟹ 1` derivable (1R); `· ; a ⟹ 1` not | `not_weakeningL`, `DILL/Goals.lean` | nothing |
| `ContractionL` | `· ; a, a ⟹ a ⊗ a` derivable; `· ; a ⟹ a ⊗ a` not | `not_contractionL` | nothing |
| `TensorRInv` | `· ; a ⊗ b ⟹ a ⊗ b` derivable (init); under ⊗R at the division `a ⊗ b` and nothing, the premise `· ; · ⟹ b` not | `not_tensorRInv` | nothing |
| `LolliLInv` | `· ; a ⊸ b ⟹ a ⊸ b` derivable; the premise `· ; · ⟹ a` not (CCP p. 18) | `not_lolliLInv` | nothing |
| `WithL₁Inv` | `· ; a & b ⟹ a & b` derivable; `· ; a ⟹ a & b` not | `not_withL₁Inv` | nothing |
| `WithL₂Inv` | `· ; a & b ⟹ a & b` derivable; `· ; b ⟹ a & b` not | `not_withL₂Inv` | nothing |
| `PlusR₁Inv` | `· ; a ⊕ b ⟹ a ⊕ b` derivable; `· ; a ⊕ b ⟹ a` not | `not_plusR₁Inv` | nothing |
| `PlusR₂Inv` | `· ; a ⊕ b ⟹ a ⊕ b` derivable; `· ; a ⊕ b ⟹ b` not | `not_plusR₂Inv` | nothing |

Each "not" is decided by the kernel: the sequent has no `!` and an empty
unrestricted zone, `DILL/Decide.lean` decides derivability without cut,
and `cutEliminationProp` carries it to the calculus with cut.

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

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (cut elimination: S8, S4b; the deduction theorems: S9; the disjunction property: S13) | 3 | 0 | 0 |
| of the other goals (S3, S4, S5, S6, the inversions of S9, S11, S12, consistency, S14, S15; S7 and S10 expected refuted) | 10 | 2 (eight statements) | 0 |
| of our own (S1, S2, S16, S17, S18) | 5 (S1, S2, S16, S17, S18) | 0 | 0 |
