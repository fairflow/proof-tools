# MALL: the statements

Every statement the campaign will cite, displayed as Lean, with its
status. A statement is entered here, OPEN, and screened before its proof
is begun; the statement of a goal is also read back. Nothing is removed.

Status is exactly one of **PROVED** (checked by the kernel, no `sorry`,
within the bound of its file), **REFUTED** (its negation is proved),
**OPEN** (everything else).

The axiom policy of the development: every theory file within
`[propext, Quot.sound]`.

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file | the source's item | read back |
|---|---|---|---|
| formulas, linear negation | `MALL.Form`, `Form.neg`, `MALL/Form.lean` | p. 21 | (stage 2) |
| judgments | `List Form`, read as a multiset | Definition 1.15, p. 22; p. 24 | |
| the family of rules | `MALL.Fam`, `MALL.CF`, `MALL/System.lean`; the figure as it stands, `MALL.Lit`, `MALL/Source.lean` | Definition 1.15 | the second transcription (`rule-table.md`) |
| what holds | `MALL.Fam`; `Derivable Γ := Nonempty (Fam Γ)` | | |

## The statements

### S1. The soundness of the moves

    S.SoundT Fam

`step_sound`, `MALL/Proof.lean`. Source: none; it joins `step` to what
holds. A definition (the family is into `Type`): one constructor of
`Fam` for each move. Status: **PROVED**, within `[propext, Quot.sound]`.
This is not the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    ∀ Γ : List Form, Fam Γ → Nonempty (Der S Γ)

`FamToDer`, proved by `famToDer`, `MALL/Proof.lean`. Source: none. By
induction on the derivation, for every permutation of its sequent
(`famToDer_perm`): the premises `step` computes are the rule's up to a
permutation. Status: **PROVED**, within `[propext, Quot.sound]`.

### S3. The figure as it stands and the family derive the same sequents

    ∀ Γ : List Form, Nonempty (Lit Γ) ↔ Derivable Γ

`lit_iff_fam`, `MALL/Source.lean`, from the two functions
`Lit.toFam : Lit Γ → Fam Γ` and `Fam.toLit : Fam Γ → Lit Γ`. Source:
none; it is what the divergence D1 of the rule table rests on. Status:
**PROVED**, within `[propext, Quot.sound]`.

(The goals of the plan are entered at the start of stage 2.)
