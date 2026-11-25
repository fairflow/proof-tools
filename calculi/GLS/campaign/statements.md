# GLS: the statements

Started in Adopt (S1 and S2), filled in Prove. Every statement the
campaign will cite, displayed as Lean, with its status. A statement is
entered here, OPEN, and screened before its proof is begun; the
statement of a goal is also read back (`reference/adopt.md` §5 and §7 of
the skill). Nothing is removed: a refuted statement stays, with its
countermodel. Lemmas on the way are not entered.

Status is exactly one of:

* **PROVED**: checked by the kernel, no `sorry`, within the bound of its
  file;
* **REFUTED**: its negation is proved, or a countermodel is checked by the
  kernel; named here;
* **OPEN**: everything else. An OPEN statement is in Lean as a named
  proposition or type, not as a theorem with `sorry`.

The axiom policy of the development: every theory file within
`[propext, Quot.sound]` (the plan).

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file | the source's item | read back |
|---|---|---|---|
| formulas | `GLS.Form`, `GLS/Form.lean` | `MPropF`, the Coq file l. 41 | |
| sequents | `GLS.Seq`, `GLS/Form.lean` | `rel (list (MPropF V))` | |
| the boxed part of an antecedent | `GLS.xbox`, `GLS.Form.xb`, `GLS/Form.lean` | `XBoxed_list (top_boxes Γ)`, l. 154, 161 | |
| the family of rules of GLS | `GLS.Fam`, `GLS/System.lean` | `GLS_rules`, l. 306 | the second transcription, in the rule table: no difference |
| the family of rules of PSGLS | `GLS.PSFam`, `GLS/System.lean` | `PSGLS_rules`, l. 314 | the same |
| the height of a derivation | `GLS.Fam.height`, `GLS/System.lean` | `derrec_height`, `general/dd_fc.v` l. 131 | |
| what holds: the family | `GLS.Fam` | | |

## The statements

### S1. The soundness of the moves

    S.SoundT Fam
      :=  ∀ m j ps, S.step m j = .ok ps → Each Fam ps → Fam j

`step_sound`, `GLS/Proof.lean`. Source: none; it joins `step` to what
holds. With the family into `Type` it is a definition. Status:
**PROVED** (the file builds within `[propext, Quot.sound]`). This is not
the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    Fam j → Nonempty (Der S j)

`FamToDer`, proved as `famToDer`, `GLS/Proof.lean`. Source: none. Status:
**PROVED**, within `[propext, Quot.sound]`: a node for each constructor.
So `step` refuses no instance of a rule of `Fam`.

## Refuted

None.

## Not goals, and set aside

Filled in Prove, from the plan.

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list | 0 | 0 | not yet entered |
| of the other goals | 0 | 0 | not yet entered |
| of our own (S1, S2) | 2 | 0 | 0 |
