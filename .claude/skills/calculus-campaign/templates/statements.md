# <CALCULUS>: the statements

*Template. Started in Adopt (S1 and S2 below), filled in Prove. Every
statement the campaign will cite, displayed as Lean, with its status. A
statement is entered here, OPEN, and screened before its proof is begun;
the statement of a goal is also read back (`reference/adopt.md` §5 and
§7; S1, S2 and the certifiers' statements have no item of the source, and
are not). Nothing is removed: a refuted statement stays, with its
countermodel. Lemmas on the way are not entered. Every goal of the plan
has an entry.*

Status is exactly one of:

* **PROVED**: checked by the kernel, no `sorry`, within the bound of its
  file;
* **REFUTED**: its negation is proved, or a countermodel is checked by the
  kernel; named here;
* **OPEN**: everything else. An OPEN statement is in Lean as a named
  proposition (`def Name : Prop := …`), not as a theorem with `sorry`.
  What tests show about it may be noted; it stays OPEN.

A result that is not a goal is listed at the end here, without a
status: *not a goal* (decided in the plan), or *set aside* (by the
reviewer, in their words). A goal ends PROVED or OPEN: where a
statement of it is REFUTED, the statement that replaces it is entered
after it.

The axiom policy of the development: <from the plan>.

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file | the source's item | read back (`reference/adopt.md` §7) |
|---|---|---|---|
| formulas | | | |
| judgments | | | |
| the family of rules | | | (the second transcription, in the rule table) |
| what holds: the family, or `Valid` | | | |
| the models, and truth in a model | | | |
| a finite model as data, and `refutes` | | | |
| the term calculus: terms, typing, reduction (where a goal needs it) | | | (its own rule table) |

## The statements

When this file is started, at step 4 of Adopt, the proof system may not
yet be written: the rule table is not yet checked. S1 and S2 are then entered
as displayed below, with "not yet in Lean" for the name and the file,
OPEN. The names are filled at step 5.

For each: the source's item (by label where there is one), the statement
as a displayed formula, the Lean name and file, the status, the axioms,
what it was screened with, and what the reading back gave.

### S1. The soundness of the moves

    S.SoundT Fam          (where what holds is validity:  S.Sound Valid)

`step_sound`, `<file>`. Source: none; it joins `step` to what holds. Its
statement was fixed with that choice, in the plan. Status: OPEN. With the
family into `Type` it is a definition, and PROVED when the file that
holds it builds within its bound. This is not the source's soundness
theorem.

### S2. Every derivation of the family is a derivation of the proof system

    Fam j → Nonempty (Der S j)

`FamToDer`, `<file>`. Source: none. Status: OPEN.

### S3. <the source's soundness theorem, its label>

    <statement>

Source: <the paper and the number of the theorem; or "a proof is stated,
not given, at …">. Screened: <which of the four directions were run, with
what, on what, and the result>. Read back: <agrees / differs, and how
that was settled / not run>. Status: OPEN.

### S4 and on

One entry in the form of S3 for each further goal, in the plan's order.

Where a theorem takes a named hypothesis, enter both: the theorem (PROVED
as stated, the hypothesis in its statement) and the hypothesis (OPEN).
Where a statement needs `Classical.choice` in its statement and has a
constructive form, enter both. Before that, where a statement about
every structure of some kind implies a classical principle, look for the
class of structures the source means (`reference/adopt.md` §5): the
statement restricted to that class is direct, and is entered alone, with
a line on how it stands to the source's wording.

## Refuted

| statement | the countermodel, or the proof of the negation | where it is checked | what replaced the statement |
|---|---|---|---|

## Not goals, and set aside

| result | not a goal (the plan's reason), or set aside (the reviewer's words, and the entry of `decisions.md`) |
|---|---|

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list | | | |
| of the other goals | | | |
| of our own (S1, S2, and what the closing page cites) | | | |
