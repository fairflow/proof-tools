# DILL: campaign folder

The status board. True at every commit; no other report is written until
the closing page.

Dual intuitionistic linear logic as a sequent calculus with two zones,
`Γ ; Δ ⟹ C`: `Γ` unrestricted, `Δ` linear, one conclusion; ⊗, 1, ⊸, &, ⊤,
⊕, 0 and `!`. The target, the paper, the place of the files and the rules
of the project: [decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2, one session started by another session from a
brief, with agents it starts (the cost log names each). The method: the
skill `calculus-campaign` as it stood at commit `94df876` (2026-11-26).

Waiting on the reviewer: nothing.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done (14:47 to 14:59 GMT, 2026-11-26) | the plan's choices screened and recorded: 4 entries; what "valid" means screened on four sequents in a model | [plan.md](plan.md), [decisions.md](decisions.md), [survey-report.md](survey-report.md) |
| 1. Adopt | in progress: the family, the proof system and the tactic are built; the tests and the exercises file are being written by an agent | `#rules` beside the figure: 20 rules, one misprint of the source (W1); `#slime`: none; the second transcription: run, no difference; S2: PROVED | [rule-table.md](rule-table.md), `DILL/System.lean`, `DILL/Proof.lean` |
| 2. Prove | in progress: cut elimination as a function and the inversions are with an agent | statements read back: all, no fault, eight instances found that refute the eight statements expected false; goals PROVED so far: soundness, completeness without cut, cut elimination as a proposition, Theorem 2, exchange, identity expansion, the subformula property, consistency, the disjunction property, the translation, decidability without `!`; REFUTED: 8 | [statements.md](statements.md) (its statuses are being filled) |
| 3. Run | in progress: two agents (the search; saturated sets) | | [brief-3-1.md](brief-3-1.md) |
| 4. Explore | not started; its brief is written | | [brief-4-1.md](brief-4-1.md) |

## Files here

* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* [skeleton.md](skeleton.md): the sources' numbered results.
* [survey-report.md](survey-report.md): the survey agent's report on the
  literature, each claim marked as read or as from memory.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the second transcription; the divergence log; a second table
  for the one-zone calculus.
* [statements.md](statements.md): every statement, PROVED, REFUTED or OPEN.
* [cost-log.md](cost-log.md): one row for each stage, and the agents.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear.
* `brief-2-1.md`, `brief-3-1.md`, `brief-4-1.md`: the briefs to the
  agents of stages 2, 3 and 4.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake build DILL.Goals DILL.Translate)

The root module `DILL.lean` does not yet import every file: agents are
writing some.

## Files of the development

* `DILL/Form.lean`: formulas, sequents (theory).
* `DILL/Perm.lean`: permutations without `Classical.choice` (theory;
  MALL's file).
* `DILL/System.lean`: the family `Fam c`, exchange, the unrestricted
  zone's monotonicity, heights (theory).
* `DILL/Semantics.lean`: phase spaces, models, `Valid` (theory).
* `DILL/ILL.lean`: one-zone intuitionistic linear logic (theory).
* `DILL/Statements.lean`: the goals as named statements (theory).
* `DILL/Proof.lean`: the moves, `step`, S1, S2 (theory).
* `DILL/Tactic.lean`: printers, candidates, the tactic `dillmove` (code).
* `DILL/Soundness.lean`, `DILL/Completeness.lean`: the phase semantics'
  two theorems (theory).
* `DILL/Results.lean`: the structural results, identity expansion,
  subformulas (theory).
* `DILL/Decide.lean`: the decision without `!` (theory).
* `DILL/Translate.lean`: to and from one-zone ILL (theory).
* `DILL/Goals.lean`: the goals joined from the others, and the
  refutations (theory).

Every theory file ends with `#axioms_within_file [propext, Quot.sound]`.
