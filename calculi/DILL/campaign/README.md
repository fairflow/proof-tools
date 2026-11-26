# DILL: campaign folder

The status board. The campaign is closed: the closing page is
[report.md](report.md).

Dual intuitionistic linear logic as a sequent calculus with two zones,
`Γ ; Δ ⟹ C`: `Γ` unrestricted, `Δ` linear, one conclusion; ⊗, 1, ⊸, &, ⊤,
⊕, 0 and `!`. The target, the paper, the place of the files and the rules
of the project: [decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2, one session started by another session from a
brief, with twelve agents it started (the cost log names each). The
method: the skill `calculus-campaign` as it stood at commit `94df876`
(2026-11-26); two later commits of the skill, on builds, were taken in
during the run.

Waiting on the reviewer: nothing.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done (14:47 to 14:59 GMT, 2026-11-26) | the plan's choices screened and recorded: 4 entries; what "valid" means screened on four sequents in a model | [plan.md](plan.md), [decisions.md](decisions.md), [survey-report.md](survey-report.md) |
| 1. Adopt | done (15:13 to 15:42) | `#rules` beside the figure: 20 rules, one misprint of the source (W1); `#slime`: none; worked derivations as terms: 13 of 13; the second transcription: run, no difference; S2: PROVED | [rule-table.md](rule-table.md), `DILL/System.lean`, `DILL/Proof.lean`, `Play/DILL.lean` |
| 2. Prove | done (15:20 to 15:33) | statements read back: all 35, no fault; goals PROVED: 13 of 13; OPEN: 0; REFUTED, as expected: 8 statements | [statements.md](statements.md) |
| 3. Run | done (15:29 to 16:27), at level 2 | negative tests: 10 for trees and scripts, 16 for saturated sets; the frontier: the kernel's check of a stated tree stops between a chain of 64 and of 96 formulas, and of a saturated set between 200 and 499 sequents; with `!` on the left of a sequent with no derivation the answer is `flag` | [measurements.md](measurements.md), [measurements-sat.md](measurements-sat.md), `DILL/Run.lean`, `DILL/SatRun.lean`, `DILL/Engine.lean` |
| 4. Explore | done (15:34 to 16:33) | the tutorial: every line elaborated and pinned (`DILL/TutorialTest.lean`); the tutorial page: 25 pins hold, by `tutorial_pins.py check` | `tutorial.md`, `Play/DILLTutorial.lean`, `Play/DILLExercises.lean`, [users-guide.md](users-guide.md), [report.md](report.md) |

## Files here

* [report.md](report.md): the closing page.
* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* [skeleton.md](skeleton.md): the sources' numbered results.
* [survey-report.md](survey-report.md): the survey agent's report on the
  literature, each claim marked as read or as from memory.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the second transcription; the divergence log; a second table
  for the one-zone calculus.
* [statements.md](statements.md): every statement, PROVED, REFUTED or
  OPEN, and the reading back.
* [measurements.md](measurements.md), [measurements-sat.md](measurements-sat.md):
  what runs, its verdicts and its timings, for a derivation and against
  one.
* [cost-log.md](cost-log.md): one row for each stage, the agents, the
  time lost, the words of the reviewer.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear (20 notes).
* [users-guide.md](users-guide.md): how a goal reads, the moves, the
  tactic's lines.
* `brief-2-1.md`, `brief-3-1.md`, `brief-4-1.md`: the briefs to the
  agents of stages 2, 3 and 4.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake build DILL dillrun)

111 jobs. The exercises and the tutorial file are in no library:

    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake env lean Play/DILL.lean)

## Files of the development

Theory files, each ending with `#axioms_within_file [propext, Quot.sound]`:

* `DILL/Form.lean`: formulas, sequents.
* `DILL/Perm.lean`: permutations without `Classical.choice` (MALL's file).
* `DILL/System.lean`: the family `Fam c`, exchange, the unrestricted
  zone's monotonicity, heights.
* `DILL/Semantics.lean`: phase spaces, models, `Valid`.
* `DILL/ILL.lean`: one-zone intuitionistic linear logic.
* `DILL/Statements.lean`: the goals as named statements.
* `DILL/Proof.lean`: the moves, `step`, S1, S2.
* `DILL/Source.lean`: the sources' derivations, as terms.
* `DILL/Soundness.lean`, `DILL/Completeness.lean`: the two theorems of
  the phase semantics; cut elimination as a proposition.
* `DILL/Cut.lean`, `DILL/Invert.lean`: both cuts admissible, cut
  elimination as a function, the inversions, the deduction theorems.
* `DILL/Results.lean`: the structural results, identity expansion,
  subformulas.
* `DILL/Decide.lean`: the decision without `!`.
* `DILL/Translate.lean`: to and from one-zone ILL.
* `DILL/Goals.lean`: the goals joined from the others, and the eight
  refutations.
* `DILL/Run.lean`, `DILL/Saturated.lean`, `DILL/SatRun.lean`,
  `DILL/Engine.lean`: the certifiers, the saturated sets and their
  soundness, the engine.

Code and tests, with no bound: `DILL/Tactic.lean` (printers, candidates,
the tactic `dillmove`), `DILL/Lazy.lean` (the search), `DILL/Refute.lean`
(the producer of saturated sets), `DILL/Corpus/Basic.lean` (the corpus),
`Main.lean` (the driver `dillrun`), `Corpus/` (the measuring scripts),
`DILL/Test.lean`, `DILL/RunTest.lean`, `DILL/SatTest.lean`,
`DILL/TutorialTest.lean`, `DILL/TutorialPins.lean` (generated by
`scripts/tutorial_pins.py`).
