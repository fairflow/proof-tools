# MALL: campaign folder

Propositional multiplicative-additive linear logic, in the one-sided
sequent calculus of J.-Y. Girard, *Linear logic* (TCS 50, 1987),
Definition 1.15, without the exponentials: connectives ⊗, ⅋, **1**, ⊥,
&, ⊕, ⊤, **0**, negation a defined function, no weakening and no
contraction. The target, the paper, the place of the files and the rules
of the project: [decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2, one session for all stages, with five agents
it started ([cost-log.md](cost-log.md)). The method: the skill
`calculus-campaign`, as it stood at commit `906e2fa` of `proof-tools`.

Waiting on the reviewer: nothing. The campaign is closed:
[report.md](report.md).
The page was pushed to `main` (`ddd34e6`) and published to the reviewer
as a private page (https://claude.ai/artifact/HXsUnPBBZSQdoc9Ku72b1E),
2026-11-26 11:06 GMT.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done, 10:04 | the plan's choices screened and recorded: 6 entries; the encoding and "valid" screened in scratch | [plan.md](plan.md), [decisions.md](decisions.md), `skeleton.md`, [survey-report.md](survey-report.md) |
| 1. Adopt | done, 10:18 | derivations of what the source asserts, as terms: 10 (it draws none); the second transcription: run, 11 rules in both readings, no difference, 5 ambiguities settled; S2: PROVED | [rule-table.md](rule-table.md), `MALL/System.lean`, `MALL/Source.lean`, `MALL/Proof.lean`, `Play/MALL.lean` |
| 2. Prove | done, 10:32 | statements screened and read back: 17 of 17; goals PROVED: 12; REFUTED: 2 (weakening and contraction, as the source says); OPEN: 0 | [statements.md](statements.md) |
| 3. Run | done, 11:00 | negative tests: 13, each rejected in the kernel; level 3. The frontier: a sequent with no derivation, ten or more formulas with ⊗, and no countermodel among the small structures tried | [measurements.md](measurements.md), `MALL/Run.lean`, `MALL/Lazy.lean`, `MALL/Model.lean`, `MALL/ModelRun.lean`, `Main.lean` |
| 4. Explore | done, 11:00 | the tutorial: every line elaborated, what each step shows pinned (`MALL/ExploreTest.lean`) | `Play/MALLTutorial.lean`, [users-guide.md](users-guide.md), `MALL/Explore.lean` |

## Files here

* [report.md](report.md): the closing page.
* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse; first, the target. No word of the reviewer came
  during the campaign.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's numbered results.
* [survey-report.md](survey-report.md): the report of the agent that
  fetched the other sources and surveyed the mechanisations.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the second transcription; the divergence log.
* [statements.md](statements.md): every statement, PROVED, REFUTED or
  OPEN, with what the reading back said of it.
* [measurements.md](measurements.md): what runs, its verdicts and its
  timings; the frontier.
* `../tutorial.md`: the tutorial, with 25 graded exercises, in the
  pinned format (`scripts/tutorial_pins.py`): 16 pins. Its solutions are
  `MALL/TutorialTest.lean`; the exercises to type are
  `Play/MALLExercises.lean`. Added after the closing page.
* [interpolation-sources.md](interpolation-sources.md): what four
  sources state about interpolation for this logic, read by an agent.
* [users-guide.md](users-guide.md): how a goal reads, the moves, the
  tactic's lines, the messages.
* [cost-log.md](cost-log.md): the sessions and the agents.
* `method-notes.md`: where the skill was wrong, silent or unclear; and
  what carries over to phase 2 of the round.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build MALL mallrun)

The exercises and the tutorial are in no library:

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake env lean Play/MALLTutorial.lean)

## Files of the development

Theory (each ends with `#axioms_within_file [propext, Quot.sound]`):

* `MALL/Form.lean`: formulas, linear negation, sizes.
* `MALL/Perm.lean`: permutations by counting (`perm_count`), without
  `Classical.choice`.
* `MALL/System.lean`: the families `Fam` (with cut) and `CF` (without);
  exchange; heights.
* `MALL/Source.lean`: the figure as it stands (`Lit`), equivalent to
  `Fam`; derivations of what the source asserts.
* `MALL/Proof.lean`: the moves, `step`, S1 and S2.
* `MALL/Semantics.lean`: phase spaces, facts, phase structures, the
  interpretation, validity.
* `MALL/Statements.lean`: the goals, as named statements.
* `MALL/Soundness.lean`: soundness (1.16).
* `MALL/Completeness.lean`: Okada's lemma, the syntactical model,
  completeness without cut (1.17), cut elimination as a proposition.
* `MALL/Decide.lean`: the search for a derivation without cut, proved
  complete.
* `MALL/FiniteModel.lean`: the finite model property.
* `MALL/Results.lean`: identity expansion, decidability, weakening and
  contraction refuted, the disjunction property, the subformula
  property.
* `MALL/Cut.lean`: cut elimination as a function; the inversions.
* `MALL/Model.lean`: finite phase structures as data, and their check.
* `MALL/Run.lean`, `MALL/ModelRun.lean`: the certifiers, the producers,
  level 3.
* `MALL/UniformLyndon.lean`: the condition on signs for the uniform
  interpolant.
* `MALL/Split.lean`, `MALL/Craig.lean`, `MALL/Uniform.lean`: Craig
  interpolation with Lyndon's condition as a function on derivations;
  uniform interpolation, the interpolant computed (added by command,
  2026-11-26).
* `MALL/Saturated.lean`, `MALL/SatRun.lean`: saturated sets of sequents
  as certificates of non-derivability, the finite phase structure a set
  presents, and the completeness of the certificate (added after the
  closing page).

Code (no bound; nothing in it is trusted):

* `MALL/Tactic.lean`: the printers, the candidates, the tactic
  `mallmove`.
* `MALL/Lazy.lean`: the search by lazy splitting.
* `MALL/Refute.lean`: the producer of saturated sets; the structure of
  a set computed by tables.
* `MALL/Explore.lean`: tactics of the calculus; `explain`.
* `MALL/Screen.lean`: the phase semantics evaluated over small cyclic
  groups, as a screen.
* `MALL/Corpus/Basic.lean`, `MALL/Corpus/Facts.lean` (generated),
  `Main.lean` (`mallrun`), `Corpus/measure.py`,
  `Corpus/measure_model.py`.
* Tests: `MALL/Test.lean`, `DecideTest.lean`, `CutTest.lean`,
  `RunTest.lean`, `ModelTest.lean`, `ExploreTest.lean`, `SatTest.lean`,
  `TutorialTest.lean`, `TutorialPins.lean` (generated), `CraigTest.lean`,
  `UniformTest.lean`.
* In no library: `Play/MALL.lean` (exercises), `Play/MALLTutorial.lean`.
