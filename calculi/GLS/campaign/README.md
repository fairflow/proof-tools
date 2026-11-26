# GLS: campaign folder

The status board. It is changed in the same commit as the thing it
reports, so that it is true at every commit.

GLS is a sequent calculus for the modal provability logic GL
(Gödel-Löb), on multisets, with one modal rule (GLR). The target, the
paper, the place of the files and the rules of the project:
[decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2 (a language model), one session, started cold
from a brief on 2026-11-25, with five agents for single tasks; the rows
are in the cost log. The method: the skill `calculus-campaign`, as it
stood at commit `818483e` of proof-tools (the text rewritten on
2026-11-25, of which this is the first run).

Waiting on the reviewer: nothing. The campaign is done; the closing page
is [report.md](report.md).

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done | the plan's choices screened and recorded: 6. The source read: the authors' Coq files first, then the thesis's chapter 12 (from 13:14, on the reviewer's word); the paper of 2021 itself was not obtained | [plan.md](plan.md), `skeleton.md`, [decisions.md](decisions.md) |
| 1. Adopt | done | worked derivations as terms: 8 (the four cases of the Coq file's identity and one more; the thesis's Examples 12.4.1 and 12.4.2, of which the first is three trees); the second transcription: run twice by cold readers, on the Coq file and on the thesis's pages, 0 differences in the rules; `#slime`: no computed index; S1 and S2: PROVED; every message of the tests pinned, the six exercises run by script | [rule-table.md](rule-table.md), `GLS/System.lean`, `GLS/Proof.lean`, `GLS/Source.lean`, `GLS/Test.lean`, `Play/GLS.lean` |
| 2. Prove | done | statements screened: all of S3 to S19 and S24; read back by a cold reader: 18 (S3 to S18, of which S6 is two, and S24; S19 has S10's type), all agree; goals PROVED: 17 of 17, and our own 6 of 6; OPEN: 0; REFUTED: 0; every theory file within `[propext, Quot.sound]` | [statements.md](statements.md), `GLS/Screen.lean` |
| 3. Run | done, to level 3 | negative tests: 10 (6 in `GLS/RunTest.lean`, 4 in `GLS/SetSearchTest.lean`); the frontier: the proved search is cut off at 28 nested boxes, the search over sets runs 256 in 0.3 s and its tree of moves is checked by the kernel in 2 s | [measurements.md](measurements.md), `GLS/Run.lean`, `GLS/SetSearch.lean`, `Main.lean` |
| 4. Explore | done | the tutorial: every line elaborated, every claim pinned in `GLS/ExploreTest.lean`; no person has typed the exercises | `Play/GLSTutorial.lean`, [users-guide.md](users-guide.md), `GLS/Explore.lean` |

## Files here

* [report.md](report.md): the closing page.
* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's results, with the thesis's numbers and
  pages and the Coq files' names.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the two second transcriptions; the divergence log.
* [statements.md](statements.md): every statement, PROVED, REFUTED or OPEN.
* [measurements.md](measurements.md): what runs, its verdicts and its
  timings.
* [cost-log.md](cost-log.md): one row for each session.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear (26 notes).
* [users-guide.md](users-guide.md): how a goal reads, the moves, the
  tactic's lines.
* `brief-2-1.md`: the brief on which goals 4 to 6 were handed to an agent.
* [2026-11-26-ui.md](2026-11-26-ui.md): uniform interpolation for GL, PROVED
  through GLS, and how the proof compares with the literature.
* [2026-11-26-intuitionistic.md](2026-11-26-intuitionistic.md): iGL, iSL, KM,
  mHC: the literature, what would transfer, and why they are consistent with GL.
* [2026-11-26-connectives.md](2026-11-26-connectives.md): `∧` and `∨` defined,
  their rules derived, the sides exchanged.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake build GLS glsrun)
    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake env lean Play/GLS.lean)
    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake env lean Play/GLSTutorial.lean)

## Files of the development

Theory files are each within `[propext, Quot.sound]`
(`#axioms_within_file` at the foot of each).

* `GLS/Form.lean`: formulas, sequents, `xbox`. Theory.
* `GLS/System.lean`: the families `Fam` (GLS) and `PSFam` (PSGLS), `#rules`, `#slime`, the height. Theory.
* `GLS/Source.lean`: the source's worked derivations as terms of the family. Theory.
* `GLS/Proof.lean`: the moves, `step`, S1, S2. Theory.
* `GLS/Semantics.lean`: models, GL, truth, `Valid`, trees as models, and every statement as a named type. Theory.
* `GLS/Lemmas.lean`: lists, `erase`, permutations, `xbox`, without choice. Theory.
* `GLS/Soundness.lean`: S3. Theory.
* `GLS/Identity.lean`: S8. Theory.
* `GLS/TreeModel.lean`: the model of a finite tree; S20. Theory.
* `GLS/Measure.lean`: the weight; S9. Theory.
* `GLS/Search.lean`: the search that returns a derivation or a tree; S4. Theory.
* `GLS/Completeness.lean`: S5, S6, S7, S10. Theory.
* `GLS/Structural.lean`, `GLS/Invert.lean`, `GLS/Contract.lean`: S11 to S17. Theory.
* `GLS/PS.lean`: S18. Theory.
* `GLS/Cut.lean`: S19, the source's cut. Theory.
* `GLS/CutRule.lean`: GLS + (cut); S24. Theory.
* `GLS/Connectives.lean`: `¬`, `⊤`, `∧`, `∨`, `◇` defined; their truth at a tree. Theory.
* `GLS/Interpolation.lean`: uniform interpolation for GL; the interpolant as the bisimulation quantifier; its modal depth. Theory.
* `GLS/ConnectiveRules.lean`: the derived rules of the defined connectives, their inverses, switching sides. Theory.
* `GLS/InterpolationTest.lean`: the tests of the last three, and their statements pinned. Code.
* `GLS/Run.lean`: the certifiers, the producer, the engine; S21, S22. Theory.
* `GLS/SetSearch.lean`: the proof system over sets, its certifier, the fast search, the checked decisions; S23. Theory (the fast search is code: nothing is proved of it).
* `GLS/Explore.lean`: the countermodel drawn, the routine moves, `found`. Code.
* `GLS/Tactic.lean`: the printers, the candidates, the tactic `glsmove`. Code.
* `GLS/Screen.lean`: the screens of the statements, compiled. Code.
* `GLS/Test.lean`, `GLS/SearchTest.lean`, `GLS/CutTest.lean`, `GLS/RunTest.lean`, `GLS/SetSearchTest.lean`, `GLS/ExploreTest.lean`: the tests, every message pinned. Code.
* `GLS/Corpus/Basic.lean`: 16 entries and four families; `GLS/Corpus/Facts.lean`: the 16 facts, written by `glsrun facts`, checked by the kernel.
* `Main.lean`: the driver `glsrun`. `Corpus/measure.py`, `Corpus/measure_set.py`: the measuring scripts.
* `Play/GLS.lean`: the exercises; `Play/GLSTutorial.lean`: the tutorial. In no library.
