# GLS: campaign folder

The status board. It is changed in the same commit as the thing it
reports, so that it is true at every commit.

GLS is a sequent calculus for the modal provability logic GL
(Gödel-Löb). The target, the paper, the place of the files and the
rules of the project: [decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2 (a language model), one session, started cold
from a brief on 2026-11-25; the rows are in the cost log. The method:
the skill `calculus-campaign`, as it stood at commit `818483e` of
proof-tools (the text rewritten on 2026-11-25, of which this is the
first run).

Waiting on the reviewer: one question, asked 2026-11-25 08:55: may the
thesis's PDF be downloaded ([decisions.md](decisions.md), "Stops").
Meanwhile Adopt goes on from the authors' Coq files.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done, with one thing owed: Q1 is from the authors' Coq files, and its comparison with the prose waits for the download | the plan's choices screened and recorded: 6 (what "valid" means and GLR's soundness, in scratch; what `deriving` gives, on four types) | [plan.md](plan.md), `skeleton.md`, [decisions.md](decisions.md) |
| 1. Adopt | done, from the authors' Coq files; the comparison with the figure in prose is owed | worked derivations as terms: 4 of 4 cases of the source's one (`Id_all_form`), and one more; the second transcription: run on the Coq file, 0 differences in the rules, 5 remarks settled; `#slime`: no computed index; S1 and S2: PROVED; tests: every message pinned, the six exercises run by script | [rule-table.md](rule-table.md), [statements.md](statements.md), `GLS/System.lean`, `GLS/Proof.lean`, `GLS/Source.lean`, `GLS/Test.lean`, `Play/GLS.lean` |
| 2. Prove | in progress | | |
| 3. Run | not started | | |
| 4. Explore | not started | | |

## Files here

* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's results, from the Coq files, without
  printed numbers until the prose is read.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the second transcription; the divergence log.
* [statements.md](statements.md): every statement, PROVED, REFUTED or OPEN.
* [cost-log.md](cost-log.md): one row for each session.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear.

The other files of a campaign folder (`measurements.md`,
`users-guide.md`, `report.md`) are listed here when they exist.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake build)
    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake env lean Play/GLS.lean)

## Files of the development

* `GLS/Form.lean`: formulas, sequents, `xbox`. Theory, within `[propext, Quot.sound]`.
* `GLS/System.lean`: the families `Fam` (GLS) and `PSFam` (PSGLS), `#rules`, `#slime`, the height. Theory, the same bound.
* `GLS/Source.lean`: the source's worked derivation as terms of the family. Theory, the same bound.
* `GLS/Proof.lean`: the moves, `step`, S1, S2. Theory, the same bound.
* `GLS/Tactic.lean`: the printers, the candidates, the tactic `glsmove`. Code.
* `GLS/Test.lean`: the tests, every message pinned. Code.
* `Play/GLS.lean`: the exercises, in no library.
