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
| 1. Adopt | in progress | | |
| 2. Prove | not started | | |
| 3. Run | not started | | |
| 4. Explore | not started | | |

## Files here

* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's results, from the Coq files, without
  printed numbers until the prose is read.
* [cost-log.md](cost-log.md): one row for each session.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear.

The other files of a campaign folder (`rule-table.md`, `statements.md`, `measurements.md`, `users-guide.md`,
`report.md`) are listed here when they exist.

## Build

Nothing to build yet.
