# GLS: the cost log

Started on the first day of the Survey, one row for each session. Times
come from the clock (`date`), never from an estimate. A figure the
environment does not give is written "not known".

## Sessions

| # | stage | operator (person, or model and settings) | started cold, or handed on from a brief, or went on in the session | began | ended | waiting on builds (the sum of the build commands' times) | waiting at a stop | requests | output tokens | input read again (cached) | cost | Lean lines added / removed (`git diff --stat`) | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | the first act | Claude Fable 5.2, in the Claude desktop app; effort not known to the operator | started cold, from a brief written by another session that had not read the paper | 2026-11-25 08:46 | 2026-11-25 08:56 | none | none (the question was sent and the work went on) | not known | not known | not known | not known | 0 | this folder's first four files |
| 1 (went on) | Survey | the same session | went on in the session | 2026-11-25 08:56 | 2026-11-25 09:08 | 3 s (one build of the library, from a cloned `.lake`; two scratch files, 1 s each) | none: the question is unanswered and the work went on | not known | not known | not known | not known | 0 (two scratch files outside the repository, 190 lines, not kept) | `plan.md`, `skeleton.md`, six entries of `decisions.md` |
| 1 (went on) | Adopt | the same session | went on in the session | 2026-11-25 09:08 | 2026-11-25 09:25 | under 1 minute in all (each build of the package 1 to 4 s); 10 minutes lost to a shell command of the operator's that waited on its input | none | not known | not known | not known | not known | 760 added (`GLS/*.lean`, `Play/GLS.lean`) | `rule-table.md` (287 lines), `statements.md` |

Where the tokens and the cost come from: not known to the operator, and
not filled.

## Words of the reviewer

Every message from the reviewer during the campaign, classed.

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
| 1 | 2026-11-25 08:46 | the first act | command | "the sequent calculus GLS for provability logic GL, from Goré, Ramanayake and Shillito (TABLEAUX 2021); you may download the paper" (through a brief) | it began the campaign |

## By stage

Filled when a stage ends.

## Errors of transcription

The list is in `rule-table.md`. Here, the count, by what found each:
filled at the end of Adopt.

## What the operator did unaided, and what it did not

Filled when a stage ends.
