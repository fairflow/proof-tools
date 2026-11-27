# <CALCULUS>: the cost log

*Template. Started on the first day of the Survey, one row for each
session. Times come from the clock (`date`), never from an estimate. A
figure the environment does not give is written "not known": do not guess
it. The purpose is to measure the method, so a bad row is as useful as a
good one.*

## Sessions

| # | stage | operator (person, or model and settings) | started cold, or handed on from a brief, or went on in the session | began | ended | waiting at a stop | Lean lines added / removed (`git diff --stat`) | document lines |
|---|---|---|---|---|---|---|---|---|
| 1 | Survey | | | | | | | |

Requests, tokens and cost: an operator that is a model does not know
them, writes "not known", and does not work a figure out from the
length of the session. They are the reviewer's to fill, from the tool's
usage report, if the method is to be costed: <who filled them, on what
date and from what; or "not filled">. A person writes hours.

Where one session runs several stages, the rows are the stages: one row
each, "went on in the session" in the fourth column, the times from the
status board's entries, and the lines of Lean from the stage's commits
(`git show --stat`).

## Agents

One row for each agent the operator started. The environment usually
reports an agent's duration and tokens when it ends: enter them as
given, and "not known" otherwise.

| # | stage | task, in a few words | brief | began | ended | duration, as reported | tokens, as reported | result: what was kept, what was redone |
|---|---|---|---|---|---|---|---|---|

## Time lost

Where the clock ran and no work was done (a hook of the application
that did not answer, a process that ended under a running command, a
session idle until someone wrote): from when to when, from the session's
record, not from memory.

## Words of the reviewer

<The count, by class (the classes are in `templates/decisions.md`), up
to the closing page. `decisions.md` has each,
with the words copied and what it changed.>

## By stage

| stage | from | to | elapsed | words of the reviewer |
|---|---|---|---|---|
| 0 Survey | | | | |
| 1 Adopt | | | | |
| 2 Prove | | | | |
| 3 Run | | | | |
| 4 Explore | | | | |

From the command to the closing page: <elapsed, by the clock>; waiting
at a stop: <the sum>.

## Errors of transcription

The list is in `rule-table.md`. Here, the count, by what found each:
`#rules` or `#slime` <n>; a worked derivation <n>; the second
transcription <n>; soundness or completeness <n>; a person <n>; later
use <n>.

## What the operator did unaided, and what it did not

<A few lines for each stage. Include what the operator knew that the skill
did not tell it, and each place where it stopped and need not have.>
