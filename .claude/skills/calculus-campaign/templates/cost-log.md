# <CALCULUS>: the cost log

*Template. Started on the first day of the Survey, one row for each
session. Times come from the clock (`date`), never from an estimate. A
figure the environment does not give is written "not known": do not guess
it. The purpose is to measure the method, so a bad row is as useful as a
good one.*

## Sessions

The four columns from "requests" to "cost" are about an operator that is
a language model; a person writes hours under "cost" and leaves the
others. **An operator that is a model does not, as a rule, know them**:
its environment shows it neither its requests nor its tokens nor what
they cost. It writes "not known" in each, and does not work a figure out
from the length of the session. They are the reviewer's to fill, from
the tool's usage report, if the method is to be costed; the line below
the table says who filled them and from what. What the operator can
measure, it measures: the clock, the builds, the lines.

| # | stage | operator (person, or model and settings) | started cold, or handed on from a brief, or went on in the session | began | ended | waiting on builds (the sum of the build commands' times) | waiting at a stop | requests | output tokens | input read again (cached) | cost | Lean lines added / removed (`git diff --stat`) | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Survey | | | | | | | | | | | | |

Where the tokens and the cost come from: <the tool's usage report, read
by the reviewer on <date>; the transcript; "not known to the operator,
and not filled">.

## Words of the reviewer

Every message from the reviewer during the campaign, classed. An
independent campaign may have none after the command.

* **command**: a goal set, a redirection, a thing to do;
* **correction**: the operator was wrong or unclear and was put right;
* **rescue**: the operator was stuck and could not have gone on alone;
* **question**: the reviewer asks about the mathematics or about the
  method. Say what it led to, or that it changed nothing;
* **answer at a stop**: to the one thing the operator asked
  (`decisions.md`, "Stops");
* **a thing to pass**: the reviewer asks to pass a thing themselves,
  which makes it a gate;
* **a report from the exercises file**.

A message that is two of these is entered once, with both classes.

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|

## By stage

| stage | sessions | elapsed | of which waiting on builds | of which waiting at a stop | requests ("not known", where the rows say so) | cost (the same) | words of the reviewer, by class |
|---|---|---|---|---|---|---|---|
| 0 Survey | | | | | | | |
| 1 Adopt | | | | | | | |
| 2 Prove | | | | | | | |
| 3 Run | | | | | | | |
| 4 Explore | | | | | | | |

From the command to the closing page: <elapsed, by the clock>; working:
<the sum of the sessions>; waiting at a stop: <the sum>.

## Errors of transcription

The list is in `rule-table.md`. Here, the count, by what found each:
`#rules` or `#slime` <n>; a worked derivation <n>; the second
transcription <n>; soundness or completeness <n>; a person <n>; later
use <n>.

## What the operator did unaided, and what it did not

<A few lines for each stage. Include what the operator knew that the skill
did not tell it, and each place where it stopped and need not have.>
