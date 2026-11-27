# Brief: <CALCULUS>, stage <stage number> (<its name>)

*Template, kept as `brief-<stage number>-<k>.md`, `k` counting that
stage's briefs from 1. Written when work is handed on: to an agent
that takes a task beside the operator (goals of Prove, a certifier, the
tutorial); or, where a session must end, to whoever opens the next one
(`SKILL.md`, rule 5). The reader starts fresh and has only this page
and what it tells it to read. Do not paste history into it: point at
files.*

Written <date and time, from the clock>.

The target, the place of the files and the rules of the project are in
`<campaign folder>/decisions.md`, the first entry. <Any word of the
reviewer that changes one of them: which entry.>

## The task

<One paragraph: the stage, and what "done" is. Then the list from the
skill's stage, with anything the plan adds.>

<Where goals are handed to an agent: each statement by its name in the
Lean file; the tests the result must pass; the files the agent will
write, which the operator keeps out of its commits until the agent
reports; the names already taken in the calculus's namespace, or a
namespace of the agent's own (a second `def step` compiles until both
files are imported); the operator's design, where there is one, with
the line "another design is welcome"; and that the agent builds by
target, not the whole library.>

<Always: "Write your files to disk early and grow them: a session can
end under a running command, and what is only in the conversation is
then lost. Run a long build or timing in the background, with its
output in a file. Before any build, look at what is running and at the
free memory (the one line and its thresholds are in the reviewer's global
instructions): builds may run side by side while the machine has room,
and a build is held back when it does not. An evaluation of unknown
size runs under `lake env lean -M <megabytes>`, and not beside a large
build.">.

## Read, in this order

Leave out what does not exist yet.

1. <The part of the skill the task needs, by file and section, where it
   needs one. For a hand-over of the campaign: `SKILL.md` from "The
   method" on, then the part and the pitfalls for the stage.>
2. `<campaign folder>/plan.md`.
3. <The files of the development to read, each with one line on why.>

<For a hand-over of the campaign, also `decisions.md`, where any word of
the reviewer that came after this brief is recorded before anything
else, and the status board.>

## What is decided

<The decisions that bear on this stage, each by its entry in
`decisions.md`. A stop that still waits for its answer is named here,
with what may go on meanwhile.>

## What is not decided

<Open choices, each with a recommendation. The reader decides and
records; none of them is a reason to wait.>

## Limits

<The plan's budget for this stage: reaching it closes the stage with
what is OPEN. A statement refuted, a need of the library and a
divergence from the source are recorded, and the work goes on. What
would be a stop (`SKILL.md`, "Deciding, checking, stopping", 3), if
anything is in sight.>

## Done looks like

<The files that will exist; the checks run; a report of what was done
and what was not. For a hand-over of the campaign: the status board
brought up to date, a row in the cost log, and the next stage begun, or
the next brief.>
