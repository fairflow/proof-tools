# GLS: the cost log

Started on the first day of the Survey, one row for each session. Times
come from the clock (`date`), never from an estimate. A figure the
environment does not give is written "not known".

## Sessions

| # | stage | operator (person, or model and settings) | started cold, or handed on from a brief, or went on in the session | began | ended | waiting on builds (the sum of the build commands' times) | waiting at a stop | requests | output tokens | input read again (cached) | cost | Lean lines added / removed (`git diff --stat`) | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | the first act | Claude Fable 5.2, in the Claude desktop app; effort not known to the operator | started cold, from a brief written by another session that had not read the paper | 2026-11-25 08:46 | 2026-11-25 08:56 | none | none (the question was sent and the work went on) | not known | not known | not known | not known | 0 | this folder's first four files |
| 1 (went on) | Survey | the same session | went on in the session | 2026-11-25 08:56 | 2026-11-25 09:08 | 3 s (one build of the library, from a cloned `.lake`; two scratch files, 1 s each) | none: the question is unanswered and the work went on | not known | not known | not known | not known | 0 (two scratch files outside the repository, 190 lines, not kept) | `plan.md`, `skeleton.md`, six entries of `decisions.md` |
| 1 (went on) | Adopt | the same session | went on in the session | 2026-11-25 09:08 | 2026-11-25 09:24 | under 1 minute in all (each build of the package 1 to 4 s); 10 minutes lost to a shell command of the operator's that waited on its input | none | not known | not known | not known | not known | 961 added (`GLS/*.lean`, `Play/GLS.lean`) | `rule-table.md` (287 lines), `statements.md` |
| 1 (went on) | Prove, goals 1 to 3 | the same session; one agent (a cold reader, for the reading back of 17 statements) | went on in the session | 2026-11-25 09:24 | 2026-11-25 09:35 (the commit `c96ddc1`) | not summed (each build of the package under 15 s; `GLS/Screen.lean` 9 s) | none | not known | not known | not known | not known | 1 710 added (11 files) | `statements.md`, `decisions.md`: 225 added |
| 1 (went on) | Prove, goals 4 to 6 | an agent of the session, started cold from `brief-2-1.md` (Claude, the session's model) | handed on from a brief | 2026-11-25 09:38 | about 09:53 (907 s by the agent's report) | not known | none | not known | 225 816 tokens in all, by the agent's report | not known | not known | 742 added (`Structural`, `Invert`, `Contract`, `PS`, `Cut`) | none |
| 1 (went on) | Run, Explore | the same session, while the agent worked | went on in the session | 2026-11-25 09:35 | about 09:57, when the session stopped with a measuring run in progress (the commit `c9880e8` at 09:50) | not summed; the measuring runs: about 6 minutes | none | not known | not known | not known | not known | 1 599 added (12 files) | 726 added (the tutorial's guide, the brief, `decisions.md`) |
| (no session) | | | | 2026-11-25 09:57 | 2026-11-25 13:14 | | 3 h 17 min in which nothing ran. The question of 08:55 was open, and was not what the work waited on: every stage had gone on without its answer | | | | | | |
| 1 (resumed) | the comparison with the prose; S24; the repair of `dedup`; the closing | the same session, resumed from a summary of itself; two agents (cold readers: on the thesis's pages, and for S24) | went on from the session's own summary | 2026-11-25 13:14 | the time at the head of `report.md` | not summed; the full build from clean and the measuring runs are in `measurements.md` | none | not known | not known | not known | not known | 849 added, 22 removed (10 files, with the agent's five) | `measurements.md`, `report.md`, and changes to every file here |
| 2 | after the campaign: uniform interpolation; the intuitionistic variants; `∧` and `∨` | Claude Opus 5.5, in the Claude desktop app, a session started by another session; two agents for the literature | started from a brief written by another session | 2026-11-26 09:46 | 2026-11-26 10:40 | not summed (the full library 22 s from a cloned `.lake`; each file under 15 s; two test runs stopped by hand after 10 minutes, on an interpolant of 11 million nodes) | none | not known | not known | not known | not known | about 1 550 added (four files) | the three reports `2026-11-26-*.md` (about 800 lines) |

Where the tokens and the cost come from: not known to the operator, and
not filled.

## Words of the reviewer

Every message from the reviewer during the campaign, classed.

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
| 1 | 2026-11-25 08:46 | the first act | command | "the sequent calculus GLS for provability logic GL, from Goré, Ramanayake and Shillito (TABLEAUX 2021); you may download the paper" (through a brief) | it began the campaign |
| 2 | 2026-11-25 13:14 | Run, Explore (the comparison owed since the Survey) | answer at a stop | "yes you can download the thesis and any other materials to which you have online access that may assist you in the formalisation." | the thesis fetched; the comparison with the prose made |
| 3 | 2026-11-25 13:33 (when it reached the operator; typed earlier, in the session that started this one) | after the closing page | answer at the same stop, relayed | "permission to dowload publicly available materials such as PhD theses should be a standard part of the relevant skills" | nothing in what was done; an entry of `decisions.md` on the target as it ended |

## By stage

Clock time, from the commits and from `date`. The stages overlapped from
09:35: the agent proved goals 4 to 6 while the operator built Run and
Explore.

| stage | from | to | clock time |
|---|---|---|---|
| the first act | 08:46 | 08:56 | 10 min |
| 0. Survey | 08:56 | 09:08 | 12 min |
| 1. Adopt | 09:08 | 09:24 | 16 min (10 of them lost to a command of the operator's that waited on its input) |
| 2. Prove, goals 1 to 3 | 09:24 | 09:35 | 11 min |
| 2. Prove, goals 4 to 6 (the agent) | 09:38 | about 09:53 | 15 min |
| 3. Run and 4. Explore | 09:35 | about 09:57 | 22 min |
| nothing running | 09:57 | 13:14 | 3 h 17 min |
| the comparison with the prose, S24, the repair, the closing | 13:14 | the time at the head of `report.md` | filled there |

Working time to the end of Explore: 71 minutes (08:46 to 09:57).

Lean, at the end: 5 103 lines in 35 files (`wc -l` over `GLS.lean`,
`GLS/`, `Play/`, `Main.lean`), of which 163 are generated
(`GLS/Corpus/Facts.lean`) and about 1 400 are tests, screens, exercises
and the tutorial. The two measuring scripts: 190 lines of Python. The
documents of this folder: about 2 600 lines.

Agents of the session (each a fresh context, for one task): 5. A cold
reader on the Coq file (the second transcription); a cold reader for
the reading back of 17 statements; the agent of `brief-2-1.md`; a cold
reader on the thesis's pages (the second transcription, from the
prose); a cold reader for S24. Their tokens, except the third's, were
not recorded.

## Errors of transcription

The list is in `rule-table.md`. The count: 0. Neither second
transcription, nor the comparison with the thesis's figure, nor the
worked derivations, nor soundness and completeness found one.

Errors of the operator's that were not of transcription, each caught by
a build or a measurement: three pinned messages or values written from
expectation; a comment in the corpus; a claim in `decisions.md` about
how the kernel checks a tree of moves, corrected there; `dedup`, which
called itself twice (`method-notes.md`, 26); four times a time written
ahead of the clock, corrected from `date`.

## What the operator did unaided, and what it did not

Unaided: everything in the repository. The reviewer's two messages gave
the target and the permission to download.

Not done by the operator, and not done at all: no person has typed the
exercises or read the tutorial; the paper of 2021 (Springer, behind a
paywall) was not obtained, so the figure was compared with the thesis's
chapter 12, which the thesis says is that paper's content; of the
thesis, only chapter 12 was read (not sections 2.1, 4.2, 5.1, which it
leans on for notation); nothing was sent to the source's authors.
