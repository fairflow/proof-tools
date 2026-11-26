# DILL: the cost log

Times come from the clock (`date`). A figure the environment does not
give is written "not known".

## Sessions

One session runs the stages; the rows are the stages. The stages overlap
(the proofs were handed out while the explorer was written), so the
times are of the commits that begin and end each.

| # | stage | operator | started cold, or handed on, or went on | began | ended | waiting on builds | waiting at a stop | requests | output tokens | input read again | cost | Lean lines added / removed | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Survey | Claude Fable 5.2 | started from a brief written by another session; cold as to the calculus | 2026-11-26 14:47 GMT | 14:59 (the plan committed) | a few seconds (two scratch files) | none (see "Time lost") | not known | not known | not known | not known | 0 | plan 355, skeleton 67, decisions (first entries), survey report 828 |
| 2 | Adopt | the same | went on in the session | 15:13 | 15:42 (the tests pinned again) | not summed; each build was seconds | none | not known | not known | not known | not known | 2 823 lines in eight files (Form, Perm, System, Proof, Tactic, Source, Test, Play/DILL), counted from the files | rule table 443 |
| 3 | Prove | the same, with agents A to E | went on in the session | 15:20 (the brief) | 15:33 (the cuts built; the joined goals at 15:30) | not summed; the whole package builds in under a minute | none | not known | not known | not known | not known | 3 012 lines in eleven files (Semantics, ILL, Statements, Soundness, Completeness, Results, Decide, Translate, Cut, Invert, Goals) | statements 380, brief 269 |
| 4 | Run | the same, with agents G and H | went on in the session | 15:29 (the brief) | 16:27 (the measurements written up) | | none | not known | not known | not known | not known | 2 216 lines in eleven files (Lazy, Run, RunTest, Corpus/Basic, Main, Saturated, Refute, SatRun, SatTest, Engine, Corpus/SatMain), and 368 of Python | measurements 386 and 161, brief 184 |
| 5 | Explore | the same, with an agent | went on in the session | 15:34 (the agent started; three repairs of the instance at 15:41) | 16:33 (this page) | | none | not known | not known | not known | not known | 2 294 lines in four files (TutorialTest, TutorialPins which is generated, Play/DILLExercises, Play/DILLTutorial) | tutorial 1 650, user's guide 182, closing page 279, brief 136 |

Where the tokens and the cost come from: not known to the operator, and
not filled. The agents' figures are as the environment reported them.

## Agents

"Began" is the clock at the launch (read by `date` in the call before or
after it); "ended" is that time plus the duration the environment
reported, so it is computed, not read.

| # | stage | task, in a few words | brief | began | ended | duration, as reported | tokens, as reported | result: what was kept, what was redone |
|---|---|---|---|---|---|---|---|---|
| 1 | Survey | the literature: a phase semantics, the finite model property, undecidability, formalisations, places for the further results | in the session; its report is `survey-report.md` | 14:49 | 15:09 | 19.5 min | 327 794 | kept whole; the operator read the semantics again from the page |
| 2 | Adopt | the second transcription, from four page images | in the session (the text is in the rule table's account) | 15:15 | 15:19 | 3.3 min | 106 261 | kept: no difference from the family |
| 3 | Prove | E: the translation to and from one-zone ILL | `brief-2-1.md`, E | 15:20 | 15:24 | 3.3 min | 119 603 | kept whole |
| 4 | Prove | D: the decision without `!` | `brief-2-1.md`, D | 15:20 | 15:25 | 4.7 min | 134 707 | kept whole |
| 5 | Prove | C: the structural results, identity expansion, subformulas | `brief-2-1.md`, C | 15:20 | 15:27 | 6.0 min | 147 994 | kept whole; it found that `Fam.exch` and `Fam.mono` were compiled by well-founded recursion |
| 6 | Prove | the reading back, from an extract of 491 lines | in the session | 15:21 | 15:28 | 6.3 min | 120 026 | kept: its eight instances are the refutations |
| 7 | Prove | B: soundness and completeness | `brief-2-1.md`, B | 15:20 | 15:28 | 7.7 min | 165 340 | kept whole |
| 8 | Prove | A: the two cuts, cut elimination, the inversions, the deduction theorems | `brief-2-1.md`, A | 15:20 | 15:32 | 12.0 min | 199 006 | kept whole; it found the same defect of `Fam.exch` as agent C, and tested the repair |
| 9 | Adopt | F: the sources' derivations as terms, the tests, the exercises file | in the session | 15:24 | 15:40; again 15:41 to 15:42 | 15.5 min, then 1.4 min | 274 539 in all | kept; pinned again after the operator's three repairs of the instance |
| 10 | Run | G: the search, the certifiers, the corpus, the driver, the measurements | `brief-3-1.md`, G | 15:29 | cut off by the restart at 15:51; again 16:04 to 16:27 | 21.9 min, as reported at its end | 360 037 | kept; its measuring was stopped by the operator at 16:19 |
| 11 | Run | H: saturated sets, their soundness, the producer, the tests, the measurements | `brief-3-1.md`, H | 15:29 | cut off by the restart at 15:51, and not started again | not reported | not reported | kept whole: its files built as the restart left them; one placeholder taken out of its measurements |
| 12 | Explore | the tutorial page, its tests, the two Play files, the user's guide | `brief-4-1.md` | 15:34 | cut off by the restart at 15:51; again 16:22 to 16:31 | 8.1 min, as reported at its end | 479 615 | kept whole; the pins written again by the operator after the commit |

## Time lost

From 15:00:36 to about 15:12 GMT, about twelve minutes. The operator's
first write of `DILL/Form.lean` came back as declined by the user, with
the instruction to stop and wait; the operator stopped and asked. The
session that started this one read the application's log and this
session's record afterwards and reports (15:33, a message between
sessions): the reviewer had interrupted that session at 15:00:33 and
15:00:35 about something else; at 15:00:36 the application stopped the
family of sessions and interrupted this one; the write had been waiting
39.9 s for its permission and was recorded as "user rejected" at the
same millisecond as the interrupt. The reviewer declined nothing and
resumed this session at about 15:12. The survey agent went on working
through it.

From 15:51 to 16:03 GMT, twelve minutes, and the three agents' work in
flight. The machine restarted at 15:51 (the session that started this
one reports it, with the cause: several Lean builds at once, three of
them this campaign's agents G, H and the tutorial's, beside an
evaluation of another repository's that had no cap on its memory). This
session's last command before it was the push of 15:42; its first after
it was at 16:03. The agents had their files on disk: G's and H's Lean
built as it stood; H's measurements were written but for one
placeholder; G's measurements and the tutorial's last files were not.
The scratchpad was cleared: the fetched papers, the page images, the
cold readers' two reports and the scratch screens are gone (what they
showed is in the plan, the rule table and the statements). From 16:03 to 16:22 the operator let one agent build at a time (the
reviewer's word of that hour, relayed, and corrected at 16:22): nineteen
minutes in which the engine file and the tutorial waited behind timing
runs.

What probably caused the restart, from the measuring agent's own account
(`measurements.md`, "What went wrong in the measuring"): its first runs,
at 15:44 and 15:50, had no cap on memory, and the deadline of its script
ended `lake` and not the Lean process under it, so two kernel checks of
a large tree and one run of the proved search went on with nothing to
stop them; run again after the restart under a cap, the first of these
passes 8 GB. So this campaign was a cause, beside the other session's
evaluation that the first account named. The script now ends the whole
process group (tested with a shell command, not with Lean).

## Words of the reviewer

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
| 1 | 2026-11-26 | before the Survey | command | "Yes, start DILL" (relayed in the brief of the session that started this one) | the campaign |
| 2 | 2026-11-26 15:13 | Adopt | correction | "I declined no such thing." | the operator went on; nothing built was affected |

## Errors of transcription

The list is in `rule-table.md`: none. By what could have found one:
`#rules` or `#slime` 0; a worked derivation 0; the second transcription
0; soundness or completeness 0; a person 0; later use 0.

## By stage

| stage | elapsed, by the commits | words of the reviewer |
|---|---|---|
| 0 Survey | 14:47 to 14:59 | none |
| 1 Adopt | 15:13 to 15:42 (beside Prove from 15:20) | one correction |
| 2 Prove | 15:20 to 15:33 | none |
| 3 Run | 15:29 to 16:27, of which 31 minutes lost (the restart, and the wait behind one builder) | two questions; two rules on builds, relayed |
| 4 Explore | 15:34 to 16:33, of which the same 31 minutes | none |

From the brief to the closing page: 1 hour 46 minutes, by the clock (14:47 to 16:33);
of it about 43 minutes in which nothing or one thing ran ("Time lost").
Waiting at a stop the operator chose: none. 10 345 lines of Lean, of
which 3 439 are tests and generated pins (Test, TutorialTest,
TutorialPins, RunTest, SatTest); about 8 100 lines of documents, the
tutorial among them.

## After the close

| what | when (GMT, 2026-11-26) | by | words of the reviewer |
|---|---|---|---|
| `dillrun prove`, first form | to 21:18 (method note 21) | the directing session | a remark that a prover at the command line would be useful (as that session reports it) |
| `dillrun prove` brought to the skill's paragraph: the printed file, the report of a text not read, Lean's reading back, `dillrun corpus`, the script, the deadline, the measurements | 22:16 to 22:34 | the owner session, no agents | none; the task came from the directing session |

In the second row: three builds of the whole (116 jobs), three runs of
the script with every file elaborated, and the sizing of "a large
answer". One run was stopped by hand: the command on 24 equal atoms,
before it had a deadline (about 100 s; the free memory of the machine stayed at 90%).

## What the operator did unaided, and what it did not

The operator wrote the target, the plan, the formulas, the family, the
semantics' definitions, the one-zone family, the named statements, the
proof system with S1 and S2, the tactic, the joined goals and
refutations, the engine, the rule table, the statements document, the
briefs and this record; and built and ran every file an agent wrote
before it was recorded as PROVED. Agents wrote every other proof, the
tests, the search, the saturated sets, the measurements and the
tutorial. The operator read from the page: the source's Section 3 and
Theorem 7, and the two pages of the semantics; it did not read the
other papers of the survey. It stopped once where it need not have
(15:00), and held work back for nineteen minutes under a rule since
corrected.
