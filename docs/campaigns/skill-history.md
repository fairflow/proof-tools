# The calculus-campaign skill: where its text came from

Started 2026-11-27 13:57 GMT, by the directing session of the round, when
the skill's main file was first pruned
(`docs/campaigns/pruning-2026-11-27.md`). The skill says what an operator
does. Which campaign showed the need of a rule, on what date, and what
each run showed, is kept here, and the skill points here once. Passages
are moved, not rewritten: what is quoted below stood in
`.claude/skills/calculus-campaign/SKILL.md` at commit `17acd9b`.

Later rounds add to this file whatever history a note brings with it; the
rule itself goes into the skill in a sentence.

## The runs

**The first run, 2026-11-23, Brünnler's system K.** Moved from "Status":

> The three parts have been used separately. The whole, from a paper to an
> explorer, has been run once: on Brünnler's system K, on 2026-11-23, by
> an operator that is a language model, under an earlier text in which the
> reviewer passed a gate before each step. That run's record (its cost
> log) shows: of seven gates one changed the work, the plan's; no error
> was found at a gate, each was found by a tool, a test or a screen that
> the operator ran; the reviewer lifted every gate in the middle of Prove;
> and most of the day was spent waiting.

**The rewriting, 2026-11-25, and the run on GLS the same day.**

> This text was rewritten on 2026-11-25 so that the operator works
> independently, and has been run once as rewritten: on GLS, the same
> day, by an operator that started cold. What that run shows, and what it
> does not:
>
> - the five stages ran in 71 minutes, with one question to the reviewer
>   (a download, since made the reviewer's standing word), which the work
>   did not wait on; every goal ended PROVED;
> - the session then ended under a running command and stood idle for
>   three hours, until the reviewer typed in it; the closing page was
>   written after that. So a run from the command to the closing page
>   with no word of the reviewer has not yet been made;
> - the second transcription and the reading back were carried out as
>   written (`reference/adopt.md` §7), and found no fault. No other check
>   found one either, so what they can catch is not known;
> - rule 1 was not kept to the letter: the rules were transcribed from
>   the authors' formalisation before any prose could be read, and were
>   compared with the prose afterwards;
> - this text was amended after that run, from its notes.

**The run on MALL, 2026-11-26.**

> It was run a second time as rewritten on 2026-11-26, on MALL, by an
> operator that another session started from a brief. What that run
> shows:
>
> - the five stages ran in 81 minutes (09:45 to 11:06 GMT), the closing
>   page delivered, with no word of the reviewer between the start and
>   the page: 12 goals PROVED, weakening and contraction REFUTED as the
>   source says, none OPEN. Five agents were started by the operator;
> - the second transcription and the reading back again found no fault;
>   the reading back found the instances that refute weakening and
>   contraction, unprompted;
> - three pinned values were typed from expectation, each wrong, each
>   refused by the build (`reference/pitfalls.md`, 11);
> - after the page, at the reviewer's word, a complete certificate
>   against a derivation and the tutorial page were added. In that
>   stretch about two hours were lost to the application (a hook that
>   did not answer, then the process ended under a running command):
>   the campaign's cost log has the times;
> - this text was amended after that run too, from its 25 notes, and as
>   it now stands it has not been run.

**The runs on DILL (2026-11-26) and on a fifth calculus (private,
2026-11-26 to 27)** were never entered under "Status". What they showed
is in `docs/campaigns/skill-against-design-2026-11-26.md` (the four
public campaigns, question by question) and in
`docs/campaigns/collation-2026-11-27.md` (all five read together).

**The text as it stands** was amended from the collated notes on
2026-11-27 (`ada8550`), and three times since from the repairs of that
day. It has not been run by a campaign.

## The worked instances, as the skill described them

> - **the subframe tableau** for propositional lax logic, in
>   lax-logic-in-lean (`LaxLogic/PLL/SubTab/`): a calculus that was
>   designed, not adopted;
> - **Brünnler's system K**, nested sequents for the modal logic K, in
>   `calculi/BrunnlerK/` of `proof-tools`: adopted from its source
>   (Brünnler, *Nested Sequents*, arXiv:1004.1845) by a campaign under
>   this skill. Its judgments are not flat (`reference/explore.md` §13).
>   The campaign's record is in its folder `campaign/`, in the earlier
>   form: the plan, the rule table, the statements, the gates, the
>   reports, the cost log and the notes on the method;
> - **GLS**, the sequent calculus on multisets for the provability logic
>   GL, in `calculi/GLS/` of `proof-tools`: adopted by a campaign under
>   this text as rewritten, from the authors' Coq files and chapter 12 of
>   Shillito's thesis (the paper, Goré, Ramanayake and Shillito, TABLEAUX
>   2021, could not be got). Its judgments are flat. Its folder
>   `campaign/` has the record in the present form: the decisions, the
>   closing page (`report.md`), and a brief by which three goals were
>   handed to an agent;
> - **MALL**, Girard's one-sided sequent calculus for multiplicative-additive
>   linear logic, in `calculi/MALL/` of `proof-tools`: the first calculus
>   here with no weakening and no contraction (`reference/adopt.md` §3),
>   with phase semantics, two kinds of certificate against a derivation
>   (`reference/certify.md` §3), and a tutorial page in the pinned format
>   (`reference/explore.md` §11).

## Where a rule came from

Each row is a clause that stood inside a rule of the main file. The rule
stays there; the occasion is here.

| the rule, in the main file | the occasion, as the main file had it |
|---|---|
| the first act, the paper: a document whose author asks that it not be cited is read, and is not the source of record | "DILL: lecture notes marked "do not cite"" |
| the first act, the system: a fragment of the paper's system | "DILL: the figure less three rules" |
| the first act, step 4: the first message says the form of what holds, and the form rejected | "Of the seven gates of the first campaign, this was the one choice that a gate changed." |
| downloading is the reviewer's standing word | "Matthew, 2026-11-25: "permission to dowload publicly available materials such as PhD theses should be a standard part of the relevant skills"." |
| what is fetched is kept outside the repository and outside any scratch folder | "a restart of the machine cleared a session's scratch folder, with the papers and the page images in it (DILL)" |
| rule 5: look at the machine before a build | "Three agents building at once, with another session's build and an uncapped evaluation beside them, restarted the machine twice in one day (2026-11-26)." |
| rule 5: give an agent your design, and say that another is welcome | "an agent has kept the design and bettered its central definition" |
| the stops: a call refused at the moment of an interrupt is reported as "stopped" | "DILL: twelve minutes waited on a refusal that the application had made for another reason" |
| Prove, step 3: a goal with a decision procedure at hand is screened before the literature on the result is read | "the order "state, screen, prove, then read" cost nothing, and the screen did the work that a source's statement would have (MALL: the uniform interpolant)" |
| Prove, step 4: the order is a matter of what is risked | "DILL: every goal out at once, and nothing lost" |
| Prove, step 4: goals that do not rest on one another go out together | "DILL: five agents, every goal proved in 3 to 12 minutes, no file touched twice"; "DILL: the statements about the calculus with cut, from the results without cut and cut elimination as a proposition" |
| the folder: a commit is cited by its hash only once it is on the shared branch | "a push that rebases changes the hash (DILL)" |
| a round of campaigns | "one arrangement has served (2026-11-26, by the reviewer's instruction)"; "The command `prove` (`reference/certify.md` §5) went this way: four revisions in an evening." |
| what is not built | "This text was checked against `proof-tools` at commit `3fa25c0` (2026-11-22)." |

The reference files (`reference/adopt.md`, `certify.md`, `explore.md`,
`pitfalls.md`) still carry their occasions inside their rules: 44 lines
at `17acd9b`. They have not been through this pass.
