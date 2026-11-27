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

## From the reference files (second part of the pass, 2026-11-27 14:33 GMT)

The reference files went through the same pass later the same day. The
occasions taken out of their rules are listed here by rule; the clauses
themselves stand in the files at commit `fe7c1c4`. Pointers to a worked
case (a file of a calculus to read) are not history and stay: 16 lines
still name a campaign for that reason.

| file, and the rule | the occasion that stood in it |
|---|---|
| `adopt.md` §1, look at what a download link gave back | a thesis repository (DSpace 7) that gave HTTP 500 at one address and the PDF at another (GLS) |
| `adopt.md` §1, read a figure as an image | `pdftotext` dropped `□` and `⊠` from one source, and its modal rule read as a rule with no modality (GLS) |
| `adopt.md` §1, the script for a paper's skeleton | its header said it simulated LaTeX's counters, and that text was old |
| `adopt.md` §2, a second proof of cut from soundness and completeness | "DILL had it before the syntactic proof, and joined those goals from it at once" |
| `adopt.md` §3, two signs that cannot be signs of a judgment | "DILL took `⨾`" |
| `adopt.md` §3, the figure's letters stay | a draft of K that called the node `Δ`, so that the figure's `Δ` became `Λ` |
| `adopt.md` §5, a goal that is a type of functions | a cold reader's remark on `Decidable`: "inhabited with no proof search at all" (DILL) |
| `adopt.md` §6, sources of `Classical.choice`; functions on derivations | the tags "(MALL)" and "(DILL)" |
| `certify.md` §3, level 3 as a function into subtypes | "GLS: `2ⁿ` by its type, cut off at 28 nested boxes"; "GLS ran an unproved search in front of an exponential proved one for two days, and the proof took an hour once the invariant was seen" |
| `certify.md` §3, a model evaluated; a saturated set | an evaluator by closures that did not end in 120 s on four elements (MALL); "DILL: 250 lines, no semantics"; "65 536 against 1" in the fifth campaign |
| `certify.md` §4, the direct decision | K's figures: 0.44 s against 1.81 s at a tree of 655 moves; 0.07 s against 2.04 s at 65 nodes. The sentence called K "the one instance measured", which GLS, MALL and DILL had since made untrue |
| `certify.md` §4, generators of inputs; a second search | a generator that wrote oversized files for minutes; a helper that called itself twice on each element |
| `certify.md` §5, the command `prove` | "Four instances here, all of 2026-11-26"; the notes it was revised from (K 72 to 80, GLS 27, MALL 29, DILL 22, and the fifth's) |
| `certify.md` §5, what is printed | "MALL: nine formulas, a letter numbered 92, refused without the options"; "K: 86 MB for a tree of 2 335 moves, 82 MB of it spaces; the command took 13.7 s to print what the search found in 19 ms" |
| `certify.md` §5, one kernel check, several facts | "41 s against 20 s on one set, DILL"; "3.6 s each at 76 sequents, beside the kernel's 1.4 s; an earlier wording here blamed the kernel" |
| `certify.md` §5, the program's own check | the two faults measured in GLS on 2026-11-27 (18.6 s at 30 worlds compiled against 0.1 s in the kernel; 1.3 s and 2.2 GB at 24 nested boxes; the kernel 10 s at 16 on a second family), and that GLS's repair took three forms |
| `certify.md` §5, a check the kernel cannot run | "MALL: a set of 119 sequents, 8 GB; DILL: a set of 200 in 16 s and 5.7 GB, a tree at a chain of 96 not settled"; "at 68 sequents, 166 326 comparisons of formulas for 386 questions"; "MALL: stopped at 119 sequents before, 1 003 in 3.6 s after, 11 110 in parts"; "three forms were tried in each of the three campaigns" |
| `certify.md` §5, a certificate beyond the kernel | MALL's 238 sequents stopped at 8 GB, and 124 checked on one family where 119 were not on another; K's file of 1.9 MB refused where a larger was checked; the fifth's trees of 257 and 385 moves |
| `certify.md` §5, measuring | "DILL: a chain taken to 96 formulas, one capped case at a time, with the rest of the campaign queued behind it"; two runs with a deadline and no cap among the likely causes of a restart of the machine (DILL, 2026-11-26) |
| `certify.md` §5, a certificate as a term | K's trees of 2 335 moves and of 258 moves nested 256 deep, not elaborated; then elaborated in 17 s and 13 s with both options (K, 2026-11-26) |
| `explore.md` §1, the layout under `calculi/` | built first as `examples/Probe/` at the library's commit `3fa25c0`: 39 jobs, under a minute |
| `explore.md` §1, a host project | Lake reporting `LeanCertify.Certifier` out of date with both packages in the workspace (the fifth) |
| `explore.md` §2, a move's name; a right rule's move | "a line `mallmove with p q` does not parse"; the tag "(DILL)" |
| `explore.md` §5, the tactic's name; `within` | in the fifth's host project a field `over` was a keyword and `![…]` a vector; in K `within` "was one line" |
| `explore.md` §11, the tutorial page | "GLS has one"; "added 2026-11-26"; "DILL: 112 links at a commit no longer on the branch"; a finding about the library of 2026-11-26 on a status REFUTED |
| `explore.md` §13, S2 for nested judgments | "forty [lines], in the instance above" (K) |
| `pitfalls.md` 11, an estimate written as a fact | one campaign typed three such values after the entry was written (MALL); "DILL: five times ahead of the clock in one campaign" |
