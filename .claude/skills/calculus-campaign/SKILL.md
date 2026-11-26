---
name: calculus-campaign
description: Take a proof calculus from its paper to mechanised use in Lean 4 with the proof-tools libraries, as one campaign of five stages - survey the source, transcribe the rules and test the transcription with a first proof explorer, prove what the literature proves about the calculus (statements first), run proof search and countermodel procedures whose answers the kernel checks, and finish the explorer. Started by the command /calculus-campaign followed by the calculus, named in words. Use when asked to adopt, formalise, port or mechanise a calculus (sequent, nested sequent, tableau, natural deduction, labelled, refutation) from a paper or a book; to make a calculus that is already in Lean explorable a move at a time (`apply_move`, scripts, `#walk`); to certify its proof search or its countermodels; or to resume such a campaign from its folder or from a brief.
argument-hint: "[the calculus, named in words | the path of a stage's brief]"
---

# One calculus, from its paper to use: the campaign

## The command

    /calculus-campaign <the calculus, named in words>

What was typed after the command's name is put here by Claude Code:

> $ARGUMENTS

- **It names a calculus** (as in `/calculus-campaign Gentzen's LJ`): that
  is the **target** of a new campaign. Read this file to the end; then
  do the first act and go on to the Survey. The campaign runs from the
  command to its closing page without waiting for the reviewer.
- **It names a brief** (`brief-<stage number>-<k>.md`) **or a campaign
  folder**: a campaign in progress. Read this file from "The method" on,
  then the brief (in a folder: `README.md`, then the latest brief), and go
  on as it says.
- **Nothing is there, or the placeholder itself is** (a dollar sign and
  the word ARGUMENTS: this file was opened as a file, not run as a
  command). Look for a line beginning `ARGUMENTS:` at the very end of this
  text, then in the request that brought you here, and treat what you find
  as one of the two cases above. If you find nothing, ask which calculus
  is meant, and wait for the answer: this is a stop ("Deciding, checking,
  stopping", 3).

The files this text calls `reference/…` and `templates/…` are beside it,
in the skill's folder: `${CLAUDE_SKILL_DIR}` (if that shows as a name in
braces, it is the folder this file is in).

## The first act: the target

The **reviewer** is the person who typed the command, unless they name
another; you are the **operator**. The target is a name in words. It does
not yet say which paper, which of the paper's systems, or what is to be
proved. You decide those, by the defaults below, write the decision
down, tell the reviewer in one short message what was decided, and go
on. You do not wait for an answer. The reviewer may give one at any
time, and it holds from when it comes ("Deciding, checking, stopping",
4).

1. **Is a campaign on this calculus already begun?** A campaign is a
   folder `campaign/` whose `decisions.md` opens with an entry "the
   target" (in a campaign begun before 2026-11-25 the file is
   `gates.md`). Look for one that names this calculus under the
   directory you were started in. One that exists is resumed (the second
   case above), not begun again. One that is closed (it has a closing
   page, or a closing report) is not run again: a request that names it
   asks for further work on it, which is recorded as a new entry and
   done under this text. One begun under `gates.md` keeps its files as
   they are: go on under this text, record new choices in a
   `decisions.md` beside it, and decide what its unanswered gates left
   open.
2. **Find the candidates**: the papers where the calculus is defined, and
   their versions (conference, journal, thesis, preprint); the systems
   each defines (a paper often has several: with and without cut, a base
   system and its extensions, a variant for proof search); the results
   each claims for them. Read no further than abstracts, introductions
   and the lists of theorems and figures: this is not the Survey. Nothing
   is decided from memory alone: each candidate and each result has a
   place you can cite. A source you cannot get is not the target: take
   the best one you can get, and say which you could not.
3. **Decide the target.** Each part has a default:
   - **the paper, and the version to be read**: the most complete
     version you can get (a journal version or a thesis before a
     conference paper; the latest revision of a preprint). The other
     candidates get a line each, with why not;
   - **the system**: the one the command's words name, under the paper's
     own name for it. Where they fit several, the base system: without
     the extensions, and in the form the source proves its theorems
     for. An extension is a campaign of its own (pitfall 2). Say what is
     left out;
   - **the results aimed at**: the entries of the standing list that the
     literature appears to have for this system, and anything else the
     request mentions. This is the aim; the Survey makes it exact;
   - **the path**: adopted from the paper, which is what this file
     describes; or, if you found the calculus already in Lean, or it has
     no source, one of the "Two shorter paths";
   - **the place**, and a short name `<Calculus>` fit to be a Lean
     module name: the folder `calculi/<Calculus>/` of the library
     `proof-tools`, with core Lean only. A calculus has a repository of
     its own only if the reviewer has said so; the directory you were
     started in is not one by default;
   - **the library**: the checkout you were started in, where it is one
     of `proof-tools`; otherwise clone
     `https://github.com/fairflow/proof-tools` and use a commit that has
     the files `ProofTools/Explore/Cert.lean` and
     `ProofTools/Explore/Session.lean`. In a checkout, compare the
     commit you are on with the remote's `main`
     (`git ls-remote origin refs/heads/main`, which writes nothing): a
     session's folder is often cut from a local `main` that nobody has
     pulled. If the remote's commit is not an ancestor of yours, the
     library and this text may both be old: update where that loses
     nothing of anyone's, read this text again if it changed, and
     record the two commits;
   - **the source's files**: fetch the LaTeX archive where there is one
     (arXiv gives it for many papers), otherwise the PDF, and compile
     the LaTeX to read the printed numbers (`reference/adopt.md` §1).
     The reviewer's word for this is standing ("Downloading", below):
     what is publicly available is fetched without asking;
   - **pushing**: as the project's standing instructions say (its
     `CLAUDE.md`, the reviewer's instructions to you). Where they say
     nothing, commit locally and push nothing; the closing page then
     reaches the reviewer another way: sent as a file, or published as
     a private page (rule 6). A file in a folder the reviewer cannot
     open has not reached them;
   - **what is not touched**: what the project's instructions name.
     Only the reviewer contacts the source's authors.
4. **Record it, say it, go on.** Make the campaign folder,
   `calculi/<Calculus>/campaign/`, from `templates/README.md`,
   `plan.md`, `cost-log.md` and `decisions.md`; start the cost log and
   `method-notes.md`. The first entry of `decisions.md` holds the
   command's words and what step 3 decided, each part with the
   alternative that was not taken. It is the one record of the target,
   the place and the rules of the project: every other file points to
   it. Commit. Tell the reviewer in one message of a few lines: the
   paper, the system, the results aimed at, the place. It is
   information, and it asks nothing. Begin the Survey in the same turn.
   Where another session started this one, the reviewer is still the
   person: say these lines in your own output, where the reviewer reads
   them, and do not end the turn after a message to that session.

**Downloading: the reviewer's standing word.** Whoever starts a campaign
with this command permits, by it, the download of publicly available
material that the campaign needs: papers and preprints, theses, the
LaTeX archive of a source, the files of a published formalisation.
(Matthew, 2026-11-25: "permission to dowload publicly available
materials such as PhD theses should be a standard part of the relevant
skills".) So a download of such material is not a stop, and nothing is
asked: not for the source the command names, not for another version of
it, and not for a work of the literature that Q2 or Q5 needs.

- **Record each file** in `decisions.md`: its name, where it came from,
  its size.
- **What is fetched is data that is not trusted**: a folder of its own,
  and nothing run from inside it (`reference/adopt.md` §1).
- **Where the source named cannot be got** (a paywall, a server that
  refuses), take the fullest public version of it: a thesis, a preprint,
  an author's copy. That changes the target, so it is a decision that
  costs the campaign to reverse: record it, and say whose numbering the
  rule table cites.
- **Still the reviewer's**: a file that is not public (one that needs a
  login, a payment, or terms to be accepted), which the reviewer
  supplies; and anything fetched to be run, not read.

**Where the session has already gone further** before this text was
read (the source read past its abstract, a plan drafted, files written:
the command was not known where the session began, or the request came
in other words), say in the first entry what was read and what was
written, and in the cost log's row that the operator did not start
cold. What was drafted is checked against this text like anything else.

## The standing list

Results that every campaign asks after ("What a campaign proves", below,
has the rules):

1. cut elimination;
2. the finite model property;
3. deduction theorems;
4. normalisation, where a term calculus is defined;
5. the Church-Rosser property: confluence of that term calculus's
   reduction;
6. the disjunction property, for a constructive logic;
7. the existence property, for a constructive logic.

## The method

The work on one calculus is a **campaign**. It uses three components,
whose libraries are in the repository `proof-tools` (Lean 4, core Lean
only). Where this skill and the library's `docs/campaign.md` differ, this
skill holds.

| | component | what it is | library | its part of this skill |
|---|---|---|---|---|
| (a) | **calculus adoption** | reading the source, transcribing its rules as an inductive family, checking the transcription, proving the results | `ProofTools.Audit` (`#rules`, `#slime`, the bounds on axioms) | `reference/adopt.md` |
| (b) | **lean-certify** | a checker proved sound, an untrusted producer, the kernel checking each answer | `LeanCertify` | `reference/certify.md`; the authority is the skill `lean-certify` (`SKILL.md` at the root of proof-tools) |
| (c) | **the proof explorer** | derivations and unfinished derivations as data: built a move at a time, by script or by program, looked at, and mapped out to the calculus's own derivations | `ProofTools.Explore`, on `ProofTools.Zipper` | `reference/explore.md`. The library's guide, `docs/explore.md`, is the reference for what the library proves: consult it; no stage asks you to read it whole |

**The operator runs the campaign, from the command to the closing page,
without waiting for anyone.** It makes the choices, records each one
where it can be reversed, and runs the checks that stand in for a second
reader ("Deciding, checking, stopping"). The reviewer owns what leaves
the project (contact with the source's authors, publication to anyone
but the reviewer, pushing to a place not agreed), and may redirect the
campaign at any time, in a word. The reviewer is not asked to read
proofs, and is not asked to approve steps: the campaign ends with one
page, which says what to read and what was decided. What a result may be relied on for is settled by
the kernel, by the checks the operator ran, and by that page being short
enough to read.

Read a part when a stage sends you to it, and the stage's entries of
`reference/pitfalls.md` with it; its entries under "Every record",
before the first document is written. Compiled Lean to read beside the parts:

- **the templates** `templates/Instance.lean.txt` and `Play.lean.txt`:
  the files of an instance, compiled for the library's example calculus;
- **the library's example**, in `ProofToolsTest/Explore/` of
  `proof-tools`: `Calculus.lean` (an intuitionistic sequent calculus of
  nine moves, with what holds taken as validity), `MapOut.lean` (the same
  calculus as an inductive family), and their tests.

**The worked instances** are not needed to follow this skill. There are
four outside the library's tests:

- **the subframe tableau** for propositional lax logic, in
  [lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
  (`LaxLogic/PLL/SubTab/`): a calculus that was designed, not adopted;
- **Brünnler's system K**, nested sequents for the modal logic K, in
  `calculi/BrunnlerK/` of `proof-tools`: adopted from its source
  (Brünnler, *Nested Sequents*, arXiv:1004.1845) by a campaign under
  this skill. Its judgments are not flat (`reference/explore.md` §13).
  The campaign's record is in its folder `campaign/`, in the earlier
  form: the plan, the rule table, the statements, the gates, the
  reports, the cost log and the notes on the method;
- **GLS**, the sequent calculus on multisets for the provability logic
  GL, in `calculi/GLS/` of `proof-tools`: adopted by a campaign under
  this text as rewritten, from the authors' Coq files and chapter 12 of
  Shillito's thesis (the paper, Goré, Ramanayake and Shillito, TABLEAUX
  2021, could not be got). Its judgments are flat. Its folder
  `campaign/` has the record in the present form: the decisions, the
  closing page (`report.md`), and a brief by which three goals were
  handed to an agent;
- **MALL**, Girard's one-sided sequent calculus for multiplicative-additive
  linear logic, in `calculi/MALL/` of `proof-tools`: the first calculus
  here with no weakening and no contraction (`reference/adopt.md` §3),
  with phase semantics, two kinds of certificate against a derivation
  (`reference/certify.md` §3), and a tutorial page in the pinned format
  (`reference/explore.md` §11).

**Status.** The three parts have been used separately. The whole, from a
paper to an explorer, has been run once: on Brünnler's system K, on
2026-11-23, by an operator that is a language model, under an earlier
text in which the reviewer passed a gate before each step. That run's
record (its cost log) shows: of seven gates one changed the work, the
plan's; no error was found at a gate, each was found by a tool, a test
or a screen that the operator ran; the reviewer lifted every gate in the
middle of Prove; and most of the day was spent waiting.

This text was rewritten on 2026-11-25 so that the operator works
independently, and has been run once as rewritten: on GLS, the same
day, by an operator that started cold. What that run shows, and what it
does not:

- the five stages ran in 71 minutes, with one question to the reviewer
  (a download, since made the reviewer's standing word), which the work
  did not wait on; every goal ended PROVED;
- the session then ended under a running command and stood idle for
  three hours, until the reviewer typed in it; the closing page was
  written after that. So a run from the command to the closing page
  with no word of the reviewer has not yet been made;
- the second transcription and the reading back were carried out as
  written (`reference/adopt.md` §7), and found no fault. No other check
  found one either, so what they can catch is not known;
- rule 1 was not kept to the letter: the rules were transcribed from
  the authors' formalisation before any prose could be read, and were
  compared with the prose afterwards;
- this text was amended after that run, from its notes.

It was run a second time as rewritten on 2026-11-26, on MALL, by an
operator that another session started from a brief. What that run
shows:

- the five stages ran in 81 minutes (09:45 to 11:06 GMT), the closing
  page delivered, with no word of the reviewer between the start and
  the page: 12 goals PROVED, weakening and contraction REFUTED as the
  source says, none OPEN. Five agents were started by the operator;
- the second transcription and the reading back again found no fault;
  the reading back found the instances that refute weakening and
  contraction, unprompted;
- three pinned values were typed from expectation, each wrong, each
  refused by the build (`reference/pitfalls.md`, 11);
- after the page, at the reviewer's word, a complete certificate
  against a derivation and the tutorial page were added. In that
  stretch about two hours were lost to the application (a hook that
  did not answer, then the process ended under a running command):
  the campaign's cost log has the times;
- this text was amended after that run too, from its 25 notes, and as
  it now stands it has not been run.

Where this text leaves you without an instruction, decide, and write it
down (rules 8 and 9).

## Nine rules for every stage

1. **Read the source at source.** A rule table comes from the paper, not
   from a summary, a survey, memory, or an example in this skill. The
   prose carries side conditions that the figure does not. A
   formalisation that the authors published with the paper is part of
   the source: it is read beside the figure, and not in place of the
   prose (`reference/adopt.md` §1).
2. **Statements before proofs.** A definition, a rule table or a statement
   is written down, displayed in its document and screened before
   anything is built on it. Nobody is waited for: the order is yours to
   keep.
3. **PROVED, REFUTED, OPEN.** PROVED means the kernel has checked it, with
   no `sorry`, within the axioms its file allows. Anything else that is
   not refuted is OPEN. A refuted statement is kept, with its countermodel.
4. **Ask the tool; do not rebuild it.** Whether a rule matches the figure:
   `#rules`. Whether an index of a conclusion is computed: `#slime`. Where
   an axiom enters: `#choice_path`. A paper's item numbers: compile it and
   read the `.aux`. And read your own check's output: one that counts the
   wrong thing reports success.
5. **Sessions are yours to arrange.** A long session pays to read its own
   history again at every step. When that cost shows, hand the next
   stage to a fresh agent that you start yourself, with a written brief
   (`templates/brief.md`), and take its result back. This needs no word
   of the reviewer. To hand goals on, a brief that gives the statements
   as named Lean types, and the tests the result must pass, is enough.
   Name in it the files the agent will write; an agent of the campaign
   works in your tree, so leave those files out of your commits until
   it reports; and build and run its result yourself before anything is
   recorded as PROVED. The lakefile's glob builds every file of the
   folder, an agent's half-written one included: until the agents have
   reported, build by target (`lake build <Calc>.Results`), and tell
   each agent to do the same. The machine is one: before a build, look
   at what is running and at the free memory (the reviewer's global
   instructions have the one line for it, and the gates). Agents may
   build side by side while the machine has room: this is not a
   one-at-a-time rule. Hold a build back when memory is short, swap is
   in use, or several builds are already running; and never run an
   open-ended search beside a large build. Three agents building at
   once, with another session's build and an uncapped evaluation
   beside them, restarted the machine twice in one day (2026-11-26).
   Say this in each brief, and run any evaluation of unknown size under
   `lean -M <megabytes>`. Give an agent your design where you have
   one, and say that another is welcome: an agent has kept the design
   and bettered its central definition. End a session before the campaign is done only
   where the environment forces it: write the brief, and enter the end
   in `decisions.md` as a stop, since someone must then open a session
   with `/calculus-campaign` and the brief's path.
   The documents are the campaign's memory: a session that goes on from
   one stage to the next reads them again, and does not work from what
   it remembers of them, nor from a summary the environment made.
6. **The campaign ends when the reviewer can read its closing page**:
   pushed, sent in full, or published. A clean build is not the end, and
   a file in a temporary folder is not a page. Until then the status
   board (`README.md` of the campaign folder) is true at every commit.
   Write the page as soon as the goals are settled, before anything
   that is optional: a measurement still running is added to it
   afterwards. The goals are those of Prove and the level the plan set
   for Run. A certifier that the first measurements show to be the
   missing half of Run at that level is not optional: build it, then
   write the page. What goes beyond the plan's level is optional: the
   page first, amended afterwards.
7. **Do not change the libraries.** If an instance seems to need a change
   to `proof-tools`, do not make it, and do not stop: it is a finding
   about the library. Record it, work round it in the campaign's own
   folder, or leave the goal that needs it OPEN with the reason, and go
   on. A campaign under `calculi/` changes no tracked file outside its
   own folder. One exception: the reviewer may ask, during a campaign,
   for a change to this skill. Make it in a commit of its own that
   changes the skill's files and nothing else, record the reviewer's
   words in `decisions.md`, and say it on the closing page.
8. **The method learns.** Keep `method-notes.md` in the campaign folder:
   each place where this skill was wrong, silent or unclear, and what you
   did there. Keep it to what would change this text. The closing page
   proposes the changes.
9. **Decide, record, go on.** Where the source, the plan or this text
   leaves a choice, make it, write it in `decisions.md`, and go on. Do
   not end a turn to ask what you can decide. The few things that do
   stop a campaign are listed in "Deciding, checking, stopping", 3.

## Before anything: five questions

Asked of the literature and answered in writing, in `plan.md`, before any
Lean of the calculus. Each gives a later stage its goals.

| | question | gives the goals of |
|---|---|---|
| Q1 | **What are the rules?** The source, its version, its notation, its side conditions, where it is ambiguous or silent. | Adopt |
| Q2 | **What is proved about it?** Every entry of the standing list, and the other published results: soundness, completeness, admissible rules, decidability, complexity. | Prove |
| Q3 | **What should run, and why?** Proof search, countermodels, or both; a decision procedure, or search with a budget; who will rely on the answers. Is there a published way to get a countermodel from a failed search? | Run |
| Q4 | **How do people use it?** By hand, in teaching, inside another proof; the worked examples; the order rules are applied in. | Explore |
| Q5 | **Which calculi is it related to?** Translations in either direction; and whether it has been formalised already, in any prover. | Adopt and Prove (what to transcribe, what can be reused) |

## What a campaign proves

In the Survey every entry of the standing list gets a line in Q2 of the
plan, with one of four values and its source: the paper and the number of
the theorem, or the place where a proof is only stated.

- **Holds**, of this system.
- **Holds of the logic, proved elsewhere**: for another calculus, or for
  the logic by other means. Say where.
- **Fails.**
- **Does not apply.** A result that needs a notion the calculus does not
  have (derivability from hypotheses, terms and their reduction, a
  constructive logic) does not apply, unless the source states a form of
  it for this system.

An entry is not dropped because the paper in hand is silent on it: look
in the literature, bound the search, and say where you looked. One you
believe holds, with no source found, is reported as that.

Which results are goals of Prove:

- **A standing result that holds of this system and has a source is a
  goal by rule.** The operator does not set one aside: a goal that is
  not reached ends OPEN, with what was tried, or why it was not begun.
  The reviewer may set one aside at any time, in their own words. Where
  such a result has more than one form (that a rule is admissible; a
  procedure that removes it) or the source proves it by more than one
  route, the goal by rule is the statement the source states. The form
  and the route beyond that are decided in the plan
  (`reference/adopt.md` §2), and recorded.
- One that holds of the logic and is proved elsewhere, or that has no
  source, is a goal where a goal by rule rests on it, or where the
  plan's budget has room for it and a use the plan names wants it.
- Of the source's own theorems, soundness is a goal, and completeness
  where the source proves it.
- **Where the source has no semantics** (it is proof theory only), the
  fourth check of meaning and the "no" side of Run still want one.
  State the logic's usual semantics, from a place in the literature
  that you cite. It is a decision that costs the campaign to reverse,
  and is among the definitions to read on the closing page. Soundness
  and completeness for it are then goals, of the kind "holds of the
  logic, proved elsewhere".
- The source's other theorems, and other important technical results
  found in the literature, are listed in the plan, each with its size
  as far as you can tell it. Which are goals is decided there: first
  those a goal rests on, then those that what the calculus is wanted
  for (Q3, Q4) asks for, within the budget. The rest are listed as not
  goals, with the reason.

Each goal is stated in Lean, displayed in `statements.md` and screened
before it is proved (rule 2), and ends PROVED or OPEN. A statement of it
that is refuted on the way is kept as REFUTED, and replaced (rule 3).

## The five stages

| | stage | the work | components | the checks, run by the operator before anything rests on the work | kept |
|---|---|---|---|---|---|
| 0 | **Survey** | the first act; the five questions, from the sources | (a); Q3 and Q4 look ahead to (b) and (c) | scratch screens of the encoding and of what "holds" will mean; the plan's choices recorded as decisions, before any Lean of the calculus | `plan.md` |
| 1 | **Adopt** | the rules as an inductive family; a first explorer instance | (a), (c) | `#rules` beside the source's figure; **a second transcription** by a cold reader; the source's own derivations, as terms of the family and run through the explorer | `rule-table.md`; the exercises file |
| 2 | **Prove** | the plan's goals, the source's soundness theorem first | (a) | each definition and statement displayed, screened, and **read back** by a cold reader, before its proof; soundness and completeness before the other goals | `statements.md`; in each theory file its bound on axioms |
| 3 | **Run** | search and countermodel procedures, each an untrusted producer whose output a checker certifies | (b), (c) | `Holds`, the certificate and each soundness statement displayed before they are proved; a negative test of each certifier | the procedures, the corpus, the project's settings for `lean-certify` |
| 4 | **Explore** | the explorer in full | (c) | every line of the tutorial elaborated, what it shows pinned in the tests; the pins of the tutorial page hold | the tutorial, the tutorial page with its exercises, a user's guide, the closing page |

After stage 1 the order is not fixed: a countermodel found in Run screens a
statement of Prove; a derivation found by hand in the explorer is the
proof that Prove then formalises; a termination theorem of Prove licenses
a producer of Run.

**The explorer appears twice on purpose.** The first instance, in Adopt,
is a probe: a rule that does not behave as the source says shows itself
when it is applied. Run the source's own derivations through it, and try
what the source's prose says cannot be done. The exercises file is also
the reviewer's way in, at any time they choose: what the reviewer tries
and reports is recorded in `decisions.md`, and is input of stage 4.

### Deciding, checking, stopping

1. **Decide, record, go on.** Each choice gets an entry in
   `decisions.md` (`templates/decisions.md`): the date; what was
   decided; the alternatives; why; what rests on it; and what it would
   cost to reverse:
   - *little*: a name, a letter, the place of a file;
   - *a stage*: the form of a goal, an encoding, which results are
     goals;
   - *the campaign*: the source, the system, what "holds" means, the
     axiom policy.

   Take care in proportion. What "holds" means is screened before it
   is fixed (stage 0, step 3); the source and the system are fixed at
   the first act, by its defaults. The closing page lists the
   decisions, the costliest first, so that the reviewer reads the few
   that matter and can reverse any of them.
2. **Run the checks of meaning.** No tool checks that a definition says
   what the source means ("What is trusted"). Four checks give evidence
   of it, and the operator runs all four:
   - **the tools, on the transcription**: `#rules` beside the figure,
     and `#slime` (stage 1, steps 3 and 4);
   - **the source's own worked derivations**: as terms of the family
     (stage 1, step 4), and as scripts of the explorer (steps 7 and 8);
   - **a second reading by a cold reader** (`reference/adopt.md` §7):
     for the rule table, a second transcription made from the source
     alone; for the definitions and the statements, a reading back into
     ordinary notation made from the Lean alone. The transcription is
     compared with what `#rules` prints for your family, the reading
     back with the source's items; every difference is settled from
     the source;
   - **soundness and completeness, proved first** (stage 2, step 4).
     Against a semantics that is stated without the rules, they fix the
     set of derivable judgments. They do not fix each rule: a result
     about this particular system (cut elimination, a rule admissible, a
     bound on depth) still rests on the comparison rule by rule.

   A check that finds a fault: repair it, run the check again, and
   enter the fault: under "Errors of transcription" in `rule-table.md`
   where it is in a rule; in the entry of `statements.md` where it is in
   another definition or in a statement. A check that was not run is
   named on the closing page as not run.
3. **The stops.** End a turn to wait for the reviewer only for:
   - what only the reviewer may do or allow: contact with anyone outside
     (the source's authors above all); publication to anyone but the
     reviewer (a private page that carries the closing page to the
     reviewer is delivery, and no stop); pushing to a place that is not
     agreed; an act your environment will not make without their word.
     A download of public material is not one: the first act has the
     reviewer's standing word for it ("Downloading");
   - an act that destroys something or cannot be undone, outside the
     campaign's own folder;
   - no source that can be got, or a command that no calculus fits.

   At a stop, ask the one thing, and go on meanwhile with whatever does
   not rest on the answer. Nothing else is a stop. A statement refuted
   is entered REFUTED and replaced. A divergence from the source is
   logged. A need of the library is a finding (rule 7). A budget reached
   closes the stage with what is OPEN. Doubt about a choice is a line in
   its entry of `decisions.md`.
4. **A word of the reviewer holds from when it comes.** Record it in
   `decisions.md` with the words copied, not summarised, and in the cost
   log. Apply it; say what it changes of what is already built; rebuild
   that. A command overrides any decision of the operator. A question
   is answered, and is not a reason to wait.
5. **A supervised campaign.** Where the reviewer asks to pass a thing
   themselves ("put the rule table to me", "I will sign the statements",
   "supervised"), that thing becomes a gate, and only that thing. Send
   it where the reviewer can read it, with the one question. Build
   nothing that rests on it until the answer; go on meanwhile with what
   does not (what rests on things already passed, the screening of the
   thing that waits, the documents). Record the answer with the
   reviewer's words. An answer may settle a part only: do what it
   settled, and ask again for the rest. A later command that cannot be
   carried out without passing the gate is the answer to it.

### Stage 0, Survey

Read `reference/adopt.md` §1 to §3, and the Survey's pitfalls.

1. Get the source and read it: the figure, the prose around it, the
   appendix. List its numbered results in `skeleton.md`
   (`reference/adopt.md` §1 says how).
2. Answer the five questions in `plan.md`; in Q2, every entry of the
   standing list. Then the rest of the template. Three of its sections
   need a part read first: the choices of encoding,
   `reference/explore.md` §2 and §13; what "holds" will mean, "What is
   trusted" below; the level aimed at, `reference/certify.md` §3.
3. A few lines of Lean to find out whether an encoding is feasible may
   be tried now, in a scratch file outside the campaign's folder that is
   not kept: what `deriving` gives (`DecidableEq`, `Repr`,
   `Lean.ToExpr`) for **every type the plan names**, not for the
   judgments alone: the formulas, the judgments, the moves, and the
   types of models and of certificates that Q3 proposes. A type fixed
   in the plan and found awkward in Prove costs a construction: a
   type that holds a list of itself gets no `DecidableEq`, and a model
   built on its members then cannot test them for equality. Say in the
   plan what was tried and what Lean answered, type by type.

   **A statement the plan proposes is screened now too**, in the same
   way. Where the plan fixes what a word of the goals will mean in Lean
   (what "valid" is; the form of a standing result) and a small case
   could show the form to be wrong, write the fragment the screen needs
   (formulas, a model, truth in it) in a scratch file, outside the
   campaign's folder and not kept, and say in the plan what was
   screened, with what, and what it showed. What "valid" means costs
   the campaign to reverse: a form of it refuted after Prove has begun
   is every theorem stated again. The form of one goal costs a stage.

   Nothing else of the calculus is written in Lean before the plan is:
   its choices come first because they are the costly ones.
4. Enter the plan's choices in `decisions.md`, each with its cost to
   reverse: which results are goals ("What a campaign proves"), what
   "holds" means, the encoding, the axiom policy. Commit, bring the
   status board up to date, and go on to Adopt.

### Stage 1, Adopt

Read `reference/adopt.md` §3, §4 and §7; `reference/explore.md` §1 to §10 and
§12, and §13 where judgments are not flat; the two Lean templates; Adopt's
pitfalls.

1. Set the project up (`reference/explore.md` §1), and build it empty.
2. Formulas and judgments as data.
3. The calculus as the source states it: one indexed inductive family, one
   constructor for each primitive rule. Run `#rules` and `#slime` on it.
4. Fill `rule-table.md`: each rule of the figure, the output of `#rules`
   for its constructor, every divergence; where judgments are not flat,
   the template's three further sections (`reference/adopt.md` §4).
   Start `statements.md`. Then check the transcription, before anything
   follows its rules:
   - on the source's own worked derivations: each written as a term of
     the family, with its constructors, and cited in the table. They
     go in a test module of their own that imports the theory file
     only: the tests of step 7 import the tactic, which does not exist
     yet. Where the source draws none for the fragment, take
     derivations of what it asserts: the simplest instances of its
     theorems, the axioms of the logic, an equation of its semantics
     read as a sequent (`reference/explore.md` §10), each cited by page;
   - by a second transcription (`reference/adopt.md` §7): made by a
     cold reader from the source alone, compared with yours row by
     row, the comparison entered in the table.

   Settle every difference from the source before step 5.
5. The proof system: `Move`, `step`, and the soundness of the moves for
   the family (`reference/explore.md` §2 to §4). Fill the table's column
   for the moves.
6. What the editor needs, the tactic, and how a goal is shown
   (`reference/explore.md` §5).
7. Tests, every message pinned (the list is `reference/explore.md` §10).
8. The exercises file (`templates/Play.lean.txt`). Check that it
   elaborates. Every exercise is also run in the tests, by script, with
   its outcome pinned: the file is for a person who wants to try the
   calculus, and the tests are the check.
9. Bring the status board up to date, and go on to Prove.

### Stage 2, Prove

Read `reference/adopt.md` §2, §5, §6 and §7, and Prove's pitfalls.

1. Where a goal is about a semantics: the models and the forcing relation,
   as definitions in a theory file of their own. Likewise a term calculus,
   where a goal is about one: its terms, its typing and its reduction are
   a further transcription, with a rule table of its own, checked as
   the first is.
2. `statements.md`: each goal of the plan as a Lean statement, displayed,
   OPEN, before any proof. The Lean file of named statements
   (`def Name : Prop := …`, or a named type) is where a statement is
   displayed first; its entry in `statements.md` is written with it.
3. Screen each statement for counterexamples before deciding how to prove
   it (`reference/adopt.md` §5), and have the definitions the goals are
   about, and the goals' statements, read back by a cold reader
   (`reference/adopt.md` §7 says which, and how). A cold reader takes
   minutes: the proofs may begin while the reading back runs, and what
   rests on a statement that it faults is then built again.
4. **Soundness, then completeness where it is a goal, before every other
   goal.** "Soundness" here is the source's theorem (what is derivable
   is valid), not the soundness of the moves of Adopt, which says only
   that the moves follow the rules. Completeness against a rule table
   that allows too much is nearly free; the content is in soundness.
   Together they are the fourth check of meaning ("Deciding, checking,
   stopping", 2): a rule transcribed wrongly, so that it changes what
   is derivable, fails one of them. Then the goals in the plan's order,
   a goal after those it rests on.

   **That order is the source's route, and the proofs may take
   another.** A lemma that the encoding gives and the source lacks can
   make the source's lemmas on the way unnecessary: the theorem they
   led to is then proved without them. Goals that fall off the route
   are still goals. Decide of each whether it is proved for its own
   sake: yes where another goal or a use the plan names wants it, and
   the budget has room. Otherwise it ends OPEN, entered as "not on the
   route taken, not attempted". The operator does not set a goal aside.
5. Each theory file ends with its bound on axioms.
6. Bring `statements.md` and the status board up to date: each statement
   PROVED, REFUTED or OPEN, with its axioms. The stage ends when every
   goal is PROVED, or is OPEN with what was tried: the route, where it
   stopped (as a named hypothesis, where there is one), and what the
   screening showed; or when the plan's budget is reached.

### Stage 3, Run

Read `reference/certify.md` and the skill `lean-certify`: the file
`SKILL.md` at the root of the `proof-tools` checkout you work in. Read
that file. Do not load, in its place, a skill of that name from your
session's list: a session may offer a copy from another repository,
which can be older. Where the two differ, the file in the checkout
holds; a copy that says its reviewer "is the gate" is the older text.

1. Decide the producers, and any certificate beyond those of the plan
   (the tree of moves or the script, and the model), and record why
   each is wanted. For each certifier of your own (the library's were
   fixed with the plan), enter `Holds`, the certificate and the type of
   its soundness theorem in `statements.md`, displayed and screened,
   before it is proved (rule R10 of `lean-certify`: statements first).
   They have no item of the source, and are not read back.
2. Follow `lean-certify`'s six steps; `reference/certify.md` says what the
   explorer library gives for a calculus, and what is written by hand.
3. A negative test for each certifier; the corpus; timings; kernel time
   against certificate size. Commit before a measuring run, and give
   every run a deadline of its own: a session can end under a long
   command, and whoever goes on has only what is in the folder.
4. **A fault of a search that the measurements show** (a proof many
   times longer than one made by hand; time that goes where it need
   not) may be repaired in this stage, in the module of Prove where the
   search is. The repair changes no statement: afterwards every theory
   file is within its bound, and every proof and every pinned test is
   as it was, or builds again unchanged. One that would change a
   statement is not a repair: it is a new statement, entered and
   screened like any other. The repair is recorded in `decisions.md`,
   and `measurements.md` says of each figure whether it was measured
   before the repair or after.
5. Write `measurements.md` in the campaign folder: the verdicts, the
   measurements with the machine and the date, and the frontier, named:
   the smallest inputs the procedures do not settle within their budget.
   Bring the status board up to date.

Where the source gives no route to countermodels, Run aims at level 1,
unless a goal of the plan gives a construction of models (a finite model
property) or the reviewer has asked for more. A tableau built to give
countermodels is a calculus of its own, with its own campaign.

### Stage 4, Explore

Read `reference/explore.md` §11.

1. List what Q4 asked for; what your own runs of the source's
   derivations through the first instance showed to be missing or
   awkward (stage 1, steps 7 and 8); and anything the reviewer has
   reported from the exercises file (`decisions.md`).
2. Serve each from what the library has. What it lacks is recorded as a
   finding, not built into the library (rule 7).
3. The tutorial (`Play/<Calculus>Tutorial.lean`) and the user's guide.
   Elaborate every line of the tutorial, and pin in the tests what each
   step shows: a comment that says what happens is a claim, and is
   checked like one. Then the tutorial page in Markdown (`tutorial.md`,
   beside `Play/`): every campaign writes one, with graded exercises, a
   file of them to type in, and a solution of each in the library. It
   shows no statement typed by hand: each is a pin, printed by Lean, its
   status computed, the page and the library held together by the build
   (`reference/explore.md` §11, "A tutorial page").
4. The closing page (`templates/report.md`): what the campaign adopted,
   proved and runs, what is OPEN, what to read, what was decided, and
   the changes to make to this skill and its templates, from
   `method-notes.md`. Deliver it as the first act fixed (rule 6).

## What is trusted

In the explorer a calculus is given as a **proof system** `S`: a type
`S.Judg` of judgments, a type `S.Move` of moves (a rule, named by its
data), and one function `S.step`. An **attempt** `Att S o j` is a tree of
moves with conclusion `j`; the Boolean `o` says whether open goals are
allowed, and a **derivation** `Der S j` is an attempt where they are not.

Trusted: Lean's kernel, and for each calculus **two functions, each with
one theorem** (their Lean is in `reference/explore.md` §3 and §4, and
`reference/certify.md` §3):

- the **step function**, which says whether a move applies at a judgment
  and what its premises are. Its theorem is **the soundness of the
  moves** for what holds: where a move applies, and what holds of each of
  its premises, it holds of its conclusion.
- the **check of a model**, optional, which says whether a finite model
  refutes a judgment. Its theorem: what a model refutes does not hold.

With them go things of the library, the same for every calculus and
within `[propext, Quot.sound]`: `Cert.check` and `derives` (they run
`step` over a tree of moves and along a script, and ask that no goal is
left), and the map out, `Att.mapOut` and `Der.mapOut`.

**Trusted too, and no tool checks them: the definitions the two theorems
are about.** The formulas, the judgments, the family of rules, the
semantics, what holds. A wrong definition compiles, passes every bound on
axioms and proves its theorems. This is why the four checks of meaning
are run ("Deciding, checking, stopping", 2), and why the closing page
lists these definitions, each with its file and its length, as the thing
to read.

**Not trusted:** the operator; everything an instance gives the editor
(`Explorable`: the candidates, the printers, the quoting); the tactics;
every producer (a search, a person typing, a language model, a
translation); `#walk`, `where` and every view. A wrong candidate costs a
failure and cannot become a wrong theorem. One caution: the kernel does
not read a printer, but the reviewer does. Pin the display of a goal in
the tests, and keep the source's notation.

**What holds** is a choice, made in the plan and recorded as a decision
that costs the campaign to reverse.

- *The family as transcribed*, `Fam`: the method's default when a
  calculus is adopted from a source. The theorem then says that every
  step is an instance of a rule, and no semantics is needed to trust a
  derivation. With the family into `Type` the theorem is a definition,
  and the map out carries a derivation of the explorer to a derivation of
  the family, as data.
- *Validity in a semantics*, `Valid`. Then the theorem is the soundness
  of the moves themselves, and nothing ties `step` to the transcribed
  family except what is proved separately.

## Axioms: the development's policy

Which axioms a development may use is settled in its plan, not by this
method. A propositional calculus with finite countermodels can often be
kept free of `Classical.choice`; a first-order calculus whose completeness
goes through infinite models in general cannot.

- The policy is stated once, in `plan.md`, and written into the files:
  **each theory file ends with its bound**, an upper bound; for a policy
  without `Classical.choice`, `#axioms_within_file [propext, Quot.sound]`.
  Files of code (producers, printers, tactics) carry no bound. An
  exception is a decision of its own, one declaration at a time:
  recorded with the path that `#choice_path` shows, and listed on the
  closing page (part 4) with the theorem it touches. The commands, and what to
  do when a bound fails, are in `reference/adopt.md` §6.
- **Certifiers have their own list.** `lean-certify` checks every
  `Certifier` and `Engine` against `Harness.config.axioms`, which is
  `[propext, Quot.sound]` unless the project's `Harness.config` says
  otherwise (rule R4 there). A policy that allows a certifier more says
  so in that constant, or names the exception in its `axiomExceptions`.

## The closing page, the folder, the log

**One page closes the campaign** (`templates/report.md`, kept as
`report.md`). It is the one thing the reviewer is expected to read, and
it asks nothing. Six parts:

1. what the campaign adopted, proved and runs: each goal displayed, with
   PROVED, REFUTED or OPEN, its axioms, and the commit;
2. what to read: the definitions that no tool checks, each with its file
   and its length;
3. the checks of meaning: which were run, what each found, which were
   not run;
4. the decisions, the costliest to reverse first;
5. what is the reviewer's: what only they may do; what they may try (the
   exercises, the tutorial), stated and not asked for;
6. what it cost, and the changes proposed to this skill.

Keep it to a few screens: it points at files and does not repeat them.

**No report is written at the end of a stage.** The status board is
brought up to date in the commit that ends the stage, and that is all.
Where a campaign is interrupted (a stop, a session that ends), the board
and the brief say where it stands.

**The campaign folder** holds `README.md` (the status board),
`decisions.md`, `plan.md`, `skeleton.md`, `rule-table.md`,
`statements.md`, `measurements.md`, `cost-log.md` (a row for each
session, its times from the clock; every word of the reviewer, and what
it changed), `method-notes.md`, `users-guide.md` (from stage 4) and
`report.md`; and a brief, where a session was handed on. It is written as
the work goes: a record written afterwards is a different document, and
says so at its top. Commit the Lean when a build is clean, and the
documents with it; push as the first act fixed.

## Two shorter paths

The first act's decision says which path is taken. On both,
`templates/record.md`, kept as `record.md`, stands in place of `plan.md`,
and the status board lists it. The stages that follow run as written,
less what needs a source: there is no second transcription, and the
reading back is compared with the record's own account of the rules and
of the reading of a judgment.

- **The calculus is already mechanised** (its rules and theorems exist in
  Lean). Survey is the record of what exists (`templates/record.md`),
  written as such. Adopt is the proof system and the editor's part only
  (`reference/explore.md` §2 to §5): expect it to be small, and to need no
  change to the library.
- **The calculus was designed, not adopted.** There is no source to be
  faithful to. In place of the rule table against a source, these are
  entered as statements, and screened, before their proofs: the rules,
  the reading of a
  judgment, and whatever its correctness rests on (with a search and a
  model construction: the measure of termination, and the truth lemma,
  which says that an open saturated attempt is a model).

## What is not built, so do not look for it

**Nothing turns the rules into a procedure, and nothing is meant to.** No
command reads an inductive family and produces `step`, a checker, a
search or a decision procedure. A one-step checker written by hand for
each calculus is the method's form: `step`, its soundness, the check of
a model and every producer are yours to write. `#rules` and `#slime`
print and report; they generate nothing.

What else the library lacks is said where an operator would look for it:
`reference/explore.md` §12 (the explorer), `reference/certify.md` §2 and
§5 (generators, drivers), `reference/adopt.md` §1 (the paper's skeleton).
This text was checked against `proof-tools` at commit `3fa25c0`
(2026-11-22). The library changes: at the commit you use, read the
section "Limits" of the library's guide.
