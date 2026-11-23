---
name: calculus-campaign
description: Take a proof calculus from its paper to mechanised use in Lean 4 with the proof-tools libraries, as one campaign of five stages - survey the source, transcribe the rules and test the transcription with a first proof explorer, prove what the literature proves about the calculus (statements first), run proof search and countermodel procedures whose answers the kernel checks, and finish the explorer. Started by the command /calculus-campaign followed by the calculus, named in words. Use when asked to adopt, formalise, port or mechanise a calculus (sequent, nested sequent, tableau, natural deduction, labelled, refutation) from a paper or a book; to make a calculus that is already in Lean explorable a move at a time (`apply_move`, scripts, `#walk`); to certify its proof search or its countermodels; or to plan, brief, report on or resume one stage of such a campaign.
argument-hint: "[the calculus, named in words | the path of a stage's brief]"
---

# One calculus, from its paper to use: the campaign

## The command

    /calculus-campaign <the calculus, named in words>

What was typed after the command's name is put here by Claude Code:

> $ARGUMENTS

- **It names a calculus** (as in `/calculus-campaign Gentzen's LJ`): that
  is the **target** of a new campaign. Read "The first act" and "The
  standing list" below, do the first act, and stop where it says. The
  rest of this file is for when the reviewer has answered.
- **It names a brief** (`brief-<stage number>-<k>.md`) **or a campaign
  folder**: a campaign in progress. Read this file from "The method" on,
  then the brief (in a folder: `README.md`, then the latest brief), and go
  on as it says.
- **Nothing is there, or the placeholder itself is** (a dollar sign and
  the word ARGUMENTS: this file was opened as a file, not run as a
  command). Look for a line beginning `ARGUMENTS:` at the very end of this
  text, then in the request that brought you here, and treat what you find
  as one of the two cases above. If you find nothing, ask which calculus
  is meant, and wait for the answer.

The files this text calls `reference/…` and `templates/…` are beside it,
in the skill's folder: `${CLAUDE_SKILL_DIR}` (if that shows as a name in
braces, it is the folder this file is in).

## The first act: the target, fixed with the reviewer

The **reviewer** is the person who typed the command, unless they name
another; you are the **operator**. The target is a name in words. It does
not yet say which paper, which of the paper's systems, or what is to be
proved, and you do not decide those. Nothing is written to disk before
the answer.

1. **Is a campaign on this calculus already begun?** A campaign is a
   folder `campaign/` whose `gates.md` opens with an entry "the target".
   Look for one that names this calculus under the directory you were
   started in. One that exists is resumed (the second case above), not
   begun again.
2. **Find the candidates**: the papers where the calculus is defined, and
   their versions (conference, journal, thesis, preprint); the systems
   each defines (a paper often has several: with and without cut, a base
   system and its extensions, a variant for proof search); the results
   each claims for them. Read no further than abstracts, introductions
   and the lists of theorems and figures: this is not the Survey. Nothing
   goes into the proposal from memory alone: each candidate and each
   result has a place you can cite. A source you cannot get is named in
   the proposal as one the reviewer must supply.
3. **Put one proposal to the reviewer, and stop.** One message, saying
   what is proposed and what is asked:
   - the paper, and the version to be read; the other candidates, a line
     each, with why not;
   - the system in it, under the paper's own name for it, and what is
     left out (its extensions, its variants);
   - the results aimed at: the entries of the standing list that the
     literature appears to have for this system, and anything else the
     request mentions. This is the aim; the Survey makes it exact;
   - the path: adopted from the paper, which is what this file describes;
     or, if you found the calculus already in Lean, or it has no source,
     one of the "Two shorter paths";
   - where the files go, and a short name `<Calculus>` for them, fit to be
     a Lean module name. A calculus has **a repository of its own** only
     if the reviewer says so; the directory you were started in is not one
     by default. Otherwise the default is the folder `examples/<Calculus>/`
     of the library `proof-tools`, with core Lean only;
   - asked: is there a checkout of the library, and a branch, to work in?
     The default is that you clone `https://github.com/fairflow/proof-tools`
     and use a commit that has the files `ProofTools/Explore/Cert.lean` and
     `ProofTools/Explore/Session.lean`;
   - asked: where and when to push? The default is that you commit
     locally and push nothing until the reviewer says;
   - asked: is anything not to be touched? Only the reviewer contacts the
     source's authors.
4. **When the answer has come**, read the rest of this file. Then make
   the campaign folder, `<the place>/campaign/` (by default
   `examples/<Calculus>/campaign/`), from `templates/README.md`,
   `plan.md`, `cost-log.md` and `gates.md`; start the cost log and
   `method-notes.md`. The first entry of `gates.md` holds the command's
   words, your proposal and the reviewer's answer in their words. It is
   the one record of the target, the place and the rules of the project:
   every other file points to it. Commit, and begin the Survey.

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

The reviewer owns the statements, the definitions and the rule tables,
and decides at each gate whether to go on. The reviewer reads statements
and tries things, and is not asked to read proofs. No stage is automatic:
the tools make each stage's result checkable without trusting the
operator.

Read a part when a stage sends you to it, and the stage's entries of
`reference/pitfalls.md` with it. Compiled Lean to read beside the parts:

- **the templates** `templates/Instance.lean.txt` and `Play.lean.txt`:
  the files of an instance, compiled for the library's example calculus;
- **the library's example**, in `ProofToolsTest/Explore/` of
  `proof-tools`: `Calculus.lean` (an intuitionistic sequent calculus of
  nine moves, with what holds taken as validity), `MapOut.lean` (the same
  calculus as an inductive family), and their tests.

**The worked instance** is not needed to follow this skill: the subframe
tableau for propositional lax logic, in
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
(`LaxLogic/PLL/SubTab/`), a calculus that was designed, not adopted, and
the only instance outside the library's tests.

**Status.** The three parts have been used separately. The whole, from a
paper to an explorer, has not yet been run by an operator starting cold.
Where this text leaves you without an instruction, that is a finding:
write it down (rule 8).

## Eight rules for every stage

1. **Read the source at source.** A rule table comes from the paper, not
   from a summary, a survey, memory, or an example in this skill. The
   prose carries side conditions that the figure does not.
2. **Statements before proofs.** A definition, a rule table or a statement
   goes to the reviewer before anything is built on it.
3. **PROVED, REFUTED, OPEN.** PROVED means the kernel has checked it, with
   no `sorry`, within the axioms its file allows. Anything else that is
   not refuted is OPEN. A refuted statement is kept, with its countermodel.
4. **Ask the tool; do not rebuild it.** Whether a rule matches the figure:
   `#rules`. Whether an index of a conclusion is computed: `#slime`. Where
   an axiom enters: `#choice_path`. A paper's item numbers: compile it and
   read the `.aux`. And read your own check's output: one that counts the
   wrong thing reports success.
5. **A stage starts in a fresh session, from a written brief**
   (`templates/brief.md`): a long session pays to read its own history
   again at every step. The command's session is stage 0's. A stage may
   take several sessions, and a gate inside it is the place to end one.
6. **A stage's work ends when the reviewer can read its report**: pushed,
   sent in full, or published. A clean build is not the end, and a file
   in a temporary folder is not a report.
7. **Do not change the libraries.** If an instance seems to need a change
   to `proof-tools`, stop and report it (part (iv) of the report): it is
   a finding about the library. A campaign under `examples/` changes no
   tracked file outside its own folder.
8. **The method learns.** Keep `method-notes.md` in the campaign folder:
   every place where this skill was wrong, silent or unclear, and what you
   did there. It feeds part (iv) of each report, and the closing report
   proposes the changes.

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
  goal by rule; only the reviewer can set one aside, in their own words,
  at the Survey's gate.**
- One that holds of the logic and is proved elsewhere, or that has no
  source, is a goal only if the reviewer says so there.
- Of the source's own theorems, soundness is a goal, and completeness
  where the source proves it.
- The source's other theorems, and other important technical results
  found in the literature, are proposed in the plan, each with its size
  as far as you can tell it. The reviewer says which are goals.

Each goal is stated in Lean and shown to the reviewer before it is proved
(rule 2), and ends PROVED or OPEN. A statement of it that is refuted on
the way is kept as REFUTED, and replaced (rule 3).

## The five stages

| | stage | the work | components | the gate: in front of the reviewer | kept |
|---|---|---|---|---|---|
| 0 | **Survey** | the first act; the five questions, from the sources | (a); Q3 and Q4 look ahead to (b) and (c) | the target; then the plan, with its results, before any Lean of the calculus | `plan.md` |
| 1 | **Adopt** | the rules as an inductive family; a first explorer instance | (a), (c) | the rule table beside the source's figure; then **the reviewer's test**: the source's own derivations, typed by the reviewer | `rule-table.md`; the exercises file |
| 2 | **Prove** | the plan's goals, the source's soundness theorem first | (a) | the definitions and each statement, before its proof | `statements.md`; in each theory file its bound on axioms |
| 3 | **Run** | search and countermodel procedures, each an untrusted producer whose output a checker certifies | (b), (c) | which producers and which further certificates, before they are written | the procedures, the corpus, the project's settings for `lean-certify` |
| 4 | **Explore** | the explorer in full | (c) | **the tutorial**, worked through | the tutorial, a user's guide, the retrospective |

After stage 1 the order is not fixed: a countermodel found in Run screens a
statement of Prove; a derivation found by hand in the explorer is the
proof that Prove then formalises; a termination theorem of Prove licenses
a producer of Run.

**The explorer appears twice on purpose.** The first instance, in Adopt,
is a probe: a rule that does not behave as the source says shows itself
when a person applies it. Expect the reviewer to go to what is missing,
not through the exercises in order. What was asked for and could not be
done is recorded with the gate, and is the first input of stage 4.

### How a gate is run

1. **Stop.** At a gate you build nothing that rests on the thing being
   reviewed.
2. **Send a gate note**: the thing itself where the reviewer can read it,
   and what is asked. At the end of a stage the stage's report is the
   gate note; the Survey's report goes with the plan. Commit the
   documents when a gate note is sent.
3. **Record the answer** in `gates.md` (`templates/gates.md`): the date,
   what was looked at, the reviewer's words. An answer that comes after
   your session has ended is recorded by the next session before anything
   else.
4. **A gate is passed when its record says so.** With no record it has not
   been passed, whatever was built after it. A gate that is refused is
   recorded too: change the thing, and ask again.
5. **After a gate inside a stage**, go on in the same session if the
   answer comes while it is open; otherwise write the brief
   (`brief-<stage number>-<k>.md`) and end. **After a gate that ends a
   stage**, always write the brief and end. Whoever runs the campaign
   opens the next session with `/calculus-campaign` and the brief's path.

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
3. A few lines of Lean to find out whether an encoding is feasible (does
   `deriving` work on the proposed type of judgments) may be tried now,
   in a scratch file outside the campaign's folder that is not kept: say
   in the plan what was tried and what Lean answered. Nothing else of
   the calculus is written in Lean before the plan's gate.
4. Send the plan, with the Survey's report. **Gate: the plan.** The
   reviewer passes it, and says which results are goals, as "What a
   campaign proves" lays down.

### Stage 1, Adopt

Read `reference/adopt.md` §3 and §4; `reference/explore.md` §1 to §10 and
§12, and §13 where judgments are not flat; the two Lean templates; Adopt's
pitfalls.

1. Set the project up (`reference/explore.md` §1), and build it empty.
2. Formulas and judgments as data.
3. The calculus as the source states it: one indexed inductive family, one
   constructor for each primitive rule. Run `#rules` and `#slime` on it.
4. Fill `rule-table.md`: each rule of the figure, the output of `#rules`
   for its constructor, every divergence. Start `statements.md`. **Gate:
   the rule table.** While it waits, write nothing that names the family
   or follows its rules (`Move`, `step`): the printers of formulas and
   judgments may be written.
5. The proof system: `Move`, `step`, and the soundness of the moves for
   the family (`reference/explore.md` §2 to §4). Fill the table's column
   for the moves.
6. What the editor needs, the tactic, and how a goal is shown
   (`reference/explore.md` §5).
7. Tests, every message pinned (the list is `reference/explore.md` §10).
8. The exercises file, for the reviewer (`templates/Play.lean.txt`).
   Check that it elaborates.
9. Report, saying for each exercise what should happen. **Gate: the
   reviewer's test.** The reviewer types; the operator's own typing of
   the exercises does not count.

### Stage 2, Prove

Read `reference/adopt.md` §2, §5 and §6, and Prove's pitfalls.

1. Where a goal is about a semantics: the models and the forcing relation,
   as definitions in a theory file of their own. Likewise a term calculus,
   where a goal is about one: its terms, its typing and its reduction are
   a second transcription, with a rule table of its own.
2. `statements.md`: each goal of the plan as a Lean statement, displayed,
   OPEN. **Gate: the definitions of step 1 and the statements**, sent
   together or in batches, before any proof; one entry of `gates.md` for
   each sending.
3. Screen each statement for counterexamples before deciding how to prove
   it (`reference/adopt.md` §5).
4. **Soundness before completeness.** "Soundness" here is the source's
   theorem (what is derivable is valid), not the soundness of the moves
   of Adopt, which says only that the moves follow the rules.
   Completeness against a rule table that allows too much is nearly free;
   the content is in soundness. Then the goals in the plan's order, a
   goal after those it rests on.
5. Each theory file ends with its bound on axioms.
6. Report: each statement PROVED, REFUTED or OPEN, with its axioms. The
   stage ends when every goal is PROVED, or is OPEN with what was tried:
   the route, where it stopped (as a named hypothesis, where there is
   one), and what the screening showed; or when the plan's budget is
   reached.

### Stage 3, Run

Read `reference/certify.md` and the skill `lean-certify`.

1. Propose the producers, and any certificate beyond those the plan
   signed (the tree of moves or the script, and the model), in a gate
   note, with why each is wanted. **Gate: this proposal**, with `Holds`, the
   certificate and the type of each soundness theorem (rule R10 of
   `lean-certify`).
2. Follow `lean-certify`'s six steps; `reference/certify.md` says what the
   explorer library gives for a calculus, and what is written by hand.
3. A negative test for each certifier; the corpus; timings; kernel time
   against certificate size.
4. Report: the verdicts, the measurements, and the frontier, named: the
   smallest inputs the procedures do not settle within their budget.

Where the source gives no route to countermodels, the campaign stops at
level 1 unless the reviewer asks for more. A tableau built to give
countermodels is a calculus of its own, with its own campaign.

### Stage 4, Explore

Read `reference/explore.md` §11.

1. List what Q4 asked for, and what the reviewer found missing at the
   reviewer's test (`gates.md`).
2. Serve each from what the library has. What it lacks is reported, not
   built into the library (rule 7).
3. The tutorial (`Play/<Calculus>Tutorial.lean`) and the user's guide.
   **Gate: the tutorial.**
4. The closing report. Its last part is the retrospective: what the
   campaign adopted, proved and runs, what is OPEN, and the changes to
   make to this skill and its templates, from `method-notes.md`.

## What is trusted

In the explorer a calculus is given as a **proof system** `S`: a type
`S.Judg` of judgments, a type `S.Move` of moves (a rule, named by its
data), and one function `S.step`. An **attempt** `Att S o j` is a tree of
moves with conclusion `j`; the Boolean `o` says whether open goals are
allowed, and a **derivation** `Der S j` is an attempt where they are not.

Trusted: Lean's kernel, and for each calculus **two functions, each with
one theorem** (their Lean is in `reference/explore.md` §4 and
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
axioms and proves its theorems. This is why the reviewer reads the rule
table and the statements, and why the reviewer's test is typed by a
person.

**Not trusted:** the operator; everything an instance gives the editor
(`Explorable`: the candidates, the printers, the quoting); the tactics;
every producer (a search, a person typing, a language model, a
translation); `#walk`, `where` and every view. A wrong candidate costs a
failure and cannot become a wrong theorem. One caution: the kernel does
not read a printer, but the reviewer does. Pin the display of a goal in
the tests, and keep the source's notation.

**What holds** is a choice, made in the plan and signed with it.

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
  exception is the reviewer's to grant, one declaration at a time. The
  commands, and what to do when a bound fails, are in
  `reference/adopt.md` §6.
- **Certifiers have their own list.** `lean-certify` checks every
  `Certifier` and `Engine` against `Harness.config.axioms`, which is
  `[propext, Quot.sound]` unless the project's `Harness.config` says
  otherwise (rule R4 there). A policy that allows a certifier more says
  so in that constant, or names the exception in its `axiomExceptions`.

## Reports, the folder, the log

**Every report has the same five parts** (`templates/report.md`, kept as
`report-<stage number>-<date>.md`): (i) what was done, with the commit,
and what it cost; (ii) the statements, each PROVED, REFUTED or OPEN; (iii)
what to look at or try, and what should happen; (iv) what differed, from
the plan, from the source, from this skill, and anything asked of the
library; (v) what the reviewer must decide.

**The campaign folder** holds `README.md` (a status board), `gates.md`,
`plan.md`, `skeleton.md`, `rule-table.md`, `statements.md`, `cost-log.md`
(a row for each session, its times from the clock; every exchange with
the reviewer, classed), `method-notes.md`, the briefs and the reports. It
is written as the work goes: a record written afterwards is a different
document, and says so at its top. Commit the Lean when a build is clean
and the documents when a gate note is sent; a report names its commit.

## Two shorter paths

The first act's proposal says which path is taken.

- **The calculus is already mechanised** (its rules and theorems exist in
  Lean). Survey is the record of what exists (`templates/record.md`),
  written as such. Adopt is the proof system and the editor's part only
  (`reference/explore.md` §2 to §5): expect it to be small, and to need no
  change to the library.
- **The calculus was designed, not adopted.** There is no source to be
  faithful to. In place of the rule table against a source, the reviewer
  gets, as statements before their proofs: the rules, the reading of a
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
