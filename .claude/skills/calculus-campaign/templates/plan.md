# <CALCULUS>: the plan

*Template: the Survey's deliverable. It can be read without opening any
code. **No Lean of the calculus before it is written**, beyond the
scratch screens it reports. It is read again at the start of every
stage, and changed when a decision changes, with the date. Its time is
read before it is written: run `date` first, in a call of its own, and
paste (pitfall 11).*

Written <date and time, from the clock>. The target, the place of the
files and the rules of the project: `decisions.md`, the first entry.

## The source

* The paper: authors, title, venue, year, identifier; the version fixed at the first act.
* **Which file was read**, and whether in full.
* The appendix: is there one, was it read, what is in it.
* Other sources consulted (another version, an erratum, a thesis), and
  for what.

## Q1. What are the rules?

* Formulas: <the connectives; what is primitive; normal forms>, at <place
  in the source>.
* Judgments: <one-sided or two; lists, multisets or sets; structure>, at
  <place>.
* Notation: <what the schematic letters range over; what each piece of
  the figure's notation means>, at <place>.
* The figure of rules: <figure, page>; <n> rules; which are primitive and
  which the source shows admissible.
* Side conditions stated in the prose: <each, with its place>.
* Rules against restrictions on proof search: <which lines are which>.
* **Ambiguous or silent**, with what was decided for each (a divergence
  of kind U, and an entry of `decisions.md`):

## Q2. What is proved about it?

**The standing list**: one row for each of its seven entries, in the
order of `SKILL.md`, by the rules of "What a campaign proves" there. The
value is one of: holds; holds of the logic, proved elsewhere; fails; does
not apply. The source is the paper and the number of the theorem, or the
place where a proof is only stated, or "none found" with where you
searched.

| entry | value, and why | source, and the system its theorem is about | a goal? (by rule / decided: yes, why / no, why) |
|---|---|---|---|

**The source's theorems, and further results from the literature.**
Soundness is a goal, and completeness where the source proves it. The
rest are listed, each with its size as far as it can be told (the
length of the published proof, what it rests on). Which are goals is
decided here, with the reason (`SKILL.md`, "What a campaign proves").

| result | where in the source | by which route | its size | a goal (by rule) / decided: a goal, why / decided: not a goal, why |
|---|---|---|---|---|

The kinds of result among the goals (`reference/adopt.md` §2), and what
each means for the encoding:

The semantics, if a goal needs one: <the source's definition of a model
and of truth, with its place>. The term calculus, if a goal needs one:
<its terms, typing and reduction, with their place>.

## Q3. What should run, and why?

* Proof search, countermodels, or both; a decision procedure, or search
  with a budget.
* Who will rely on the answers, so why they are certified. <Where the
  request does not say: decide from Q4 and from what the calculus is
  used for, and record it.>
* **The certificate of record** for a derivation
  (`reference/certify.md` §1): the tree of moves, which is the default,
  or the script; and why.
* **The route to countermodels**: what the source gives (a failed search
  read as a model; a separate construction; none).
* **The level aimed at** for the refutation side
  (`reference/certify.md` §3): 1, 2 or 3; and at level 2 or 3, what a
  finite model is, as data.
* **Does a search in this calculus end by itself?** What the source says
  ends it, with its place; or that the source is silent.

## Q4. How do people use it?

* The source's worked derivations (each with its place): these are the
  exercises, and the first tests of the transcription. <If it has
  none: which derivations are chosen, and that the choice is ours.>
* The order in which rules are applied by hand; what a reader does without
  comment.
* What the explorer should show: <how a judgment should read; which steps
  should be done at once; what a reader wants to see of a failed attempt>.

## Q5. Which calculi is it related to?

* Translations in the literature, in either direction.
* Calculi already in this project.
* **Existing formalisations**, in any prover: what was found, and where
  you searched.

## Choices of encoding

Read `reference/adopt.md` §3 and `reference/explore.md` §2 and §13 before
filling this. Give the options you weighed, not only the one proposed, and
say what was tried in Lean to see that a choice is feasible.

**What `deriving` gives**, tried in scratch on every type this plan
names (stage 0, step 3), not on the judgments alone:

| type | `DecidableEq` | `Repr` | `Lean.ToExpr` | where it does not derive: what is written instead, or what must then not be asked of the type |
|---|---|---|---|---|
| formulas | | | | |
| judgments | | | | |
| moves | | | | |
| a finite model (Q3), and any other certificate | | | | |

In the third column give the reason with the choice, and **what the
choice does to the rules**: which rule of the source needs no
constructor under it, and why (exchange, where a rule finds its formula
by membership); which rule the encoding adds. A reader who has to ask
why a rule of the figure is missing was not given the reason here.

| choice | the options weighed | chosen, why, and what it does to the rules |
|---|---|---|
| a judgment as data | | |
| how a rule, and a move, names what it acts on | | |
| the family: into `Type` or `Prop` | | |
| what holds | the family itself; or validity in the semantics (`SKILL.md`, "What is trusted") | |
| where the source has two systems, or a measure to induct on | two families; one with a parameter; a function on derivations | |

## Goals, non-goals, order

**Goals**, in order: the source's soundness theorem first; then the rest,
a goal after those it rests on. Of each goal that is a lemma on the
source's way to another goal, say which one: if the proofs take another
route it falls off, and is decided on again (`SKILL.md`, stage 2,
step 4).

**Non-goals**, with the reason for each:

## The development's axiom policy

<For example: every theory file within `[propext, Quot.sound]`; or: the
completeness files may use `Classical.choice`, the rest not. If certifiers
are to be allowed more than `[propext, Quot.sound]`, say so here: it goes
into the project's `Harness.config`.>

## Dependencies

<Core Lean only (always, under `calculi/`); or which libraries, and why.>
The commit of `proof-tools` (of the checkout, or pinned): <…>. The
toolchain: <…>.

## Known non-theorems

| judgment | why it must fail | how it is expected to show here: a move refused (which side condition), a query where no move applies, an attempt that stays open, a search that does not end |
|---|---|---|

## Results that exist in Lean already, used and not re-proved

Theorems of this project or of a library that the campaign will import and
rely on. For each, why the notion it is about is the same notion here.

| result | where | why it is safe to use |
|---|---|---|

If none, say so.

## Budget

A guess is enough: its use is to say when a stage is closed with goals
still OPEN.

| stage | time expected, by the clock | what closes the stage short of its goals: a time by the clock, or a number of routes tried on one goal |
|---|---|---|

## The decisions that cost the campaign to reverse

Anything that is a choice about what is true or what is meant, not about
how to prove it: the source and the system, what "holds" means, the
axiom policy. Each is entered in `decisions.md` and comes first on the
closing page; what "holds" means is screened first (stage 0, step 3).
