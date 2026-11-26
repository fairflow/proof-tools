# The calculus-campaign skill against its design: the record of four campaigns

Written 2026-11-26 22:44 GMT, from the repository `fairflow/proof-tools` at commit `0e83910` on `main`. Nothing was built or run for this page: it is a reading of the files and of the git history.

The skill `calculus-campaign` was drafted on 2026-11-22 by a design session that had read the libraries at commit `2cf7044` and built nothing. That session sent eight conclusions, ten proposals (a to j) and eight questions. This page answers the questions from the record of the four campaigns run since, and is raw material for a later collation of the method notes. Every answer cites a file and line, a note by campaign and number, or a commit. Where the record does not settle a point the page says "not settled by the record", and what would settle it.

## How to read this page

* **The skill** is the folder `.claude/skills/calculus-campaign/`. Its files are cited without that prefix: `SKILL.md`, `reference/adopt.md`, `templates/plan.md`. Line numbers are those at `0e83910`.
* **The draft** is the skill's first commit, `ce28bcc` (2026-11-23 00:15 GMT). **The rewrite** is commit `1611566` (2026-11-25 07:46 GMT), which removed the gates.
* **The campaigns**, each in `calculi/NAME/` with its record in `calculi/NAME/campaign/`: `BrunnlerK` (nested sequents for the modal logic K, 2026-11-23, under the draft with its gates); `GLS` (a sequent calculus on multisets for provability logic, 2026-11-25, the first run of the rewrite); `MALL` (a one-sided sequent calculus for multiplicative-additive linear logic, 2026-11-26); `DILL` (a two-zone sequent calculus for intuitionistic linear logic, 2026-11-26).
* **A note** is cited as "BrunnlerK note 27": note 27 of `calculi/BrunnlerK/campaign/method-notes.md`. The four files hold 75, 26, 28 and 21 notes: 150. MALL's are numbered 1 to 16, then 23 to 28, then 17 to 22, in that order in the file.
* A campaign file is cited by its name alone where the campaign is clear from the sentence: "`cost-log.md`, lines 53 to 62" under BrunnlerK is `calculi/BrunnlerK/campaign/cost-log.md`.

## The starting point, and the eight conclusions in brief

The design session read the libraries at `2cf7044` (2026-11-21 22:23 GMT). The draft's own last paragraph says that its text was checked against `3fa25c0` (2026-11-22 23:45 GMT), and that line is unchanged today (`SKILL.md`, lines 866 to 867; BrunnlerK notes 60 and 66). The draft's commit message says that the two Lean templates "were compiled against the library at 3fa25c0". Fourteen commits to `ProofTools/` lie between the two commits (listed under question 5). So part of what the design session concluded had been acted on in the library before the first campaign began, on 2026-11-23 at 07:23 GMT.

| | the conclusion of 2026-11-22 | at `0e83910` | evidence |
|---|---|---|---|
| 1 | nothing compiles a checker, a search or a decision procedure from the rules | still so, and stated as the method's form | `SKILL.md`, lines 854 to 861; each campaign wrote `step`, its two theorems, the check of a model and every producer by hand (`calculi/NAME/NAME/Proof.lean` and the files of Run) |
| 2 | `apply_move` did not use the zipper; `#walk` and `Tac` used its types and none of its moves | changed in part, before any campaign: the cursor's motions are the zipper's moves, and the cursor serves `run`, `#walk` and `apply_move where`. A move by `apply_move` is still a node built on Lean's own goals | commit `b2f2cdb` (2026-11-22); `ProofTools/Explore/Tactic.lean`, lines 10 to 14 and 25 to 30. No campaign's record speaks of it |
| 3 | `S.Sound D` joins `step` to the family one way; the converse is asked nowhere | the library still does not ask it; the skill asks it, and each campaign proved it | `docs/explore.md`, line 164 ("Not asked, not given: the converse"); `reference/explore.md`, lines 209 to 221; question 4 |
| 4 | the sequence from paper to explorer had never been walked; no compiled public model of "family, then soundness into the family" | walked four times; a compiled model exists in the library's tests and in the skill's template | question 2; commit `b7b70d4` (2026-11-22, `ProofToolsTest/Explore/MapOut.lean`); `templates/Instance.lean.txt` |
| 5 | the infoview showed Lean's goal, and each instance wrote the same delaborator | the library has one delaborator for every instance | commit `bbdae58` (2026-11-22, `delabAtt`); question 7 |
| 6 | `lean-certify` checks every `Certifier` and `Engine` against the axiom list (R4) | the paragraph is as drafted; no campaign asked for an exception | `SKILL.md`, lines 792 to 796; `calculi/GLS/campaign/report.md`, line 132 ("Exceptions to the axiom policy: none"); `calculi/DILL/campaign/measurements.md`, lines 22 to 26 |
| 7 | housekeeping: an installed `lean-certify` skill older than the repository's; audit commands in drifted copies, `#uses` missing; the skeleton script elsewhere; Lean v4.31.0 only | the older installed copy was met again and the skill now says which file to read; no `#uses` in `ProofTools/`; the skeleton script is still not in this repository; still v4.31.0 only | `calculi/BrunnlerK/campaign/gates.md`, lines 504 to 524, and commit `af3d56e`; `reference/adopt.md`, lines 33 to 38; `lakefile.toml`, lines 6 to 8 (on v4.33.0 `ProofTools/Zipper.lean` does not build, seen 2026-11-22) |
| 8 | open after a cold read: no public model of a structured judgment; no corpus driver, no generator of fact files | one public instance with nested judgments; still no driver and no generator in the library, and four written in the campaigns | `reference/explore.md`, lines 626 to 627; `reference/certify.md`, lines 341 and 410; question 7 |

## Question 1. Which of a to j survived, which were dropped or replaced, which proved wrong

| | the proposal | in the skill at `0e83910` | by what, and on what evidence or whose word |
|---|---|---|---|
| a | one skill joining the three components, with eight rules for every stage | **Survived in structure, changed in three rules.** The table of components is as drafted. The rules are nine. Rule 5 (a stage in a fresh session from a brief) and rule 6 (a stage ends when its report can be read) are replaced; rule 7 (do not change the libraries) is kept with "stop and report" turned into "record it and go on"; rule 8 (keep `method-notes.md`) is kept | `SKILL.md`, lines 175 to 184 and 290 to 368. The rewrite, at the reviewer's word. Rule 5 was never followed in any campaign |
| b | "How a gate is run"; two gates in Adopt | **Replaced.** The section is gone. In its place: "Deciding, checking, stopping", the file `decisions.md`, four checks of meaning run by the operator, three kinds of stop, and a gate only for a thing the reviewer asks to pass | `SKILL.md`, lines 458 to 532. The rewrite, at the reviewer's word, on the figures of BrunnlerK's cost log |
| c | `D` as a choice signed in the plan: the family (default) or validity | **Survived, with "signed" replaced by "recorded".** Every campaign took the default. The validity form has not been used by a campaign | `SKILL.md`, lines 764 to 775; the four decisions cited in the notes below |
| d | the converse entered in `statements.md` during Adopt, PROVED or OPEN | **Survived and strengthened**: "Prove it in Adopt where you can". PROVED in all four campaigns, in Adopt | `reference/explore.md`, lines 209 to 221 and 697 to 702; `templates/statements.md`, lines 65 to 69; BrunnlerK note 28; question 4 |
| e | a rule at a place inside a judgment: the conclusion a variable, an address in the constructor, the same functions in the family and in `step` | **Survived, and held** on the one nested calculus. Several additions and one correction came from that campaign | `reference/adopt.md`, lines 239 to 245; `reference/explore.md`, lines 644 to 716; BrunnlerK notes 6, 21, 27, 29, 34; question 3 |
| f | judgments as data: lists with rules by membership; admissible rules as theorems; two systems as two families or one with a Boolean | **Survived, and its first part proved incomplete.** The membership form is wrong for a logic with no weakening. A third form was added | `reference/adopt.md`, lines 149 to 180; MALL note 1; commit `94df876` |
| g | an OPEN statement as a named proposition, never a `sorry`; a case that will not close as a named hypothesis | **Survived, and extended** to a goal that is data (a named type). The named hypothesis was never needed | `reference/adopt.md`, lines 360 to 391 and 508 to 512; BrunnlerK note 36 |
| h | a third kind of divergence, representation | **Survived unchanged**, and used in all four rule tables | `reference/adopt.md`, lines 327 to 336 |
| i | templates: plan, rule table, statements, gates, report, brief, record, a cost log by session with exchanges classed, two Lean skeletons never compiled | **Mixed.** Plan, rule table, statements and brief: kept and amended. Gates: replaced by `decisions.md`. Report: replaced by one closing page and a status board. Record: never used. Cost log: reshaped twice. The Lean skeletons were compiled before the draft was committed | the folder `templates/`; `git diff --stat ce28bcc..0e83910`; the notes below |
| j | a section "What is not built, so do not look for it", and a list of passages that planned library changes R2 to R5 would make out of date | **The section survived word for word. The list is in no committed version of the skill** | `SKILL.md`, lines 854 to 868, against lines 481 to 494 of the draft; not settled by the record what became of the list |

The skill grew from 2 846 lines in 16 files at the draft to 4 205 lines at `0e83910`, over twenty commits, the draft included (`git log -- .claude/skills/calculus-campaign`).

### Notes on a: the rules

* **Rule 5, a fresh session for each stage, was never followed.** In BrunnlerK the reviewer said at the first boundary: "Continue here with Adopt … I think a single session may be sensible, we'll see how much context is needed" (`gates.md`, lines 181 to 194; BrunnlerK notes 19 and 56). All five stages ran in one session (`cost-log.md`, rows 1 to 7). The rule was first amended to allow this (commit `3186d6d`) and then replaced by "Sessions are yours to arrange" (`SKILL.md`, lines 310 to 340). GLS, MALL and DILL each ran in one session that started agents: 5, 5 and 12 of them before the closing page (question 8). So the record does not test the drafted rule: it was set aside, not shown wrong. What the draft gave as its reason, that a long session pays to read its own history, is still the reason the present rule gives for handing a stage to an agent.
* **Rule 6, a report at the end of each stage, is replaced.** BrunnlerK wrote six stage reports (`report-0` to `report-5`). The rewrite has "No report is written at the end of a stage" (`SKILL.md`, lines 817 to 820): a status board kept true at every commit, and one closing page of six parts. The later campaigns each have one `report.md`.
* **Rule 7 is kept, with two changes.** A need of the library is now a finding to record and work round, not a stop (`SKILL.md`, lines 352 to 360). And the reviewer may ask for a change to the skill during a campaign, in a commit of its own (BrunnlerK note 16). The second was not always kept to the letter: commits `dcf7a5b` and `7d7f283` (BrunnlerK, before the rule had the words) and `3f435db` (DILL, after) change the skill and a campaign's files together. Question 5 has what the campaigns asked of the libraries.
* **Rule 8 is kept.** It produced the 150 notes. Of them 96 are applied to the skill and still in its text, 13 were applied and then reworded or replaced by the rewrite, 20 are proposed and not applied (18 of them DILL's), and 21 are findings or records that ask for no change (question 6).
* **A ninth rule**, "Decide, record, go on", came with the rewrite (`SKILL.md`, lines 365 to 368).

### Notes on b: the gates

The draft had seven gates: the target, the plan, the rule table, the reviewer's test, the statements, the producers, the tutorial. What happened to them in the one campaign that ran under them (`calculi/BrunnlerK/campaign/gates.md`):

| gate | what the record shows |
|---|---|
| the target | passed: "Yes, as proposed" (`cost-log.md`, exchange 5) |
| the plan | answered in part, then passed at a second putting. It changed the work: the form of "valid" (truth in every two-valued model, in place of the operator's indirect form), the letters, the folder, where commits go (`gates.md`, lines 85 to 179; BrunnlerK notes 12 to 15) |
| the rule table | passed as put: "As put thanks", after one question (`gates.md`, lines 196 to 222). No constructor changed |
| the reviewer's test | deferred by the reviewer and never made (`gates.md`, lines 224 to 244; `report-5-2026-11-23.md`, line 100, "Yours, and not done") |
| the statements, first sending | "signed as put", after the operator had stopped twice though a goal had been set (`gates.md`, lines 246 to 285; BrunnlerK note 35) |
| the statements, second sending; the producers | decided by the operator, the gates having been lifted (`gates.md`, lines 306 to 407) |
| the tutorial | put, and not worked through (`gates.md`, lines 408 to 428) |

The words that removed them. During Prove: "Stop telling me to read and approve everything. Act independently." (`gates.md`, line 315; `cost-log.md`, exchange 16). Two days later: "the primary purpose of the skill seems to have been to ensure an agent implementing it cannot work independently, while my intention in commissioning the skill was more to ensure an agent CAN work independently", and then "Yes, rewrite it" (`gates.md`, lines 472 to 502). The figures put to the reviewer with the question, from the cost log: of seven gates one changed the work, the plan's; no error was found at a gate; a little over two hours of work in a span of 11 h 24 min; 2 933 of 6 459 lines of Lean in the last 36 minutes, where nothing waited (`gates.md`, lines 479 to 484).

What replaced each gate is tabulated in BrunnlerK note 67. In brief: the reviewer's signature on the rule table became a second transcription by a cold reader; the reviewer's sight of each statement became a screen and a reading back by a cold reader; the reviewer's test became every exercise run by script; soundness and completeness are proved before the other goals as a check of the rule table.

Whether the gates would have caught an error is not settled by the record: the one campaign under them had no error of transcription to catch (question 2). One thing the rewrite gives up is recorded: at the plan's gate the reviewer chose a better form of "valid" than the operator had proposed, and nothing in the present text makes that choice (BrunnlerK note 69). The present text gives an order in which to look for the forms (`reference/adopt.md`, lines 393 to 419).

### Notes on c: what holds

All four campaigns took the family: BrunnlerK (`plan.md`, line 357, the row "what holds"); GLS (`decisions.md`, the entry of 09:07, "what holds is the family"); MALL (`decisions.md`, the entry of 10:03, "two families, into `Type`; what holds is the family"); DILL (`decisions.md`, line 145: "what holds is the family with cut"). Validity as what holds is exercised only by the library's own example (`ProofToolsTest/Explore/Calculus.lean`). Whether the skill's text for that case is right is not settled by the record: a campaign that chose it would settle it.

### Notes on f: judgments as data

* **Lists with membership.** Used inside a node by BrunnlerK (`rule-table.md`, divergence D1), by GLS (divergence D2), and for DILL's unrestricted zone (divergence R2).
* **Wrong where there is no weakening.** The draft offered two forms, membership or an exchange rule. Membership makes weakening admissible, so it is wrong for a linear calculus (MALL note 1). The third form, a variable conclusion under a permutation hypothesis, is now `reference/adopt.md`, lines 169 to 180.
* **Admissible rules as theorems**: kept in all four. Exchange is a theorem or a function in each (BrunnlerK goal 4; GLS; `Fam.exch` in MALL and DILL).
* **Two systems.** One family with a Boolean parameter: BrunnlerK (divergence D6) and DILL (divergence R3). Two families: GLS (`Fam`, `PSFam`) and MALL (`Fam`, `CF`). DILL's decision records why it did not follow MALL: "every structural function twice" (`decisions.md`, lines 184 to 185).

### Notes on g: OPEN statements

Each later campaign fixed its goals as named Lean propositions or types before their proofs: MALL in a commit of its own, `c81bc59`; DILL in `584b842`; GLS in the commit that also has its first proofs, `c96ddc1`, the statements having been written, screened and sent to be read back first (GLS note 10). BrunnlerK found that a goal may be data and not a proposition, and stated it as `abbrev ProofOrRefutation : Type` (BrunnlerK note 36); that form is now beside the other. The named hypothesis for a case that will not close was not used: no entry of any `statements.md` has one, since every goal that was attempted ended PROVED (two goals of BrunnlerK were set aside by the reviewer). Whether the device works is not settled by the record. DILL note 10 records what a cold reader said of every goal stated as a type: classically it says no more than that the type is inhabited. The proposed answer (say what the type asserts beyond its proposition, and test that the kernel runs it) is not applied.

### Notes on i: the templates

* **`gates.md`** was deleted by the rewrite; `decisions.md` replaces it. BrunnlerK keeps its `gates.md`; the others have `decisions.md`.
* **`report.md`**: a report of five parts for each stage became a closing page of six parts (`SKILL.md`, lines 798 to 815).
* **`record.md`** (for a calculus already mechanised, or designed) has never been used: no campaign folder has the file, and no campaign took a shorter path.
* **The cost log.** Three faults were found in the drafted form. The operator, being a language model, does not know its requests, tokens or cost (BrunnlerK note 9). The three classes of exchange (decision, correction, rescue) had no place for a question (BrunnlerK note 10); the template now has seven classes (`templates/cost-log.md`, lines 55 to 64). A row for each session does not fit one session that runs five stages beside agents (MALL note 22); the template now has rows by stage, a table of agents and a section "Time lost".
* **The Lean skeletons** were compiled before the draft was committed (the message of `ce28bcc`). Two things in them did not fit a later calculus. The form of S1 in `templates/Instance.lean.txt` relies on a rule that reduces once the move and the shape of the judgment are known, and does not fit a rule that first looks its place up (BrunnlerK note 27). The compiled template has no test module for the source's worked derivations, which the present text asks for (BrunnlerK note 70).
* **The brief** gained what the campaigns with agents needed: the names taken in the namespace, files on disk early, builds by target, the look at the machine before a build (`templates/brief.md`, lines 26 to 37; MALL notes 8, 9, 25; DILL note 14).

### Notes on j

The section is unchanged from the draft, the commit it names included. No file of the skill at `ce28bcc` has a list of passages that library changes would make out of date, and no later commit adds one. The record names one of R2 to R5 only (question 5). Whether the list was dropped before the first commit, or was never part of the committed text, is not settled by the record: the design session's own draft would settle it.

## Question 2. Has the full sequence been walked from a paper, and where did errors of transcription show

**Walked four times**, each from a source to a closing page with an explorer: BrunnlerK on 2026-11-23, GLS on 2026-11-25, MALL and DILL on 2026-11-26. Four qualifications:

* **BrunnlerK**: the test with the explorer was never made by a person. The operator built the source's one worked proof with the tactic, and its map out is equal by `rfl` to the term written with the constructors (`cost-log.md`, lines 66 to 69). The operator did not start cold: it had read the source and drafted a plan before it had the skill (BrunnlerK notes 1, 3, 60).
* **GLS**: the rules were transcribed from the authors' published formalisation before any prose could be read, and compared with a thesis chapter four hours later; the paper's own figure was never seen (`rule-table.md`, lines 7 to 15; `SKILL.md`, lines 261 to 263).
* **MALL**: the source draws no derivation of the fragment, so ten derivations of what it asserts stand in for the worked derivations (`rule-table.md`, lines 16 to 21; MALL note 4).
* **MALL and DILL**: the cold readers are the same model as the operator, so a misreading shared by all would pass (`calculi/MALL/campaign/report.md`, lines 133 to 135).

**Errors of transcription found: none, in any campaign, by any check, at any stage.** Each rule table ends with an empty list (BrunnlerK `rule-table.md`, lines 454 to 461; GLS, lines 376 to 382; MALL, lines 397 to 402; DILL, line 130, "Errors of transcription found: none"). DILL's cost log gives the count by what could have found one: "`#rules` or `#slime` 0; a worked derivation 0; the second transcription 0; soundness or completeness 0; a person 0; later use 0" (`cost-log.md`, lines 92 to 96). So the question "at the rule table, at the test, or later" has the answer "nowhere", and the record cannot say what the checks are able to catch. The skill says so of its own checks (`SKILL.md`, lines 258 to 260).

What the record does name is listed below: faults of the source, faults that a check stopped before they reached the family, and faults of other things than the rules.

| campaign | what | kind | caught by | stage |
|---|---|---|---|---|
| BrunnlerK | the proviso of the second system read as a condition at the node ("the formula added is not already there") | a simplification that was tempting and is false; it never entered the family | a test of four lines, three sibling boxes (BrunnlerK note 22; divergence D11) | Adopt, before the rule table was put |
| BrunnlerK | the node named with one of the figure's letters, so that the figure's own letter moved | a fault of readability in a draft constructor | the operator, reading the draft against the figure (BrunnlerK note 20) | Adopt, before the rule table was put |
| BrunnlerK | a type declared inside a namespace, which the family's binders did not resolve | a false start in the family's file | the file's bound on axioms (`cost-log.md`, lines 84 to 86) | Adopt, before the rule table was put |
| BrunnlerK | "valid" over all models implies excluded middle | a fault of a proposed statement, not of a rule | a scratch screen (BrunnlerK note 5); the form was then chosen by the reviewer at the plan's gate | Survey |
| BrunnlerK | four pinned messages wrong at the first run of the tests | the operator's expectation, not the family | Lean's output (`cost-log.md`, lines 102 to 104) | Adopt, at the tests |
| BrunnlerK | the search gave proofs of 2ⁿ⁺¹ − 1 steps for an instance of the axiom | a fault of the search | a family written to measure (BrunnlerK note 50) | Run |
| BrunnlerK | four lines of the tutorial did not do what their comments said | a fault of the tutorial | elaborating it (`cost-log.md`, lines 140 to 143) | Explore |
| GLS | text extracted from the PDF had lost the modal signs, so the modal rule read as a rule with no modality | a hazard of reading; it did not reach the family, which came from the formalisation | reading the page as an image (GLS note 23) | the late comparison with the prose, after Explore |
| GLS | three pinned messages or values; a comment in the corpus; a helper that called itself twice | the operator's code and expectation | the build; the search's tree printed beside the comment; two searches timed on one input (GLS notes 12, 26; `cost-log.md`, lines 72 to 77) | Prove and Run |
| MALL | three misprints in the source's proofs, outside the definition of the rules | faults of the source that touch no rule | the second transcription (`rule-table.md`, lines 378 to 380) | Adopt |
| MALL | three pinned values typed from expectation; an agent's function with a name already taken | the operator's and an agent's | the build (`cost-log.md`, lines 62 to 71) | Run; Prove |
| DILL | the source's figure prints the conclusions of two right rules with the wrong connective | a fault of the source (divergence W1); transcribed with the right connective from the start | the operator, at the plan (14:59); found again by the cold reader, unprompted (`rule-table.md`, the divergence log) | Survey; then Adopt |
| DILL | the sign `;` between the zones | a fault of notation: the plan's screen passed in a file with no tactic block | the first build of a file with tactics (DILL note 4; divergence R4) | Adopt |
| DILL | the plan's prediction for one non-theorem | a fault of the plan, not of the instance | the tests (`decisions.md`, lines 296 to 320) | Adopt, at the tests |
| DILL | two functions on the family compiled by well-founded recursion, so that the kernel could not run them | a fault of definition, with no statement changed | two agents independently, from a `decide` that failed (DILL note 6; `decisions.md`, lines 278 to 294) | Prove |

The reading back of definitions and statements, the check that stands beside the second transcription, also found no fault in GLS, MALL or DILL. It did find, unprompted, the instances that refute weakening and contraction in MALL and an instance against each of the eight statements expected false in DILL (`calculi/MALL/campaign/report.md`, from line 122, and `calculi/DILL/campaign/report.md`, from line 156).

## Question 3. Proposal e on a real nested or structured calculus

**BrunnlerK, nested.** The shape used is the one proposed (`rule-table.md`, lines 27 to 50, and divergence D2):

* the conclusion of every constructor is a variable `Γ`;
* the address is a path `a`, the positions of the boxes entered from the root (`[1, 0]` is box 0 of box 1);
* a side condition `Γ.node? a = some Θ` names the whole node at that place, and a membership condition says the main formula is there;
* the premise is `Γ.setNode a Θ′`;
* one rule needs a second lookup, the position `i` of a box in the node (`Θ.box? i = some Δ`);
* `step` uses the same functions (`node?`, `setNode`, `add`, `erase`, `addBox`, `box?`, `setBox`), and the move carries what the constructor carries less the derivations and the proofs of the side conditions (`rule-table.md`, lines 370 to 392).

The address shape held. Adopt's report: "`apply_move` names a place inside a sequent with no change: a path is an argument of the move like any other, and patterns fill it" (`report-1-2026-11-23.md`, lines 160 to 162). What the campaign added to the proposal:

* **S1 does not go through in the template's form** when every rule begins by looking its place up: the rule is split into the rule given the node (`Move.ruleAt`) and the lookup, and split once more for the second lookup (BrunnlerK note 27; `reference/explore.md`, lines 668 to 696).
* **The draft's check of one step in the kernel was wrong as written**: core Lean has no decidable equality on the result type of `step`, so the check goes through `Except.toOption` (BrunnlerK note 29).
* **`#rules` prints the functions by name**, so the rule table cannot be read against the figure without their definitions; three sections were added to the template (BrunnlerK note 21).
* **A term syntax** is needed to read a nested judgment at all (BrunnlerK note 34).
* **The figure's own shape is recovered as theorems.** The reviewer asked at the rule table's gate, "So the paper puts no constructors in the rule conclusion?" Contexts with `fill`, and each rule in the figure's shape as a derived rule, were then added (`gates.md`, lines 205 to 222 and 287 to 300; `calculi/BrunnlerK/BrunnlerK/Ctx.lean`).
* **In Prove**, cases on pairs of positions were replaced by one relation between whole judgments (BrunnlerK notes 44 and 45; `reference/adopt.md`, lines 521 to 579).

**What `#slime` reported.** No computed index, on every family of every campaign, with the two controls behaving as they should (the slimed control flagged at `ms ++ ns`, the clean one not):

| campaign | the output recorded | where |
|---|---|---|
| BrunnlerK | `Fam`: 1 index, 6 constructors, 0 carrying green slime; `FamO`: 5 constructors, 0 | `rule-table.md`, lines 330 to 353 |
| GLS | `Fam`: 5 constructors, 0; `PSFam`: 6, 0 | `rule-table.md`, lines 217 to 232 |
| MALL | `Fam`: 10, 0; `CF`: 9, 0; `Lit` (the figure as it stands): 11, 0 | `rule-table.md`, lines 310 to 314 |
| DILL | `Fam`: 20 constructors, 0 | `rule-table.md`, lines 262 to 264 |

No record shows `#slime` reporting a computed index on a family of a campaign. Whether an earlier draft of any family was flagged and repaired before the table was written is not settled by the record. One limit of the command showed in DILL: its judgment is a structure, so a conclusion is a constructor applied to variables, which `#slime` rightly calls clean; a function on the family whose argument has that index was then compiled by well-founded recursion with no warning (DILL note 6). `#slime` looks at constructors, not at functions.

**Did `deriving` work on the tree type.** For the type chosen, yes; for the type the source's wording suggests, no.

* A type that holds a list of itself: `DecidableEq` does not derive (tried in BrunnlerK's Survey: `plan.md`, line 353, option (a); `reference/explore.md`, line 631).
* A multiset as a quotient, nested in its own type: the kernel refuses the declaration (`plan.md`, line 355).
* The type chosen, `leaf` of a node's formulas or `cons` of an inner judgment and the rest, with no list of itself: `DecidableEq`, `Repr` and `Lean.ToExpr` all derive (`calculi/BrunnlerK/BrunnlerK/Sequent.lean`, line 32). This was a fourth option, not among the draft's three (BrunnlerK note 6).
* The same failure met the type of models later: a tree of worlds holds a list of itself, the plan's probe had been run on the judgments only, and a construction of Prove had to be designed another way (BrunnlerK note 46). GLS's plan then probed the model's type too (`plan.md`, line 308).

**The three encodings of `reference/adopt.md` §3, and where each came from.**

| the form | from | used by |
|---|---|---|
| a list, each rule asking for its formula by membership and adding at the head (lines 161 to 167) | the draft, unchanged but for its last clause | BrunnlerK inside a node; GLS; DILL's unrestricted zone |
| a list with an exchange rule added (the same paragraph) | the draft | no campaign's working family. MALL has it as a second family, `Lit`, the figure letter for letter, proved to derive the same sequents (`statements.md`, S3, `lit_iff_fam`) |
| every constructor concludes a variable `Ξ` under `Ξ.Perm (…)` (lines 169 to 180) | MALL note 1 and MALL's decision of 10:03 (`decisions.md`, lines 151 to 180); into the skill by commit `94df876` | MALL; DILL's linear zone, "as written, one form for each zone" (DILL note 19) |

What the third form costs is recorded with it: Lean infers nothing from a variable conclusion, so constructors take their formulas and contexts as explicit arguments; and S2 needs its induction generalised over a permutation (`famToDer_perm` in MALL and DILL). The table of `reference/explore.md` §13, for judgments that are not flat, grew from three options to four (BrunnlerK note 6).

**DILL, two zones.** The judgment is a structure of two lists and a formula, flat, with no address. Each zone takes its own form (divergences R1 and R2). Two things were new. The sign between the zones could not be the source's (DILL note 4). And a move of a right rule names the conclusion's formula though `step` could read it, so that S1 is a definition with no case for each other shape of conclusion (divergence R5; DILL note 7): this goes against the sentence "Nothing a move could compute from the judgment need be in it" (`reference/explore.md`, line 112), and the proposed line is not applied.

**MALL, one-sided up to permutation.** No address. The two rules that divide a context name, in the move, the context of the first premise as a list; a Boolean mask and a split by position were weighed and not taken (`decisions.md`, lines 247 to 267).

## Question 4. The converse: stated and proved in each campaign?

Yes, in all four, under one name, in Adopt, in the commit that first has the proof system.

| campaign | S1 | S2, the converse | where | the commit | for which system |
|---|---|---|---|---|---|
| BrunnlerK | `step_sound : S.SoundT K` | `famToDer : FamToDer`, with `FamToDer := ∀ Γ, K Γ → Nonempty (Der S Γ)`, from `der_of_fam : Fam c Γ → c = false → Nonempty (Der S Γ)` | `calculi/BrunnlerK/BrunnlerK/Proof.lean`, lines 131, 157, 199 | `5de5634` | the system without cut. There is no move for cut and none for the second system (`rule-table.md`, lines 380 to 381) |
| GLS | `step_sound : S.SoundT Fam` | `famToDer : FamToDer`, `∀ j, Fam j → Nonempty (Der S j)` | `calculi/GLS/GLS/Proof.lean`, lines 80, 103, 107 | `010a68e` | GLS only; the proof-search variant has no proof system (`rule-table.md`, lines 17 to 19) |
| MALL | `step_sound : S.SoundT Fam` | `famToDer : FamToDer`, `∀ Γ, Fam Γ → Nonempty (Der S Γ)`, from `famToDer_perm` | `calculi/MALL/MALL/Proof.lean`, lines 105, 136, 140, 204 | `e605abf` | the calculus with cut |
| DILL | `step_sound : S.SoundT (Fam true)` | `famToDer : FamToDer`, `∀ j, Fam true j → Nonempty (Der S j)`, from `famToDer_perm` | `calculi/DILL/DILL/Proof.lean`, lines 159, 220, 224, 349 | `538a5e2` | the calculus with both cuts |

Each is entered in the campaign's `statements.md` as S2, PROVED, and each closing page lists "S2: `step` refuses no instance of a rule" among the checks.

* **The form is the proposed one**, `Fam j → Nonempty (Der S j)`, a proposition. No campaign states a function from the family's derivations to the explorer's, and the library still lists that map as not built (`reference/explore.md`, lines 611 to 613).
* **In MALL and DILL "faithful" is up to a permutation.** The premises of `step` are the rule's only up to one, so S2 is proved for every permutation of the sequent (MALL note 1; `statements.md`, S2, in each).
* **Did a `step` ever turn out weaker than its family?** The record names no case. BrunnlerK: "S2 found no instance of a rule that `step` refuses" (`cost-log.md`, line 69) and "it found nothing wrong" (BrunnlerK note 28). In each campaign the file `Proof.lean` has had no later commit that changes a side condition or a premise of `step`: the one later commit, in DILL, changes the texts of four refusal messages and the order of the moves offered, with "no side condition, no premise, no theorem changed; S1 and S2 built unchanged" (`decisions.md`, lines 296 to 311; commit `2f53fa0`).
* **By decision, not by fault**, the proof system is smaller than the family in two campaigns: BrunnlerK has no move for cut, and GLS none for its second family or for cut.
* Whether a draft of `step` was weaker and was repaired while S2 was being proved, inside one commit, is not settled by the record. The draft of the skill let S2 stay OPEN (`reference/explore.md` at `ce28bcc`, lines 211 to 212); no campaign left it so.

## Question 5. "Do not change the libraries": what was asked, and what has landed

**What each campaign asked of `ProofTools/` and `LeanCertify/`.** Each closing report says that nothing of the library was changed.

| campaign | asked, or recorded as lacking | where |
|---|---|---|
| BrunnlerK | at Survey and Adopt: nothing. At the close, two things not served: a tactic that applies a tactic of the calculus to the goal in front of it, and a goal shown as a tree in the infoview. In passing: a word of the library's syntax, `size`, becomes a keyword for every file that imports it; the line the move tactic offers takes a trailing comment with it. After the campaign: a library function for the test that Lean reads a judgment printed as Lean source, wanted and not asked | `report-0-2026-11-23.md`, line 99; `report-1-2026-11-23.md`, lines 160 to 162; `report-5-2026-11-23.md`, lines 33 to 36; BrunnlerK notes 51, 55, 75 |
| GLS | `Cert` has no `DecidableEq`; a script printed by `Repr` over several lines is not always Lean source; the offered line is placed after comment lines that follow a pattern | `report.md`, lines 170 to 176 |
| MALL | the permutation lemmas free of `Classical.choice` (`perm_count` and those on `erase`) belong in the library: written in GLS and again here. For the tutorial pages: a status REFUTED, and `#statement` printing what is negated | `report.md`, lines 202 to 206; MALL notes 2 and 20; `method-notes.md`, lines 317 to 320 |
| DILL | the same permutation lemmas, now written three times; the enumerations of picks and divisions of a list, written twice; the explorer offers moves as one list, with nothing to mark where the rules that lose nothing end | `report.md`, lines 257 to 263 |

None of these has landed. The permutation lemmas are still in `calculi/GLS/GLS/Structural.lean`, `calculi/MALL/MALL/Perm.lean` and `calculi/DILL/DILL/Perm.lean`, and nothing under `ProofTools/` or `LeanCertify/` names `perm_count`.

**What has landed since `2cf7044`** (`git log 2cf7044..0e83910 -- ProofTools LeanCertify ProofTools.lean LeanCertify.lean`): fifteen commits, all under `ProofTools/`. No file under `LeanCertify/` has changed (`git diff --stat 2cf7044..0e83910 -- LeanCertify` is empty). Fourteen of the fifteen are dated before the first campaign began.

| commit | date (GMT) | in one line |
|---|---|---|
| `891fe56` | 11-21 22:31 | a panel for `#walk`, as a trial: the attempt drawn as a tree in the infoview |
| `8310474` | 11-22 07:39 | the panel's buttons are the motions the view offers |
| `b7b70d4` | 11-22 20:33 | soundness of the moves for a family into any sort (`SoundT`), and the map out |
| `178683b` | 11-22 20:44 | the guide says what the map out adds; a test of it in the kernel |
| `05ddc63` | 11-22 20:51 | rose trees with labelled edges, their zipper, and the instance of the family zipper |
| `7ee39a2` | 11-22 21:00 | a merge: "the rose-tree zipper files with the map out of stage R4" |
| `6ee81d3` | 11-22 21:30 | a tree of moves as a certificate (`Cert`), a rose tree of the library; `Evaluator` removed |
| `c475963` | 11-22 21:33 | the map out of a derivation, at a node (`Der.mapOut_node`, `Der.mapOutAll`) |
| `24d9d85` | 11-22 21:51 | a header comment of `Explore/Cert.lean` |
| `bbdae58` | 11-22 22:29 | `apply_move where`; the walker as a tactic block; one delaborator of the goal (`delabAtt`) |
| `4314c3e` | 11-22 22:34 | two functions fewer in the drawing of an attempt |
| `b2f2cdb` | 11-22 23:19 | the zipper's step to a sibling; the cursor's motions are the zipper's moves |
| `fe8b4e7` | 11-22 23:43 | one change at the focus (`Cursor.replace`); a session of commands (`Cursor.walk`) |
| `3fa25c0` | 11-22 23:45 | a lemma and an instance that nothing used are removed |
| `906e2fa` | 11-26 09:20 | `#statement`, `#statement_status`, `#statement_location` (`ProofTools/Audit/Statement.lean`), with `scripts/tutorial_pins.py`, for pinned tutorial pages |

The one commit dated within the campaigns, `906e2fa`, is not a commit of a campaign's operator: it came from the session that wrote the GLS tutorial page after that campaign had closed (`calculi/GLS/campaign/decisions.md`, lines 431 to 446), and it changes the library, the skill and `calculi/GLS/` together. The reviewer's request for a tutorial is recorded there; a word of the reviewer for the change to the library is not. Not settled by the record: that session's own record would settle it.

**Was the rule kept?** No commit made by a campaign changes a file under `ProofTools/` or `LeanCertify/`. Outside their own folders the campaigns changed the skill, at the reviewer's word, and, with the rewrite, the repository's own pages that describe the method (commit `4185324`: the root `SKILL.md` of `lean-certify`, `docs/campaign.md`, `docs/outline.md`, `README.md`).

**Did R2 to R5 land?** The record names one of them, once: the merge `7ee39a2`, "with the map out of stage R4". By that name R4 is the soundness of the moves into any sort and the map out, and it landed in `b7b70d4` and `c475963`. R2, R3 and R5 are named nowhere in the repository as stages of work on the library: in commit messages, in `docs/` and in the skill those strings occur only as rules of `lean-certify`, which are another thing. What the fourteen commits of 2026-11-21 and 22 did is in the table; which of them were R2, R3 and R5 is not settled by the record. The design session's list of the planned changes would settle it.

## Question 6. Where operators still needed a rescue, and the themes of the notes

### Rescues, from the cost logs

Every cost log classes the reviewer's messages. The classes changed between the first campaign and the others (question 1, notes on i). **No exchange in any of the four logs is classed a rescue.**

| campaign | the log's classification | where |
|---|---|---|
| BrunnlerK | by stage, as decisions / corrections / rescues: Survey 7 / 3 / 0 and three questions; Adopt 2 / 0 / 0 and one question; Prove 4 / 2 / 0 and one question; Run 0 / 0 / 0; Explore 0 / 0 / 0. After the campaign: five more exchanges about the skill | `cost-log.md`, lines 27 to 62 |
| GLS | three messages: the command, and two answers at the one stop | `cost-log.md`, lines 24 to 32 |
| MALL | "None after the task that started the session. No stop." The table is empty | `cost-log.md`, lines 75 to 80 |
| DILL | two rows: the command, and one correction. The table by stage adds, for Run: "two questions; two rules on builds, relayed" | `cost-log.md`, lines 85 to 90 and 98 to 106 |

Two of these tables are short of what the same campaign's `decisions.md` holds. MALL's table is empty, and its decisions record the reviewer's words after the closing page ("Can you complete the counter model construction? …", and a later command for interpolation: `decisions.md`, lines 403 to 432). DILL's table has two rows, and its decisions have four entries headed "A word of the reviewer", one of them holding two questions (`decisions.md`, lines 227, 321, 339, 359).

Where a person's word was in fact needed for the work to move, whatever its class:

| campaign | what happened | the log's class | cause |
|---|---|---|---|
| BrunnlerK | the operator did not find the skill, which was on another branch, until told that one existed (exchange 2) | correction | the skill's installation (BrunnlerK notes 1 and 2) |
| BrunnlerK | the operator stopped twice at the statements' gate after the reviewer had set a goal (exchange 14) | decision, and a correction of the method | the skill's gates (BrunnlerK note 35) |
| GLS | the session ended under a running command at about 09:57 and stood idle for 3 h 17 min, until the reviewer typed in it | answer at a stop | the environment (GLS note 20; `cost-log.md`, line 17) |
| MALL | after the closing page: five tool calls each waited ten minutes on a hook that did not answer, then the session's process ended; nothing ran for 80 minutes, until the reviewer wrote | not in the table | the environment (MALL note 25; `cost-log.md`, lines 44 to 51) |
| DILL | a write came back as declined by the user at the moment the application interrupted the sessions; the operator stopped and asked; twelve minutes, until "I declined no such thing." | correction | the environment (DILL note 5; `cost-log.md`, lines 46 to 57) |
| DILL | the machine restarted under several builds and an evaluation with no cap on memory; twelve minutes and three agents' work in flight; then nineteen minutes under a rule of one builder at a time, corrected by the reviewer | two rules, relayed | the machine, and a first wording of the rule (DILL note 14; `cost-log.md`, lines 59 to 83) |

None of these is a rescue in the mathematics. The logs' sections "What the operator did unaided" say so stage by stage: BrunnlerK has "Not unaided: nothing" for the second part of Prove, for Run and for Explore (`cost-log.md`, lines 121 to 143); GLS has "Unaided: everything in the repository" (`cost-log.md`, lines 81 to 82). After the gates were removed, the one stop an operator chose was GLS's question about a download, which the work did not wait on (`calculi/GLS/campaign/decisions.md`, lines 420 to 429); every other halt the logs record came from the environment or the machine, not from the method.

### The themes

Ten themes, chosen from the notes. Each note has exactly one. The assignment is this page's, made by reading each note; another reader would move some notes between neighbouring themes.

| theme | what it covers | BrunnlerK | GLS | MALL | DILL | all |
|---|---|---|---|---|---|---|
| RUN | certificates, searches, producers, the command at a shell, measurement | 10 | 6 | 6 | 3 | 25 |
| ENCODING | judgments, rules and moves as Lean data: types, letters, signs and keywords, the rule table and the checks of the transcription, S1 and S2 | 13 | 0 | 4 | 2 | 19 |
| STATEMENT | the form of a statement or a goal, screening, the reading back, which results are goals and by which route | 7 | 6 | 2 | 3 | 18 |
| SKILL | the skill's own text, defaults and installation, and the records of changes made to it | 15 | 0 | 0 | 0 | 15 |
| REVIEWER | gates, stops, permissions, delivery: what waits for the reviewer and what does not | 13 | 1 | 0 | 0 | 14 |
| RECORD | times, pinned values, the cost log, how a document is written | 3 | 2 | 5 | 4 | 14 |
| SESSION | sessions, agents and their briefs, commits beside agents, builds and the machine, the environment's interruptions | 2 | 4 | 4 | 3 | 13 |
| LEAN | Lean itself and proof technique: where `Classical.choice` enters, recursion, tactics, patterns of proof | 6 | 0 | 5 | 1 | 12 |
| SOURCE | getting, reading and citing the source; which document is the source | 1 | 5 | 1 | 3 | 10 |
| EXPLORER | the tactic, its tests, the exercises, the tutorial and its page | 5 | 2 | 1 | 2 | 10 |

The three most frequent: RUN (25), ENCODING (19), STATEMENT (18). Two themes belong to one campaign: 13 of the 14 notes on the reviewer and all 15 on the skill's own text are BrunnlerK's, the campaign run under the gates and the one whose notes were turned into changes in four separate passes. Six themes have notes in all four campaigns: RUN, STATEMENT, RECORD, SESSION, SOURCE and EXPLORER.

The state of each note is one of four:

* **applied**: a change to the skill that is in its text at `0e83910`, with the commit and the place;
* **applied, then reworded or replaced**: a change made after BrunnlerK that the rewrite, or a later commit, superseded; the place given is where the matter stands now;
* **proposed, not applied**: the note asks for a change and the skill does not have it;
* **finding** or **record**: no change asked.

| state | BrunnlerK | GLS | MALL | DILL | all |
|---|---|---|---|---|---|
| applied | 46 | 23 | 25 | 2 | 96 |
| applied, then reworded or replaced | 13 | 0 | 0 | 0 | 13 |
| proposed, not applied | 0 | 0 | 2 | 18 | 20 |
| finding or record | 16 | 3 | 1 | 1 | 21 |

Three of the four notes files end with a section on what became of the notes, and the table below uses them: BrunnlerK (`method-notes.md`, lines 372 to 506), GLS (lines 216 to 255), MALL (lines 280 to 320). DILL's file has no such section; the state of each DILL note was found by searching the skill's text for what the note proposes.

**Three of the files' claims, checked against the skill's text.**

* BrunnlerK's table says note 36 is in `reference/adopt.md` §5. It is: "A goal that is data", lines 372 to 391, with the two `abbrev` lines of the note.
* MALL's table says note 1 is in `reference/adopt.md` §3. It is: "Where the logic has no weakening", lines 169 to 180, with both costs the note names.
* BrunnlerK's table says notes 35, 54 and 15 are in `SKILL.md`, "How a gate is run", items 1, 6 and 4. That section does not exist at `0e83910`. It was true when written (the section is in `SKILL.md` at `3186d6d`) and the rewrite removed it: what survives of notes 15 and 35 is in "Deciding, checking, stopping", items 4 and 5; note 54 has nothing left to apply to. BrunnlerK's file records the rewrite (note 67) and does not go back over its earlier tables. So a place cited in BrunnlerK's three tables is the place at the time; for thirteen notes the matter now stands elsewhere, and the table below gives where.
* One more, on a proposal: GLS's table says note 23 is in `reference/adopt.md` §1 and §7. It is: lines 60 to 63, and lines 598 to 601.

### Every note

| campaign | note | title | theme | state |
|---|---|---|---|---|
| BrunnlerK | 1 | Command unknown where sessions start | SKILL | applied: commit `07a5b2e` (README, "If the command is unknown"; `SKILL.md`, the first act, step 3, "the library") |
| BrunnlerK | 2 | Skill added mid-session is not loaded | SKILL | applied: commit `07a5b2e` (README); `SKILL.md`, "The command", third case |
| BrunnlerK | 3 | First act when the source is already read | REVIEWER | applied: `9cbfec1`; `SKILL.md`, "Where the session has already gone further" |
| BrunnlerK | 4 | First act does not ask leave to download | REVIEWER | applied: `3186d6d`; replaced by `28e3aa8`: `SKILL.md`, "Downloading" |
| BrunnlerK | 5 | Screening a planned statement in scratch Lean | STATEMENT | applied: `5337dd4`; `SKILL.md`, stage 0, step 3 |
| BrunnlerK | 6 | A fourth type for non-flat judgments | ENCODING | applied: `5337dd4`; `reference/explore.md` §13, the table's second row |
| BrunnlerK | 7 | Goal by rule: which form | STATEMENT | applied: `9cbfec1`; reworded in `1611566`: `SKILL.md`, "What a campaign proves" (form and route are decided in the plan) |
| BrunnlerK | 8 | Delivering a report from a worktree | REVIEWER | applied: `9cbfec1`; now `SKILL.md`, the first act, step 3, "pushing", and rule 6 |
| BrunnlerK | 9 | Cost log asks figures the operator lacks | RECORD | applied: `3186d6d`; `templates/cost-log.md`, "Sessions" |
| BrunnlerK | 10 | No exchange class for a reviewer's question | RECORD | applied: `5337dd4`; `templates/cost-log.md`, the class "question" |
| BrunnlerK | 11 | Download permission, the reviewer's answer | REVIEWER | applied with note 4; replaced by `28e3aa8` |
| BrunnlerK | 12 | Default folder `examples/` rejected | SKILL | applied: `d2ad48f`; `SKILL.md`, the first act, "the place"; `reference/explore.md` §1 |
| BrunnlerK | 13 | Letters that Lean reserves | ENCODING | applied: `d2ad48f`; `reference/adopt.md` §3, "The source's letters" |
| BrunnlerK | 14 | Direct statement over the class meant | STATEMENT | applied: `5337dd4`; `reference/adopt.md` §5; `templates/statements.md` |
| BrunnlerK | 15 | A gate answered in part | REVIEWER | applied: `3186d6d`; survives for a supervised campaign: `SKILL.md`, "Deciding, checking, stopping", 5 |
| BrunnlerK | 16 | Reviewer asks for a skill change mid-campaign | REVIEWER | applied: `9cbfec1`; `SKILL.md`, rule 7 |
| BrunnlerK | 17 | Plan's encoding table lacked the reason | ENCODING | applied: `5337dd4`; `templates/plan.md`, the table of choices |
| BrunnlerK | 18 | Skeleton script's header is out of date | SOURCE | applied: `5337dd4`; `reference/adopt.md` §1 |
| BrunnlerK | 19 | Stage run in the previous stage's session | SESSION | applied: `3186d6d`; replaced in `1611566` by rule 5, "Sessions are yours to arrange" |
| BrunnlerK | 20 | Figure's letters and the encoding's letters | ENCODING | applied: `5337dd4`; `reference/adopt.md` §3 |
| BrunnlerK | 21 | `#rules` prints names; table needs definitions | ENCODING | applied: `5337dd4`; `templates/rule-table.md`; `reference/adopt.md` §4 (the third section is now "What the table rests on") |
| BrunnlerK | 22 | A side condition that looks local | ENCODING | applied: `9cbfec1`; `reference/pitfalls.md`, 8 |
| BrunnlerK | 23 | Testing the family before its gate | ENCODING | applied: `5337dd4`; now `SKILL.md`, stage 1, step 4 (the worked derivations as terms, before anything follows the rules) |
| BrunnlerK | 24 | Printer writes a combining character | EXPLORER | applied: `5337dd4`; `reference/explore.md` §10 |
| BrunnlerK | 25 | S1 and S2 entered before the proof system | STATEMENT | applied: `9cbfec1`; `templates/statements.md` |
| BrunnlerK | 26 | Gate answered within the session | REVIEWER | finding; the note says there is nothing to change |
| BrunnlerK | 27 | S1 where a rule looks up its node | ENCODING | applied: `3186d6d`; `reference/explore.md` §13 |
| BrunnlerK | 28 | S2 proved in Adopt | ENCODING | applied: `5337dd4`; `reference/explore.md` §13, "prove S2 in Adopt" |
| BrunnlerK | 29 | `decide +kernel` on a step needs `toOption` | LEAN | applied: `3186d6d`; `reference/explore.md` §13 |
| BrunnlerK | 30 | Combining character in pinned messages | EXPLORER | applied with note 24 |
| BrunnlerK | 31 | The tactic's name becomes a keyword | ENCODING | applied: `3186d6d`; `reference/explore.md` §5 |
| BrunnlerK | 32 | Exercise whose first query is an error | EXPLORER | applied: `5337dd4`; `reference/explore.md` §10; `templates/Play.lean.txt` |
| BrunnlerK | 33 | `within` from the source's proviso | EXPLORER | applied: `5337dd4`; `reference/explore.md` §5 |
| BrunnlerK | 34 | Term syntax for non-flat judgments | ENCODING | applied: `5337dd4`; `reference/explore.md` §13 |
| BrunnlerK | 35 | A goal the reviewer sets overrides a gate | REVIEWER | applied: `dcf7a5b`, `3186d6d`; survives in `SKILL.md`, "Deciding, checking, stopping", 4 and 5 |
| BrunnlerK | 36 | A goal that is data: a named type | STATEMENT | applied: `3186d6d`; `reference/adopt.md` §5 |
| BrunnlerK | 37 | Goals that fall off the route taken | STATEMENT | applied: `5337dd4`; reworded in `1611566`: `SKILL.md`, stage 2, step 4 (such a goal ends OPEN) |
| BrunnlerK | 38 | Functions on derivations by matching, not `induction` | LEAN | applied: `3186d6d`; `reference/adopt.md` §6 |
| BrunnlerK | 39 | `Classical.choice` from a list lemma | LEAN | applied: `9cbfec1`; `reference/adopt.md` §6 |
| BrunnlerK | 40 | A characterisation as `simp` lemma loops | LEAN | finding; not applied (note 64: about Lean in general) |
| BrunnlerK | 41 | The screen served again as countermodel check | STATEMENT | finding; the reference was right |
| BrunnlerK | 42 | Deciding validity in the kernel | RUN | finding; covered by the change of note 48 |
| BrunnlerK | 43 | "Act independently": every gate lifted | REVIEWER | applied: `7d7f283`, `5337dd4`; superseded by the rewrite `1611566` |
| BrunnlerK | 44 | One relation instead of cases on positions | LEAN | applied: `3186d6d`; `reference/adopt.md` §6, the last part |
| BrunnlerK | 45 | One occurrence stated, several proved | LEAN | applied: `3186d6d`; `reference/adopt.md` §6 |
| BrunnlerK | 46 | `deriving` probed on every planned type | ENCODING | applied: `3186d6d`; `SKILL.md`, stage 0, step 3; `templates/plan.md`; `reference/explore.md` §13 |
| BrunnlerK | 47 | An estimate written as a fact | RECORD | applied: `9cbfec1`; `reference/pitfalls.md`, 11 |
| BrunnlerK | 48 | A proved, structural search: decide directly | RUN | applied: `3186d6d`; `reference/certify.md` §4 |
| BrunnlerK | 49 | A certificate as a term has limits | RUN | applied: `3186d6d`; `reference/certify.md` §5 |
| BrunnlerK | 50 | Measuring found a fault of the search | RUN | applied: `3186d6d`; `SKILL.md`, stage 3, step 4; `reference/certify.md` §5 |
| BrunnlerK | 51 | A library's syntax word is a keyword | ENCODING | applied: `3186d6d`; `reference/explore.md` §5; `reference/certify.md` §1 |
| BrunnlerK | 52 | What a column of times measures | RUN | applied: `3186d6d`; `reference/certify.md` §5 |
| BrunnlerK | 53 | Explore with no reviewer's test | REVIEWER | applied: `3186d6d`; now `SKILL.md`, stage 4, step 1 |
| BrunnlerK | 54 | Two gates need the reviewer's hands | REVIEWER | applied: `3186d6d`; superseded by `1611566` (the exercises are run by script; no such gates) |
| BrunnlerK | 55 | A suggested line takes the comment along | EXPLORER | applied: `5337dd4`; `reference/explore.md` §6 |
| BrunnlerK | 56 | A whole campaign in one session | SESSION | applied: `3186d6d`; now `SKILL.md`, rule 5, its last sentences |
| BrunnlerK | 57 | §13 said no public non-flat instance | SKILL | applied: `3186d6d`; `reference/explore.md` §13 names this instance |
| BrunnlerK | 58 | Status paragraphs seen and not changed | SKILL | finding; in part applied later (note 60) |
| BrunnlerK | 59 | Amended text not tried | SKILL | finding; no change asked |
| BrunnlerK | 60 | "Status" and worked instances updated | SKILL | applied: `d5c7f14`; `SKILL.md`, "The worked instances" and "Status" |
| BrunnlerK | 61 | Choices made while applying notes | SKILL | record; no change asked |
| BrunnlerK | 62 | New fragments not compiled | SKILL | finding; no change asked |
| BrunnlerK | 63 | The list of eighteen was short | SKILL | record; the eight left out were applied in `9cbfec1` |
| BrunnlerK | 64 | Notes still outside the skill | SKILL | record; no change asked |
| BrunnlerK | 65 | Pitfalls renumbered | SKILL | record of a change in `9cbfec1` |
| BrunnlerK | 66 | "Checked against `3fa25c0`" left unchanged | SKILL | finding; the line is unchanged at `0e83910` (`SKILL.md`, the last paragraph) |
| BrunnlerK | 67 | What the rewrite changed | REVIEWER | record of the rewrite: commit `1611566` |
| BrunnlerK | 68 | The rewrite not tested | SKILL | finding; since run on GLS, MALL and DILL (`SKILL.md`, "Status") |
| BrunnlerK | 69 | What the rewrite gives up | REVIEWER | finding; no change asked |
| BrunnlerK | 70 | The rewrite read cold; thirty findings | SKILL | applied in `1611566`; one finding in the text only (no test module in the compiled template) |
| BrunnlerK | 71 | `prove` built from one bullet | RUN | finding; it led to notes 72 to 75 |
| BrunnlerK | 72 | What the bullet did not say | RUN | applied: `0e83910`; `reference/certify.md` §5, "A judgment typed at a shell" |
| BrunnlerK | 73 | What a nested judgment needed at a shell | RUN | applied: `0e83910`; `reference/certify.md` §5 |
| BrunnlerK | 74 | Where K's and DILL's commands differ | RUN | finding; DILL's printed file is unchanged (note 75) |
| BrunnlerK | 75 | Changes asked for the `prove` paragraph | RUN | applied: `0e83910`; `reference/certify.md` §5. Not done: `leanReads` as a library function |
| GLS | 1 | Default version against the download permission | REVIEWER | applied: `28e3aa8`; `SKILL.md`, "Downloading" |
| GLS | 2 | A named paper that cannot be got | SOURCE | applied: `28e3aa8`, `b20b7aa`; `SKILL.md`, "Downloading" and rule 1 |
| GLS | 3 | First act in a session another started | SESSION | applied: `b20b7aa`; `SKILL.md`, the first act, step 4 |
| GLS | 4 | Times in the first entry | RECORD | applied: `b20b7aa`; `templates/decisions.md` |
| GLS | 5 | The source may be a formal development | SOURCE | applied: `b20b7aa`; `SKILL.md`, rule 1; `reference/adopt.md` §1 and §7 |
| GLS | 6 | A semantics the source does not have | STATEMENT | applied: `b20b7aa`; `SKILL.md`, "What a campaign proves" |
| GLS | 7 | Two routes to cut; which function | STATEMENT | applied: `b20b7aa`; `reference/adopt.md` §2 |
| GLS | 8 | Doc comment above a pinned message | EXPLORER | applied: `b20b7aa`; `reference/explore.md` §10 |
| GLS | 9 | Comments below a pattern line are taken | EXPLORER | applied: `b20b7aa`; `reference/explore.md` §6 |
| GLS | 10 | Order of display, screen, reading back | STATEMENT | applied: `b20b7aa`; `SKILL.md`, stage 2, steps 2 and 3 |
| GLS | 11 | Screens as a module of the build | STATEMENT | applied: `b20b7aa`; `reference/adopt.md` §5 |
| GLS | 12 | Pinned values from expectation, three times | RECORD | finding; the text held (reworded later from MALL's note 18) |
| GLS | 13 | `maxRecDepth` tried, and works | RUN | applied: `b20b7aa`; `reference/certify.md` §5 |
| GLS | 14 | Multi-line `Repr` is not always source | RUN | applied: `b20b7aa`; `reference/certify.md` §5 |
| GLS | 15 | macOS has no `timeout` | RUN | applied: `b20b7aa`; `reference/certify.md` §5 |
| GLS | 16 | The kernel is lazy, the producer not | RUN | applied: `b20b7aa`; `reference/certify.md` §5 |
| GLS | 17 | A frontier caused by the calculus | RUN | applied: `b20b7aa`; `reference/certify.md` §4 |
| GLS | 18 | Handing goals on by brief worked | SESSION | applied: `b20b7aa`; `SKILL.md`, rule 5; `templates/brief.md` |
| GLS | 19 | A commit took an agent's half-made file | SESSION | applied: `b20b7aa`; `SKILL.md`, rule 5 |
| GLS | 20 | Session ended under a running command | SESSION | finding; the note proposes nothing (two lines were added "in no note": rule 6, and stage 3, step 3) |
| GLS | 21 | What is owed when the prose arrives late | SOURCE | applied: `b20b7aa`; `reference/adopt.md` §1 |
| GLS | 22 | A download link returned an error page | SOURCE | applied: `b20b7aa`; `reference/adopt.md` §1 |
| GLS | 23 | Text extraction dropped the modal signs | SOURCE | applied: `b20b7aa`; `reference/adopt.md` §1 and §7 |
| GLS | 24 | An operator's definition was in the source | STATEMENT | finding; the text held |
| GLS | 25 | Reading back after the proof | STATEMENT | applied with note 10 |
| GLS | 26 | A code fault that looked like a frontier | RUN | applied: `b20b7aa`; `reference/certify.md` §4 |
| MALL | 1 | No form for a logic without weakening | ENCODING | applied: `94df876`; `reference/adopt.md` §3 |
| MALL | 2 | Permutation lemmas bring in `Classical.choice` | LEAN | applied: `94df876`; `reference/adopt.md` §6. Not done: the lemmas in the library |
| MALL | 3 | A scan with no text layer | SOURCE | applied: `94df876`; `reference/adopt.md` §7 |
| MALL | 4 | A source with no worked derivation | ENCODING | applied: `94df876`; `SKILL.md`, stage 1, step 4 |
| MALL | 5 | A move's name that is a keyword | ENCODING | applied: `94df876`; `reference/explore.md` §2 |
| MALL | 6 | The source's signs that core Lean uses | ENCODING | applied: `94df876`; `reference/adopt.md` §3 |
| MALL | 7 | "Told to the reviewer" has no time | RECORD | applied: `94df876`; `templates/decisions.md` |
| MALL | 8 | The default build compiles an agent's file | SESSION | applied: `94df876`; `SKILL.md`, rule 5 |
| MALL | 9 | An agent's name clashed in the namespace | SESSION | applied: `94df876`; `templates/brief.md` |
| MALL | 10 | A brief with the design in it | SESSION | applied: `94df876`; `SKILL.md`, rule 5; `templates/brief.md` |
| MALL | 11 | One construction for completeness and finite model | LEAN | applied: `94df876`; `reference/adopt.md` §2 |
| MALL | 12 | The reading back's remarks are findings | STATEMENT | applied: `94df876`; `reference/adopt.md` §7 |
| MALL | 13 | `omega` and a negation not unfolded | LEAN | applied: `94df876`; `reference/adopt.md` §6 |
| MALL | 14 | A certifier with no certificate | RUN | applied: `94df876`; `reference/certify.md` §3 |
| MALL | 15 | A pinned value from expectation, again | RECORD | applied with note 18 |
| MALL | 16 | The proved search is the slow one | RUN | applied: `94df876`; `reference/certify.md` §4 |
| MALL | 17 | Rule 6 and a certifier found missing | RUN | applied: `94df876`; `SKILL.md`, rule 6 |
| MALL | 18 | Pinned values typed, three times | RECORD | applied: `94df876`; `reference/pitfalls.md`, 11 |
| MALL | 19 | Lists as sets in the kernel | RUN | applied: `94df876`; `reference/certify.md` §3 |
| MALL | 20 | The tutorial as a pinned Markdown page | EXPLORER | applied: `94df876`; `SKILL.md`, stage 4, step 3; `reference/explore.md` §11. Not done: a status REFUTED in the library's script |
| MALL | 21 | A document written through a heredoc | RECORD | applied: `94df876`; `reference/pitfalls.md`, 12 |
| MALL | 22 | The cost log's columns | RECORD | applied: `94df876`; `templates/cost-log.md` |
| MALL | 23 | A refutation need not be a model | RUN | applied: `94df876`; `reference/certify.md` §3 |
| MALL | 24 | `#eval` of a search is no measurement | RUN | applied: `94df876`; `reference/certify.md` §5 |
| MALL | 25 | Where the time went after the page | SESSION | applied: `94df876`; `templates/brief.md`; `templates/cost-log.md`, "Time lost" |
| MALL | 26 | A result proved before its sources were read | STATEMENT | proposed (stage 2); not applied: written after the table of `94df876` |
| MALL | 27 | Tactics that reach for classical logic | LEAN | proposed (`reference/adopt.md` §6); not applied |
| MALL | 28 | An interpolant simplified as it is built | LEAN | finding; no change asked |
| DILL | 1 | The system is a fragment of the paper's | SOURCE | proposed (the first act); not applied |
| DILL | 2 | A source marked "do not cite" | SOURCE | proposed (the first act); not applied |
| DILL | 3 | A time typed before reading the clock | RECORD | proposed (`templates/decisions.md`, `templates/plan.md`); not applied |
| DILL | 4 | A notation screened without a tactic block | ENCODING | proposed (stage 0, step 3; `reference/adopt.md` §3); not applied |
| DILL | 5 | A refusal that came with an interrupt | SESSION | proposed ("The stops"); not applied |
| DILL | 6 | Silent well-founded recursion on a family function | LEAN | proposed (`reference/adopt.md` §6); not applied |
| DILL | 7 | A right rule's move names its formula | ENCODING | proposed (`reference/explore.md` §2); not applied |
| DILL | 8 | Five agents at once from one brief | SESSION | proposed (stage 2); not applied |
| DILL | 9 | Semantic cut elimination arrived first | STATEMENT | proposed (`reference/adopt.md` §2); not applied |
| DILL | 10 | What a goal stated as a type asserts | STATEMENT | proposed (`reference/adopt.md` §5); not applied |
| DILL | 11 | A commit cited before a rebase | RECORD | proposed ("The campaign folder"); not applied |
| DILL | 12 | Measurements with no budget | RUN | proposed (stage 3, step 3; `reference/certify.md` §5); not applied |
| DILL | 13 | A saturated set's soundness needs no model | RUN | proposed (`reference/certify.md` §3); not applied |
| DILL | 14 | Builds side by side | SESSION | applied during the run: `8285c44`, corrected by `d9716bd`; `SKILL.md`, rule 5; `templates/brief.md`; the cap on memory, `8cc17d6`, `reference/certify.md` §5 |
| DILL | 15 | Times typed ahead of the clock, five times | RECORD | proposed (`reference/pitfalls.md`, 11); not applied |
| DILL | 16 | Fetched sources lost at a restart | SOURCE | proposed (the first act); not applied |
| DILL | 17 | A sum typed, not computed | RECORD | finding; no change asked |
| DILL | 18 | The tutorial page begun before Run ended | EXPLORER | proposed (stage 4, step 3); not applied |
| DILL | 19 | The amended skill on its first run | STATEMENT | proposed (stage 2, step 4: the order of soundness and completeness); not applied |
| DILL | 20 | The tutorial's links and a rebase | EXPLORER | proposed (`reference/explore.md` §11); not applied |
| DILL | 21 | A sequent typed at a shell | RUN | applied: `3f435db`; `reference/certify.md` §5 |

## Question 7. The corpus driver, the fact-file generator, the goal delaborator: written again, or moved into a library?

**The driver and the generator were written again in each campaign. Neither is in a library.** The skill still says so: "The library has no such generator" and "There is no driver for this in the library" (`reference/certify.md`, lines 341 and 410), and no file for either is among those changed under `ProofTools/` or `LeanCertify/` since `2cf7044` (question 5).

| campaign | the driver: one executable, with the corpus beside it | the deadline and measuring scripts | the generator of facts, and its output |
|---|---|---|---|
| BrunnlerK | `calculi/BrunnlerK/Main.lean` (`ksearch`, 262 lines); `calculi/BrunnlerK/BrunnlerK/Corpus/Basic.lean` | `calculi/BrunnlerK/Corpus/measure.py`; `calculi/BrunnlerK/Corpus/prove_corpus.py` | the command `ksearch facts`; `calculi/BrunnlerK/BrunnlerK/Corpus/Facts.lean` (496 lines, generated, committed) |
| GLS | `calculi/GLS/Main.lean` (`glsrun`, 133 lines); `calculi/GLS/GLS/Corpus/Basic.lean` | `calculi/GLS/Corpus/measure.py`; `calculi/GLS/Corpus/measure_set.py` | `glsrun facts`; `calculi/GLS/GLS/Corpus/Facts.lean` (163 lines) |
| MALL | `calculi/MALL/Main.lean` (`mallrun`, 164 lines); `calculi/MALL/MALL/Corpus/Basic.lean` | `calculi/MALL/Corpus/measure.py`; `calculi/MALL/Corpus/measure_model.py` | `mallrun facts`; `calculi/MALL/MALL/Corpus/Facts.lean` (327 lines) |
| DILL | `calculi/DILL/Main.lean` (`dillrun`, 395 lines); `calculi/DILL/Corpus/SatMain.lean`; `calculi/DILL/DILL/Corpus/Basic.lean` | `calculi/DILL/Corpus/measure.py`; `calculi/DILL/Corpus/measure_sat.py` | `dillrun facts`. Its output was written to `Corpus/out/run/Facts.lean`, a folder that git ignores, and is "not kept" (`calculi/DILL/campaign/measurements.md`, lines 134 to 136). DILL has no committed facts file |

The four executables have the same four commands (`facts`, `status`, `run`, `cert`), and small functions are carried from one to the next by copy: `certSize` is defined in the same words in `Main.lean` of BrunnlerK, GLS and MALL, and `showFlat`, which prints a script on one line, in those of GLS and MALL. One piece of `LeanCertify` was looked at for the purpose and not used: the namespace `Certify.Cli`, at the end of `LeanCertify/Decider.lean`, has a `main` that needs a registry of tools "which no campaign has", so only its four exit codes were taken (BrunnlerK note 72, item g).

Two more things were written more than once and are not in a library:

* **the reader of a judgment typed at a shell**: `calculi/DILL/DILL/Parse.lean` and `calculi/BrunnlerK/BrunnlerK/Parse.lean`, the second built from the skill's one bullet and then compared with the first (BrunnlerK notes 71 to 75). GLS and MALL have none (DILL note 21);
* **the permutation lemmas**: three copies (question 5).

**The goal delaborator was moved into the library before the first campaign, and no campaign wrote one.** Commit `bbdae58` (2026-11-22) added `delabAtt`: "a goal `Att S o j` shown as its judgment by the instance's `showJudg`, for every instance" (`ProofTools/Explore/Tactic.lean`, line 221). The skill has said since the draft that "there is no delaborator to write" (`reference/explore.md`, lines 271 to 277). Each campaign's instance gives `showJudg` and nothing more: `calculi/BrunnlerK/BrunnlerK/Tactic.lean`, line 123; `calculi/GLS/GLS/Tactic.lean`, line 87; `calculi/MALL/MALL/Tactic.lean`, line 130; `calculi/DILL/DILL/Tactic.lean`, line 168. A search for `delab` under `calculi/` finds nothing. One wish of the same kind was left unserved: a goal shown as a tree in the infoview, for nested sequents (`calculi/BrunnlerK/campaign/report-5-2026-11-23.md`, lines 33 to 36).

## Question 8. Cost by stage

No log records requests, the tokens of the operator's own session, or money: each writes "not known" (BrunnlerK note 9; `templates/cost-log.md`, lines 11 to 19). What is recorded is the clock, the lines of Lean, and, for the three later campaigns, the tokens and durations that the environment reported for agents when each ended.

**BrunnlerK** (`cost-log.md`, lines 8 to 16 and 55 to 62). One session ran every stage; no agent. Times from `date` and the session's transcript; lines added per row.

| stage | by the clock (GMT, 2026-11-23) | Lean lines added |
|---|---|---|
| Survey | 07:23 to the first gate note at 07:57 (34 min); again 09:06 to 09:12; the plan passed at 09:36 | 0 |
| Adopt | 14:07 to 14:19, to the rule table's gate; 15:45 to 15:55, after the signature | 631, then 976 |
| Prove | 17:30 to 18:00, of which 17 min at the statements' gate; 18:11 to 18:33 | 1 919, then 2 135 |
| Run | 18:32 to 18:44 | 479 by hand, 496 generated |
| Explore | 18:43 to 18:47 | 319 |

From the command to the closing report: 11 h 24 min, of which "a little over two hours of work" (`gates.md`, lines 480 to 483). Waiting on builds: under a minute to about three minutes a stage. 6 459 lines of Lean by hand.

**GLS** (`cost-log.md`, lines 9 to 19 and 34 to 64). One session, started cold from a brief, and five agents. Times from `date` and the commits; lines from `git diff --stat`.

| stage | who | by the clock (GMT, 2026-11-25) | Lean lines added | tokens |
|---|---|---|---|---|
| the first act | the session | 08:46 to 08:56, 10 min | 0 | not known |
| Survey | the session | 08:56 to 09:08, 12 min | 0 | not known |
| Adopt | the session; a cold reader | 09:08 to 09:24, 16 min, 10 of them lost to a command that waited on its input | 961 | not recorded |
| Prove, goals 1 to 3 | the session; a cold reader | 09:24 to 09:35, 11 min | 1 710 | not recorded |
| Prove, goals 4 to 6 | an agent, from a brief | 09:38 to about 09:53, 907 s by its report | 742 | 225 816, by its report |
| Run and Explore | the session | 09:35 to about 09:57, 22 min | 1 599 | not known |
| (nothing running) | | 09:57 to 13:14 | | |
| the comparison with the prose, one more goal, a repair, the closing page | the session, resumed; two cold readers | 13:14 to 13:31 | 849 added, 22 removed | not recorded |

Working time to the end of Explore: 71 minutes. 5 103 lines of Lean in 35 files at the end.

**MALL** (`cost-log.md`, lines 14 to 60). One session, cold, and five agents before the closing page. Each stage's end is the time of its last commit; the Lean lines are the total at that commit, not what the stage added.

| stage | agents | by the clock (GMT, 2026-11-26) | Lean lines at the stage's last commit | the agents' tokens and own time |
|---|---|---|---|---|
| Survey | a1, the literature | 09:46 to 10:04, 18 min | 0 | 215 326; 575 s |
| Adopt | a2, the second transcription | 10:04 to 10:18, 14 min | 1 734 | about 85 000; 67 s |
| Prove | a3 and a4, two goals; a5, the reading back | 10:18 to 10:32, 14 min | 4 173 | about 152 000, 112 000 and 88 000; 516 s, 243 s, 152 s |
| Run, Explore | none | 10:32 to 11:00, 28 min | 6 051 | |
| the closing documents | none | 11:00 to 11:06 | the same | |

From the task to the closing page: 80 minutes by these rows (the skill's "Status" has 81, from 09:45: `SKILL.md`, line 270). The five agents: about 652 000 tokens and 26 minutes of their own time. After the page, at the reviewer's word: 11:39 to 14:11, of which about 45 minutes in tool calls that waited on a hook, 80 minutes with the process not running, and about half an hour of work; one agent for the tutorial, 376 105 tokens. Then interpolation, 15:06 to 15:22, with three agents: 164 029, 320 787 and 88 477 tokens.

**DILL** (`cost-log.md`, lines 12 to 42 and 98 to 113). One session, from a brief, and twelve agents. The stages overlap, so the times are those of the commits that begin and end each; an agent's start is from `date` and its end is computed from the duration reported; the Lean lines are counted from the files of each stage.

| stage | agents | by the clock (GMT, 2026-11-26) | Lean lines | the agents' tokens |
|---|---|---|---|---|
| Survey | 1, the literature | 14:47 to 14:59, 12 min | 0 | 327 794 |
| Adopt | 2, the second transcription; 9, the tests and the exercises | 15:13 to 15:42, beside Prove from 15:20 | 2 823 in eight files | 106 261 and 274 539 |
| Prove | 3, 4, 5, 7, 8, the proofs; 6, the reading back | 15:20 to 15:33, 13 min | 3 012 in eleven files | 886 676 in all |
| Run | 10 and 11 | 15:29 to 16:27, of which 31 min lost | 2 216 in eleven files, and 368 of Python | 360 037 for one; the other's not reported |
| Explore | 12, the tutorial page | 15:34 to 16:33, of which the same 31 min | 2 294 in four files | 479 615 |

From the brief to the closing page: 1 h 46 min, of which about 43 minutes in which nothing or one thing ran. 10 345 lines of Lean, 3 439 of them tests and generated pins. The eleven agents that reported: 2 434 922 tokens.

**Side by side**, with what each figure is:

| | BrunnlerK | GLS | MALL | DILL |
|---|---|---|---|---|
| sessions; agents before the closing page | 1; 0 | 1; 5 | 1; 5 | 1; 12 |
| from the command to the closing page | 11 h 24 min | 4 h 45 min (08:46 to 13:31) | 80 min | 1 h 46 min |
| of which not working | more than nine hours, most of it waiting at gates | 3 h 17 min idle | none recorded before the page | about 43 min |
| Lean lines at the close | 6 459 by hand, 496 generated | 5 103 | 6 051 | 10 345 |
| messages of the reviewer in the log, before the close | 16 | 3 | 0 | 2 rows; more in `decisions.md` |
| tokens recorded | none | 225 816, one agent of five | about 652 000, five agents | 2 434 922, eleven agents of twelve |
| requests, the session's own tokens, money | not known | not known | not known | not known |

**The logs are not comparable in these ways.**

* **The unit of a row.** BrunnlerK has a row for each part of a stage between two words of the reviewer. GLS has a row for each stretch of one session, with the first act apart and Run joined to Explore. MALL has a row for each stage, with Run and Explore joined. DILL has a row for each stage, and the stages overlap, so their times do not add up to the whole.
* **The clock measures different things.** BrunnlerK's 11 h 24 min is mostly waiting at gates. GLS's includes a session that was not running. DILL's includes a restart of the machine. Only MALL's is close to working time.
* **Lean lines.** Added per row (BrunnlerK, GLS), the total at a commit (MALL), counted from the files of a stage (DILL). Tests and generated files are inside the figure in some rows and apart in others.
* **Tokens.** None for BrunnlerK. For the others, the agents only, as the environment reported them, with some figures approximate and two agents unreported. The operator's own session has no figure in any campaign. So the totals rise from GLS to DILL at least in part because more of the work was handed to agents, where it is counted.
* **The operator's starting point.** Not cold in BrunnlerK; cold in the others, each from a brief written by another session whose own cost is in no log.
* **What a campaign contained.** DILL wrote the tutorial page inside the campaign; MALL wrote it afterwards; GLS's was written by another session. BrunnlerK has no `tutorial.md`.

## What the record cannot answer

* **What the checks of a transcription can catch.** No error of transcription occurred in four campaigns, so `#rules` beside the figure, the worked derivations, the second transcription, the reading back, and soundness with completeness have each been run and none has been seen to fail. A campaign on a source with a known trap, or a transcription with a fault planted in it, would settle it.
* **Whether the gates would have found an error.** One campaign ran under them, and it had none to find.
* **Whether a fresh session for each stage works** (rule 5 as drafted). It was never tried.
* **Whether a person can use the explorer.** No person has typed the exercises or worked through a tutorial in any campaign (`calculi/GLS/campaign/cost-log.md`, lines 84 to 85; `calculi/BrunnlerK/campaign/cost-log.md`, lines 142 to 143).
* **Three parts of the skill that no campaign has exercised**: validity as what holds (proposal c); the two shorter paths with `templates/record.md`; the named hypothesis for a case that will not close (proposal g). Nor has a campaign ended with a goal OPEN.
* **What proposal j's list was, and which library commits were R2, R3 and R5.** The record has "stage R4" once and nothing else.
* **The design session's text before the draft was committed**: whether the Lean skeletons were uncompiled then, and what the cold read of conclusion 8 changed.
* **Money, requests, and the tokens of any operator's own session.** The usage reports of the application would settle it; the logs leave the columns for the reviewer to fill, and none is filled.
* **Whether DILL's eighteen proposals are right.** They are not applied and no later campaign has tested them. The skill as amended after DILL has not been run either.
* **Whether the cold readers are independent of the operator.** They are the same model; the record has no reading by a person or by another model to compare.
* **Whose word asked for the library change of commit `906e2fa`.**
* **The state of what lies outside this repository**: the other copies of the audit commands, the installed copy of the `lean-certify` skill, the script that writes a paper's skeleton.
* **Whether the libraries and the four calculi build on a Lean later than v4.31.0.** The lakefile records that the zipper did not on v4.33.0; nothing since.
* **Two small disagreements inside the record**: MALL's cost log has no word of the reviewer while its decisions record several after the closing page; MALL's run is 81 minutes in the skill and 80 by the cost log's rows. And one thing left standing: the skill's last paragraph says its text was checked against the library at `3fa25c0`, and nothing records a check against a later commit (BrunnlerK note 66).

## Received after this page was written

From the design session, which read the page at commit f4f9acb (2026-11-26). Its statements are about its own files, which this sweep did not read; they are recorded here as its account.

* **"The draft" on this page is the skill's first commit, `ce28bcc`, and that is not the design session's last text.** Between the two, another session revised the draft in four commits on the evening of 2026-11-22: it added the command and its target, the first act, the standing list and "What a campaign proves"; repaired the text from a second cold read and compiled the two Lean skeletons; and applied the list of proposal j (the passages that the planned library stages would make out of date). So, in question 1: row j's list was used, not lost, which is why no committed version has it; the skeletons were uncompiled in the design session's text and compiled before `ce28bcc`; "the section survived word for word" and "there is no delaborator to write" are true of `ce28bcc`, not of the design session's text, which listed nine things not built and told the operator to write a delaborator.
* **Which library commits were the stages R2 to R5** (question 5; the sixth item of "What the record cannot answer"): R4, soundness of the moves into any sort and the map out, `b7b70d4`, `178683b`, `c475963`; R3, a tree of moves as a certificate, `6ee81d3`, `24d9d85`; R2, the attempt drawn inside the build tactic and the walker as a tactic block, `bbdae58`; R5, a change at the focus and a session of commands, `fe8b4e7`, with `b2f2cdb` the reuse asked of it; `05ddc63` is the rose-tree zipper carried into the library.
* **Four proposals of the design session for the collation of the method notes**, untested: a planted-fault test of the checks of meaning (copies of one adopted family with one fault each, to tabulate which check catches which fault, since none has yet been seen to fail); one list of what the campaigns asked of the libraries, each with a decision, since rule 7 records such needs and none has landed while the same code is written again in each calculus; a statement, as information and not as a gate, of the form of "valid" chosen and the form rejected, at the end of the Survey; and the operator's own tokens in the cost logs.
