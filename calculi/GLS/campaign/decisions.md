# GLS: the decisions

One entry for each choice the operator made, in order, and one for each
word of the reviewer. Written when the choice is made, not afterwards.
The closing page lists the entries by what they cost to reverse, the
costliest first.

The cost to reverse is one of:

* **little**: a name, a letter, the place of a file;
* **a stage**: the form of a goal, an encoding, which results are goals;
* **the campaign**: the source, the system, what "holds" means, the
  axiom policy.

## 2026-11-25 08:56 GMT. The target

*The first entry, and the one record of what it fixes: the other files of
the folder point here.*

* **The command's words**: "the sequent calculus GLS for provability
  logic GL, from Goré, Ramanayake and Shillito (TABLEAUX 2021); you may
  download the paper". They reached the operator in a brief written by
  another session, which copied them word for word; the skill's file was
  opened as a file, not run as a command.
* **The paper and its version**: R. Goré, R. Ramanayake, I. Shillito,
  *Cut-Elimination for Provability Logic by Terminating Proof-Search:
  Formalised and Deconstructed Using Coq*, TABLEAUX 2021, LNCS 12842,
  pp. 299-313, DOI 10.1007/978-3-030-86059-2_18. The command names it.
  **The version to be read** is, by the skill's default (a thesis before
  a conference paper), the fuller account by one of its authors:
  I. Shillito, *New Foundations for the Proof Theory of Bi-Intuitionistic
  and Provability Logics Mechanized in Coq*, PhD thesis, Australian
  National University, 2023, DOI 10.25911/8F2P-AA86, the part on GLS.
  Its abstract says it obtains cut elimination for GLS. Whether the
  thesis states the same system as the paper is checked in the Survey;
  where they differ, the paper's system rules, since the command names
  the paper.
  Not taken:
  - a journal version of the paper: none found (searched: DBLP's record
    `conf/tableaux/GoreRS21`, Semantic Scholar, the Groningen research
    portal, the author's publication page `ianshil.github.io`);
  - an arXiv preprint: none found (the same places, and two web
    searches);
  - J. Brighton, *Cut elimination for GLS using the terminability of
    its regress process*, J. Philos. Logic 45 (2016): the proof the
    paper starts from, for a set-based GLS; another paper, not a version;
  - Goré and Ramanayake, *Valentini's cut-elimination for provability
    logic resolved*, Rev. Symb. Logic 5 (2012): another proof, another
    paper.

  Could not be got on 2026-11-25: **the paper itself**. Springer's page
  shows the abstract and the references and no more ("a preview of
  subscription content"), in the reviewer's own browser too. The open
  copy that searches list, `publik.tuwien.ac.at/files/publik_299043.pdf`,
  refuses connections (tried four times, from two tools). The Internet
  Archive answered "temporarily offline". TU Wien's present repository
  (reposiTUm) answers 416 to a search from here.
* **The system**: GLS, under the paper's own name (the abstract: "the
  standard set-based sequent calculus GLS for modal provability logic
  GL", of which the paper argues for a formulation with multisets). The
  base system, in the form the source proves cut admissibility for.
  Left out: Brighton's auxiliary calculus RGL and its regress trees; any
  variant of GLS that the source defines for proof search (the authors'
  Coq files name one, PSGLS), except as far as the Run stage needs a
  terminating search, which is then the source's; the other calculi of
  the thesis (bi-intuitionistic logic; GL4ip for the intuitionistic
  provability logic iGLL).
* **The results aimed at**: of the standing list, entry 1, cut
  elimination (the paper's abstract: "a direct proof of
  cut-admissibility"); entry 2, the finite model property, which
  appears to hold of the logic GL and to be proved elsewhere, not for
  this calculus (the Survey says where). Entries 3 to 7 appear not to
  apply (no derivability from hypotheses in a sequent calculus of this
  kind, no term calculus, a classical logic); the Survey looks, and says
  where. Beyond the list: the termination of backward proof search (the
  paper's title), the admissible structural rules on the way to cut,
  and soundness and completeness, where a source proves them.
* **The path**: adopted from the paper. The calculus was not found in
  Lean in this repository (`calculi/` holds Brünnler's K only).
* **The place and the name**: `calculi/GLS/` of the library
  `proof-tools`, core Lean only; the Lean module name `GLS`; this folder
  is `calculi/GLS/campaign/`.
* **The library**: the checkout the session was started in, a worktree
  of `proof-tools` at commit `818483e`; the remote's `main` is at
  `818483e` (`git ls-remote origin refs/heads/main`, 2026-11-25 08:46):
  the same commit, nothing to update. It has
  `ProofTools/Explore/Cert.lean` and `ProofTools/Explore/Session.lean`.
* **The source's files**: no LaTeX archive exists to fetch (no arXiv
  version). The paper's PDF could not be got (above). The thesis is one
  file, "Ian Shillito_Thesis_2023.pdf", 1.41 MB, in ANU's collection
  "Open Access Theses". The reviewer's words allow the download of "the
  paper"; the thesis is another file, and this operator's environment
  asks the reviewer's word for each file. **Asked on 2026-11-25 08:55**
  (the first act's one question; "Stops", below). Read meanwhile, as web
  pages and without a download: Springer's abstract and reference list;
  the authors' Coq formalisation, `github.com/ianshil/CE_GLS` (commit
  `3dd8619`, MIT licence), which the paper is about.
* **Pushing**: to `main` of `fairflow/proof-tools`, with
  `git push origin HEAD:refs/heads/main`, fast-forward, by the standing
  instruction in the project's memory ("proof-tools commits go to main",
  the reviewer's words of 2026-11-23: "merge to main as there's no
  current need for branching"). The session's own branch
  (`claude/gls-campaign-0ee711`) is never pushed (the global rule on
  ephemeral branches). The closing page reaches the reviewer by that
  push, and also as a private page (the reviewer cannot open a file in a
  worktree).
* **Not touched**: every tracked file outside `calculi/GLS/` (rule 7);
  the main checkout `/Users/matthew/Lean/Sources/proof-tools`; other
  sessions' worktrees. Only the reviewer contacts the source's authors.
* **Told to the reviewer**: 2026-11-25 08:56, in the session, in full:

  > GLS campaign begun. The paper: Goré, Ramanayake and Shillito,
  > TABLEAUX 2021 (DOI 10.1007/978-3-030-86059-2_18); the version to be
  > read is the fuller account in Shillito's thesis (ANU, 2023), since
  > the paper is paywalled and its open copy is unreachable today. The
  > system: GLS, without Brighton's RGL and without the other calculi of
  > the thesis. Aimed at: cut admissibility; the termination of backward
  > proof search; the admissible structural rules; soundness and
  > completeness where a source proves them; the finite model property
  > appears to be a result about the logic, proved elsewhere. The place:
  > `calculi/GLS/` of proof-tools, pushed to `main`. One question, to
  > the session that started this one: may the thesis's PDF (1.41 MB,
  > ANU Open Access Theses) be downloaded?
* **Before this text was read**: nothing of the source. The brief that
  started the session says its writer has not read the paper.

## 2026-11-25 09:07 GMT. Stage 0: the transcription is made from the authors' Coq files while the prose is not read

* **Decided**: Q1 of the plan, and the rule table of Adopt, are written
  from `GL/GLS_PSGLS_calcs.v` of `ianshil/CE_GLS` (commit `3dd8619`),
  by file and line. The comparison with the figure and the prose (the
  thesis, or the paper) is owed, and is made when one of them can be
  read; every difference is then entered in the rule table, and what
  rests on a rule that changes is built again.
* **Not taken**: to end the turn and wait for the download. The skill's
  stop says to go on with what does not rest on the answer; nearly
  everything rests on the rules, and the Coq file states them without
  ambiguity. To transcribe from memory of the paper: rule 1 forbids it.
* **Why**: the paper's theorems are theorems about these Coq
  definitions ("By formalising the GLS calculus and the proofs in Coq",
  the abstract). A figure in prose can differ from them in notation and
  in what it leaves implicit; where it does, the Coq definition is what
  was proved.
* **Rests on it**: the plan's Q1; the rule table; the family.
* **Cost to reverse**: the campaign, if the prose shows another system;
  little, if it shows the same one in other notation. Doubt: the second
  transcription (`reference/adopt.md` §7) asks for a cold reader given
  "the figure, and the prose around it". Until the prose is read the
  cold reader is given the Coq file.

## 2026-11-25 09:07 GMT. Stage 0: what holds is the family

* **Decided**: the moves of the explorer are sound for the family `GLS`
  as transcribed, into `Type` (the method's default for an adopted
  calculus). Validity is a goal of Prove.
* **Not taken**: validity as what holds: nothing would then tie `step`
  to the transcribed rules except what is proved separately.
* **Why**: a derivation of the explorer maps out to the calculus's own
  derivation, as data; the search and cut admissibility are functions on
  such derivations.
* **Rests on it**: S1, S2, the certifiers of Run.
* **Cost to reverse**: the campaign.

## 2026-11-25 09:07 GMT. Stage 0: what "valid" means

* **Decided**: `Valid (Γ ⇒ Δ)`: in every model whose relation is
  transitive and conversely well-founded and in which every formula is
  true or not true at every world, at every world: if every formula of
  `Γ` is true then some formula of `Δ` is. Truth of `□A` at `w`: `A` at
  every `v` with `w R v`.
* **Not taken**: every model, two-valued or not: screened in scratch, it
  gives `P ∨ ¬P` for every proposition `P` from the validity of
  `⇒ p, p → ⊥`. The indirect form (no model refutes the sequent): the
  reviewer's recorded preference is the direct form over the class the
  literature means (the project's memory, 2026-11-23). Finite models
  only: completeness would be the same theorem, soundness a weaker one.
* **Why**: it is the classical notion under excluded middle. Screened:
  GLR preserves it, with no axiom beyond `propext`, by induction along
  the converse of the relation.
* **Rests on it**: goals 1 to 3 of the plan; the no side of Run.
* **Cost to reverse**: the campaign. Doubt: **the semantics is not in
  the source's Coq files.** It is the standard one for GL (transitive,
  conversely well-founded frames), stated here by the operator; the
  closing page lists it among the definitions to read. (13:21: the
  thesis has it, Definitions 12.2.2 and 12.2.3, p. 168, in these
  words. What remains the operator's own: the restriction to two-valued
  models, and truth of a sequent with several formulas on the right.)

## 2026-11-25 09:07 GMT. Stage 0: the axiom policy

* **Decided**: every theory file within `[propext, Quot.sound]`.
* **Not taken**: `Classical.choice` allowed in the completeness file.
* **Why**: the countermodels are finite trees given as data, and
  validity is over two-valued models.
* **Rests on it**: every theory file's last line.
* **Cost to reverse**: the campaign (to tighten later is a rewrite; to
  loosen is one line).

## 2026-11-25 09:07 GMT. Stage 0: the encoding

* **Decided**: a sequent is a structure of two lists. A rule finds its
  principal formula by membership and its premises remove one
  occurrence of it (`List.erase`). The boxed part of GLR is one
  function `xbox` on the antecedent. Moves name a rule by its formula.
  Two families, `GLS` and `PSGLS`. The height is a function on
  derivations.
* **Not taken**: the Coq form with places in lists (`++` in every
  conclusion: a computed index, and exchange at the cost it had in Coq,
  140 000 characters); a principal formula kept in the premises (another
  calculus: the number of implications no longer falls); one family
  with a Boolean parameter.
* **Why**: the plan, "Choices of encoding". Each is a divergence of
  representation, entered in the rule table.
* **Rests on it**: every Lean file.
* **Cost to reverse**: a stage (Adopt and all of Prove).

## 2026-11-25 09:07 GMT. Stage 0: which results are goals, and the route to cut

* **Decided**: the goals of the plan, in its order: soundness;
  completeness as data, with the finite model property and
  decidability; cut admissibility; the source's structural theorems
  with heights; the two systems derive the same sequents; cut
  admissibility a second time by the source's induction.
  **Soundness, completeness and the finite model property are goals
  although the source's Coq files have no semantics**: the method wants
  them as its fourth check of meaning, Run wants countermodels, and
  entry 2 of the standing list is then proved for this calculus and not
  only cited.
  **Cut admissibility is proved first through the semantics**, and then
  by the source's route.
* **Not taken**: the source's route only: it is the longer (210 000
  characters of Coq without exchange) and the semantic route's
  ingredients are wanted anyway. The semantic route only: it ignores
  the two given derivations, which is what the paper's abstract holds
  against an earlier proof.
* **Why**: `reference/adopt.md` §1 ("the shorter one is equally
  published"), and stage 2, step 4.
* **Rests on it**: `statements.md`.
* **Cost to reverse**: a stage. Doubt: that the semantic route is "in
  the literature" for GLS rests on a search result's report of Sambin
  and Valentini 1982, which was not read.

## 2026-11-25 09:38 GMT. Stage 2: goals 4 to 6 handed to a fresh agent

* **Decided**: the source's syntactic route (the structural theorems
  with heights, the two systems, cut by the source's induction: S11 to
  S19) is given to a fresh agent, started by the operator, with
  [brief-2-1.md](brief-2-1.md), which holds the operator's design of
  each proof. The operator goes on with stage 3 meanwhile, in the same
  checkout: the agent creates five new files and changes no other.
* **Not taken**: to write them in this session, one after another: the
  session has read 400 000 characters of its own history, and stage 3
  does not rest on these goals (rule 5).
* **Why**: the statements are fixed in `GLS/Semantics.lean`; the kernel
  checks what comes back, so the agent need not be trusted.
* **Rests on it**: S11 to S19.
* **Cost to reverse**: little.

## 2026-11-25 09:39 GMT. Stage 3: the producers and the certificates

* **Decided**: one producer, the search of `GLS/Search.lean` compiled,
  with what it returns checked before it is handed on. Certificates: for
  a derivation its tree of moves (the plan's certificate of record),
  read off the derivation the search returns; against derivability and
  against validity, the finite tree the search returns, checked by
  `Seq.refutedAt` (certifiers of our own: S21). Level 3: S22. The kernel
  running the search itself (`decide +kernel` on `Valid s`) is measured
  beside the certificates.
* **Not taken**: a second, faster search that is not proved: the
  measurements decide whether one is wanted. A certificate of the
  search's own.
* **Why**: who relies on the answers (the plan, Q3): the campaign's
  corpus, and a user of the explorer who wants the countermodel of a
  goal no move closes.
* **Rests on it**: `GLS/Run.lean`, the corpus, `measurements.md`.
* **Cost to reverse**: little.

## 2026-11-25 09:48 GMT. Stage 3: a certifier over sets

* **What the measurements showed** (`measurements.md`): the producer
  answers `□p → □¹⁷p` in 8 ms, `□p → □²¹p` in 132 ms, `□p → □²⁵p` in
  2.2 s, and not `□p → □²⁹p` in 20 s: its time doubles with each box.
  The same for the non-theorem `□ⁿ⁺¹⊥ → □ⁿ⊥`. The cause is the rule and
  not the order of the search: the premise of GLR holds `B, □B` for
  every boxed formula of the antecedent, counted with repetitions, and
  a formula that is both a `□B` and the body of a `□□B` is there twice
  after one GLR, and so on: the antecedents double. A derivation of
  GLS, as a term of `Fam`, holds these sequents, and the compiled
  search builds them and looks through them. (The kernel does not: it
  evaluates lazily, and checked the tree of moves of `□p → □²⁵p` in
  under a second, since no step of that tree looks beyond the head of
  an antecedent. The kernel running the first search does look through
  them, and was cut off at `n = 16`.)
* **Decided**: a second certifier, `setCert`, for the proposition "there
  is a derivation in GLS" (not for the derivation as data): trees of
  moves checked by a `step` that removes the repeated formulas of each
  premise. A search over sets as its producer, not proved; and a second
  decision of derivability that runs it, checks its answer, and falls
  back on the first. The statements: S23, entered before the proofs.
  The first search, the first certifiers and every statement are as
  they were.
* **Not taken**: to change `search` (stage 3, step 4, allows a repair
  that changes no statement): the search returns a derivation in `Fam`,
  and that object is as large as it is; `search` is also what the
  theorems of goals 2 and 3 are about. To leave the frontier at
  `n = 28`: the answers that matter to a user (is it derivable; if not,
  where is it false) do not need the derivation as data.
* **Why**: a sequent less its repeated formulas is derivable exactly if
  the sequent is (weakening one way, which is all soundness needs).
* **Rests on it**: `GLS/SetSearch.lean`; `Fam.wk` of
  `GLS/Structural.lean` (goal 4).
* **Cost to reverse**: little.

## 2026-11-25 13:14 GMT. A word of the reviewer

* **The words**: "yes you can download the thesis and any other
  materials to which you have online access that may assist you in the
  formalisation." (typed by the reviewer in the operator's session,
  which had ended at about 09:57 with a command still running; this is
  the next message after it).
* **What it is**: an answer at a stop (the one question of the first
  act, asked at 08:55), and wider than the question: every source that
  can be reached may be fetched.
* **What it changes**: the thesis is fetched and read; the comparison
  of the rules with a figure in prose, owed since the Survey, is made
  (the rule table, "The comparison with the figure in prose"); the
  plan's Q1 and the skeleton get the printed numbers. What was built on
  the Coq files is built again only where the comparison finds a
  difference: the entry after this one says what it found.

* **The file fetched**, at 13:17: "Ian Shillito_Thesis_2023.pdf",
  1 481 279 bytes, from the Australian National University's open
  repository
  (`openresearch-repository.anu.edu.au/server/api/core/bitstreams/0bbb4f8c-19b1-4e28-96e8-4ca795c863bf/content`;
  DOI 10.25911/8F2P-AA86). Kept in a folder of its own outside the
  repository; read as text and as images of its pages; nothing in it
  was run. Not in the repository. Nothing else was fetched: the paper
  of 2021 is behind the publisher's paywall and its open copy
  (`publik.tuwien.ac.at`) did not answer.

## 2026-11-25 13:21 GMT. The comparison with the prose: what it found

* **Decided**: nothing built on the Coq files is built again. The
  thesis's Figure 12.1 and its definition of PSGLS (pp. 171, 178) state
  the rules that `GLS_PSGLS_calcs.v` states; the comparison is in the
  rule table, row by row. The decision of 09:07 (to transcribe from the
  Coq files) is thereby settled at its lower cost.
* **What the thesis adds**, each taken in: Theorem 12.7.2, cut
  elimination from GLS + (cut), a goal by rule (the entry below); a
  source for goal 5 (Proposition 12.6.1) and for the decidability of
  provability in GLS (Corollary 12.6.1); the semantics, which the
  operator had stated from the logic's usual presentation, is the
  thesis's Definitions 12.2.2 and 12.2.3; four worked derivations
  (Examples 12.4.1, 12.4.2), now terms of the family.
* **Not taken**: to make the thesis's own formulation of termination
  (`mhd`, Theorem 12.6.1) a goal after all: S9 states the termination,
  and the cut by the source's induction (S19) was made on the measure
  itself, so nothing rests on `mhd`.
* **Doubt**: the paper itself (TABLEAUX 2021) has still not been read.
  The command names it. What stands in for it: its abstract, the Coq
  development it is about, and the thesis chapter by one of its
  authors, which says of itself that it presents that work. If the
  paper's figure differs from the thesis's, the campaign has not seen
  it.
* **Cost to reverse**: little.

## 2026-11-25 13:21 GMT. Stage 2: cut elimination from GLS + (cut) is a goal

* **Decided**: S24, the thesis's Theorem 12.7.2: a third family,
  `FamCut`, the five rules of GLS and the additive cut as the thesis
  prints it (p. 171); and a function from its derivations to those of
  `Fam`. Proved twice, as cut admissibility is: with the source's
  construction at each cut (`cutElimination`), and with the search at
  each cut (`cutEliminationBySearch`).
* **Not taken**: to leave entry 1 of the standing list at
  admissibility, which is what the Coq files of the paper state: the
  version fixed to be read is the thesis, and "the goal by rule is the
  statement the source states".
* **Why**: the plan had listed it as a non-goal "to be looked at again
  when the prose is read".
* **Rests on it**: `GLS/CutRule.lean`.
* **Cost to reverse**: little. The statement was put in Lean and proved
  in one step (it is five lines from S10); its reading back was made
  after: `statements.md`, S24.

## 2026-11-25 13:33 GMT. A second word of the reviewer, relayed; and the target as it ended

* **The words**: "permission to dowload publicly available materials
  such as PhD theses should be a standard part of the relevant skills".
  Typed by the reviewer in the session that started this one, in reply
  to the question of 08:55; relayed by that session in a message that
  reached the operator at 13:33, after the closing page was pushed. (The
  reviewer's own answer in this session, at 13:14, had already been
  acted on.) The reading that the relaying session gives, which is its
  and not the reviewer's: public material the campaign needs is fetched
  without asking; a file that is not public is still the reviewer's to
  supply. It is now the skill's text (commit `28e3aa8`).
* **What it changes**: nothing in what was done. The one file fetched
  is recorded above (13:14: name, place, size; a folder of its own,
  nothing run).
* **Decided, the target as it ended**: the thesis's chapter 12 stands in
  place of the paper of 2021, which could not be got (the publisher's
  paywall; the open copy did not answer). The thesis says the chapter
  is that paper's content; the operator could not check this, since the
  paper was not read. The first entry's clause "where they differ, the
  paper's system rules" therefore could not be applied.
* **Whose numbering is cited**: the rule table, the skeleton and
  `statements.md` cite the Coq files of `ianshil/CE_GLS` (commit
  `3dd8619`) by file and line, and the thesis by its own numbers and
  pages (Figure 12.1, Definitions 12.2.2 and 12.2.3, Lemmas 12.5.1 to
  12.5.5, Theorems 12.6.1 to 12.7.2). The paper's numbering is cited
  nowhere.
* **Not taken**: to stop until the paper could be had.
* **Cost to reverse**: the campaign, if the paper's figure shows
  another system; a pass over the rule table, if it shows the same one
  with other numbers. Doubt: the paper is the earlier text, and a rule
  may have been changed between it and the thesis; the Coq files, which
  the paper's theorems are about, agree with the thesis.

## Stops

*Each time the reviewer's word was needed (`SKILL.md`, "Deciding,
checking, stopping", 3). The turn was not ended at the first: the
question was sent to the session that started this one, and the work
that does not rest on the answer went on.*

| date | what was asked, and why only the reviewer can answer it | what went on meanwhile | the answer, in the reviewer's words |
|---|---|---|---|
| 2026-11-25 08:55 | May the thesis's PDF be downloaded ("Ian Shillito_Thesis_2023.pdf", 1.41 MB, `openresearch-repository.anu.edu.au/bitstreams/0bbb4f8c-19b1-4e28-96e8-4ca795c863bf/download`)? The operator's environment makes no download without the reviewer's word, and his words covered "the paper". | The campaign folder; the literature for Q2 and Q5; the authors' Coq formalisation read as web pages; then, by the decision of 09:07, Adopt, Prove, Run and Explore from the Coq files, with the comparison with the prose owed. | 2026-11-25 13:14, in the operator's session: "yes you can download the thesis and any other materials to which you have online access that may assist you in the formalisation." Waited: 4 h 19 min by the clock, of which the work went on for the first hour; the session was not running from about 09:57 to 13:14. |

## 2026-11-25 16:30 GMT. A word of the reviewer, after the campaign

* **The words**: "can you write me now a tutorial for the new calculus
  with some graded exercises and an explanation of the key syntactic and
  semantic properties you have formalised please" (typed in the session
  that started this campaign's session).
* **What it is**: a command.
* **What it changes**: nothing that was decided or built. Added:
  `tutorial.md` (a page to read: the calculus, the semantics, what is
  proved, thirty graded exercises with solutions);
  `Play/GLSExercises.lean` (the exercises, as stubs to type in; its
  `sorry`s are the exercises, and nothing imports the file);
  `GLS/TutorialTest.lean` (a solution of each, in the library, with
  every output the page quotes pinned). `Play/GLS.lean` and
  `Play/GLSTutorial.lean` are as they were. Written by the session that
  started this one, not by the campaign's operator.

## 2026-11-26 09:46 GMT. A word of the reviewer, after the campaign: uniform interpolation, the intuitionistic variants, `∧` and `∨`

*Entered on 2026-11-27 14:15 GMT by the owner of `calculi/GLS`, from the
three reports and from row 2 of the cost log. The work was done by
another session (Claude Opus 5.5, started by another session from a
brief; 09:46 to 10:40 by its row, commits `b698279` at 10:38 and
`d7e79f6` at 11:14), not by the campaign's operator and not by the
owner. That session wrote its reports and its row and no entry here, so
this entry is written afterwards, against the rule at the head of this
page. Nothing below is restated from the reports: each is pointed at.*

* **The words**, as the three reports copy them (each calls them "the
  reviewer's task, verbatim"):

  > (A) you said that UI holds for GLS; find a proof, then check the
  > literature (this reverses the usual order: you might find a different,
  > shorter or interesting proof);

  > (B) report on literature and feasibility of extending these results to
  > an intuitionistic setting; consistent or not?

  > (C) there's no ∨ or ∧ in this development that I can see, it
  > corresponds to a minimal logic, can we define these or extend to
  > these? Clearly multiple premises implies ∧ on the left and multiple
  > conclusions ∨ on the right, but can we switch sides?

  and, in reply to the first version of the report on (A), as that report
  copies it (its §3.5): "If you can simplify the interpolant, go ahead".
* **What they are**: three commands, and a leave to go on.
* **What they change**:
  * Interpolation was "not a goal: about other systems" by the decision
    of 2026-11-25 09:07 ("which results are goals") and by the plan. It
    stays outside the campaign's goals; uniform interpolation for GL is
    now proved beside them, at the reviewer's word. The statements are
    in `GLS/Interpolation.lean`, pinned in `GLS/InterpolationTest.lean`;
    the report, with what is PROVED and what is OPEN (its §4), is
    [2026-11-26-ui.md](2026-11-26-ui.md). They have no number in
    `statements.md` and are not in its summary; the line there under
    "Not goals, and set aside" says where they are.
  * The order of work for (A) was the reviewer's: the proof first, the
    literature after. The report says the order was kept (its §3), and
    that the claim "UI holds for GLS" was not found anywhere in the
    campaign's record (its §1).
  * (B) is a report on the literature:
    [2026-11-26-intuitionistic.md](2026-11-26-intuitionistic.md). The
    facts about GL it uses are pinned in `GLS/InterpolationTest.lean`;
    nothing about an intuitionistic logic is in Lean.
  * (C) added `GLS/Connectives.lean` and `GLS/ConnectiveRules.lean`; the
    report is [2026-11-26-connectives.md](2026-11-26-connectives.md).
    The calculus and its encoding are as they were: `∧` and `∨` are
    defined, not new constructors of `Form`.
* **Cost to reverse**: little for the interpolation (nothing imports
  `GLS/Interpolation.lean` but its test file and `GLS.lean`); a stage
  for the connectives, since `GLS/Parse.lean` imports
  `GLS/Connectives.lean`.

## 2026-11-26 22:28 GMT. After the campaign: `glsrun prove`, and what it checks before it prints

By the owner of `calculi/GLS`, at the directing session's request
(the round's organisation since 2026-11-26: a directing session, and an
owner for each calculus).

* **Decided**: the command answers by the search over sets, checks the
  answer in the program, and falls back on the proved search where the
  check fails. It prints only facts whose certificate the program has
  checked. For a derivation: the tree of moves replayed on multisets
  under a cap (no side of a sequent longer than 4 096 formulas), then
  `treeCert.check`; beyond the cap, the proposition `Derivable` alone,
  by `setCert.check`. For a tree of worlds: a table of truth values
  (`GLS/FastCheck.lean`), which is not the certifier's check and is
  compared with it in `GLS/ParseTest.lean`.
* **Not taken**: to print the derivation as data beyond the cap without
  checking it in the program (the kernel checks such a tree in under a
  second, and it would pass: a move that applies to a set of formulas
  applies to any multiset with those members; but that is not proved in
  Lean). To check a tree of worlds by `noDerivable.check` compiled: the
  first run returned a flag for `consis 32`.
* **Why**: a file made at a shell that Lean then refuses is worse than
  a weaker fact.
* **Also decided**: a text with no arrow is one formula `A`, read as
  `⇒ A`. The signs `¬ ⊤ ◇ ∧ ∨` are read by the definitions of
  `GLS/Connectives.lean`; the printers write `→ ⊥ □` only.
* **Rests on it**: `GLS/Parse.lean`, `GLS/FastCheck.lean`, the `prove`
  part of `Main.lean`, `Corpus/prove_corpus.py`.
* **Cost to reverse**: little.

## 2026-11-27 09:00 GMT. After the campaign: the two checks are the algorithms one would run

By the owner of `calculi/GLS`, at the directing session's request,
which relayed the reviewer's words on note 27 (a) ("the compiled check
can be the slow side"): "so that's not right. The compiled checker must
have an error, no? … It shouldn't happen."

* **What was wrong.** Two definitions were also the checks of the
  certifiers, and each is exponential run as it is written. `Form.holds`
  asks for `A` at every world below a world for each `□A` and keeps
  nothing. `Cert.check` writes each premise out, and GLR doubles the
  boxed part of an antecedent. The kernel keeps the terms it has
  reduced and reduces a list only as far as it is looked at, which hid
  both on the families first measured. It does not hide the second on
  every family: on `lastChain` (`⇒ □p → □ⁿq → □ⁿp`, where the `p` that
  IdP asks for is last in the antecedent) the kernel took 10 s on the
  list replay at `n = 16` and overflowed its stack at 20.
* **Decided.** The check of `noValid` and `noDerivable` is
  `Seq.refutedT` (`GLS/Table.lean`): each formula evaluated at all the
  worlds of the tree at once. The check of `treeCert` is
  `Seq.countCheck` (`GLS/Counts.lean`): the replay with each side by
  counts. Each is proved equal to the definition it replaces (S25 to
  S27), the soundness of each certifier goes through that equality, and
  the kernel and compiled code run the same function. `Form.holds`,
  `Seq.refutedAt` and `Cert.check` stay as the definitions that the
  theorems of the development are about.
* **Not taken: `@[csimp]`**, the definition for the kernel and the new
  function for compiled code. The kernel's run of the list replay is
  not good either (above), and `Cert.check` is the library's function
  for every proof system, so there is no constant of GLS for `@[csimp]`
  to replace. Not taken either: a check by the marks proved sound with
  no equality; the equality costs no more and keeps the old statements
  as theorems (`noValid_check`, `treeCert_check`).
* **The replay by counts took three forms**, and the first was itself
  too slow in the kernel (`measurements.md`, "The two checks"). The
  first looked each formula up in the whole side: at each GLR the
  square of the number of entries in comparisons of formulas; in the
  kernel 3.7 s at `boxChain 64` and over the cap of 8 GB at 128, where
  the list replay it replaced took 0.03 s. Seen only because the table
  was carried beyond the sizes asked for. The form kept: the entries of
  a side in order of the size of the formula, the premise of GLR by one
  merge, and the formula that ImpR or ImpL adds put in with no search.
  The proof of S27 was made again for it; only the lemmas about one
  side changed.
* **What it costs.** Where the kernel's laziness served the list
  replay, the replay by counts is somewhat slower in the kernel: 1.4 s
  against 0.9 s at `kChain 128`, 0.1 s against 0.02 s at `boxChain
  256`. Where it did not (`lastChain`), the list replay overflows the
  stack from 24 and the replay by counts takes 11 s at 256.
* **Gone with it.** `GLS/FastCheck.lean`, the program's second check of
  a countermodel, which was only tested against the certifier's; the
  cap of 4 096 formulas in `glsrun prove`, and with it the third kind
  of answer as the normal answer for `□p → □ⁿp` from `n = 12` (the
  decision of 2026-11-26 above): the derivation is now stated as data
  at every size tried. The kind remains for a tree of moves over sets
  that would not replay as a derivation of GLS, which has not been
  seen; `--sets` asks for it.
* **Also decided: a cap on the program's own memory**, 8 GB
  (`watchMemory`, `Main.lean`), and in the measuring scripts a cap on
  the memory of what they run, with a deadline that ends the process
  group. The search over multisets still writes the sequents out (it
  returns a derivation of GLS as a term, which holds them): a deadline
  alone let it take what it could reach in 20 s.
* **Not repaired**: `measurements.md`, "The two checks", at its end.
* **Rests on it**: `GLS/Run.lean` (the certifiers), `Main.lean`,
  `GLS/CheckTest.lean`, `Corpus/measure_checks.py`.
* **Cost to reverse**: little; the definitions and their theorems are
  untouched.

## 2026-11-27 10:14 GMT. After the campaign: the search and the scripts write no sequent out

By the owner of `calculi/GLS`, at the directing session's request,
which relayed the reviewer's words on what the entry above left ("Please
sort out both issues. Delegate or fix yourself. Do it now."), and its
own: "a cap on a known exponential is a fence, not a repair".

* **Route (a), of the two offered**: a proved decision that does not
  build what it does not read (S28), and not route (b), every command on
  the search over sets with its answers checked and the search over
  multisets kept behind a size. **Why**: (a) was within reach in the
  hour. The search over sets was already the search of S4 with each
  premise less its repeated formulas, and S4's proof has two parts that
  carry over. Its measure (S9) does not rise when repetitions are
  removed. Its refutations look at which formulas a sequent has, not how
  often. The one new fact is on the other side: a tree of moves found
  for a sequent without repetitions replays at every sequent with its
  formulas (`Yes`), which is where "no formula repeated" is used. With
  (b) the proved decision would have stayed exponential and one command
  would have needed a stated size at which it stops.
* **Decided.** `certOrRef` (`GLS/Decide.lean`) is the producer of every
  command of `glsrun` and of the library (`prove?`, `refute?`,
  `produce`, the decisions `derivableDecidableFast` and
  `validDecidableFast`, the `Decidable (Valid s)` of the corpus, the
  explorer's `found` and `explain`). The search over sets that was not
  proved is deleted, with the fallback from it. `glsrun prove --proved`
  is gone: there is one search, and it is proved.
* **Kept as theory**: `proofOrRef` and S4 to S6 as they were proved
  (completeness as data is a derivation of GLS, which is `2ⁿ` large as a
  term), with the tutorial's and the tests' uses of them on small
  sequents. No command runs `proofOrRef`. Table 1 of `measurements.md`
  is its record: cut off at 28 nested boxes.
* **Scripts** (S29): `scriptCert` and the engine's yes side check a
  script with its goals by counts. The library's `derives` is first
  proved equal to a run on a bare list of goals, for every proof system
  (`derives_eq_goalsDone`); that half belongs in the library, and is
  asked of the directing session in method note 29.
* **The script of a tree of moves** (`certScript`) is computed from the
  tree, not from the derivation the tree is, which `Der.ofCert` would
  write out. That the two scripts are one is tested on 385 trees and not
  proved.
* **`glsrun check`** runs the definitions (`Cert.check` on lists,
  `Seq.refutedAt`) only with `--definitions`, to measure them, under its
  deadline and the cap of 40 000 000 formulas. It is the one command
  that writes a sequent out, and only when asked.
* **Still `2ⁿ`, and why**: `measurements.md`, "What remains exponential".
* **Found, and left at that hour**: the check by the marks is slower
  compiled than in the kernel on `binTree 12` (7.7 s against 2.0 s), a
  formula with repeated subformulas; `measurements.md`, under Table 5,
  and method note 29 (h). Repaired in the next entry.
* **Rests on it**: `GLS/Decide.lean`, `GLS/Scripts.lean`, `GLS/Run.lean`,
  `GLS/SetSearch.lean` (now `setCert` and the producer's old name),
  `Main.lean`, `Corpus/measure.py`.
* **Cost to reverse**: little; nothing proved before was changed.

## 2026-11-27 11:03 GMT. After the campaign: the countermodel check keeps a table over the different subformulas

By the owner of `calculi/GLS`, on the reviewer's word in the session
("Yes, repair it"), to the question the entry above ended on.

* **What was wrong.** The check of S26 computes the marks of a formula
  for each occurrence of a subformula. On `binTree 12`, whose formula
  has a subformula twice at each level, it took 7.7 s compiled and
  2.0 s in the kernel, which keeps what it has reduced.
* **Decided.** `noValid` and `noDerivable` check by `Seq.refutedM`
  (S30): the marks of a subformula are kept in a table once computed,
  looked up before the subformula is entered, one table for the whole
  sequent. Proved equal to `Seq.refutedAt`.
* **The table's form, chosen for the kernel as well as for compiled
  code**: an entry holds the size of its formula, the table is in order
  of size with the largest first, and a search stops at the first
  smaller entry. A subformula is entered after its parts, so it goes in
  at the head. Variables and `⊥` are not kept. A table searched from
  end to end by equality of formulas would have cost, on a chain of `n`
  boxes, `n²` comparisons each of up to `n` steps (the fault of the
  first replay by counts, entry of this morning).
* **Kept**: `Form.marks`, `Form.holdsT`, `Seq.refutedT` and S25, S26,
  which S30's proof goes through.
* **Rests on it**: `GLS/Table.lean`, `GLS/Run.lean`.
* **Cost to reverse**: little.

## 2026-11-27 14:31 GMT. After the campaign: is uniform interpolation proved? Checked, and the condition on variables added

By the owner of `calculi/GLS`, at the reviewer's word.

* **The words** (typed in the owner's session, after the entry of
  2026-11-26 09:46 above was written): "so well, it seems we don't know
  if UI has been proved or not. Please find out for us!"
* **What it is**: a command.
* **What was found**. The proof is there and the kernel accepts it:
  `GLS/Interpolation.lean` elaborated afresh (1.7 s), no `sorry`, no
  axiom declared, nothing `unsafe` or `partial`; `#print axioms` gives
  `[propext, Quot.sound]` for `uniformInterpolation`,
  `uniformInterpolationSeq`, `uiSeq_iff`, `uiSeq_free`,
  `uiSeqRaw_mdepth`, `uiSeq_equiv_raw`, `holds_bisim`. The statement
  `UIFor p A` was read against the usual one: it has both quantifiers,
  the interpolant is chosen before `B`, and derivability is `Fam`, the
  family of S3 and S5. One clause of the usual statement was missing:
  that every variable of `∃p.A` is a variable of `A` (the statement had
  only "no `p`").
* **The choice**: the missing clause is stated and proved, in a file of
  its own (`GLS/InterpolationVars.lean`), with `UIFor` and the file of
  2026-11-26 left as they are; the new statement S32 holds a `UIFor p A`
  and adds the clause. Statements S31 and S32, screened and committed
  before their proofs.
* **Not chosen**: adding the clause as a field of `UIFor` (it would
  change a statement the report of 2026-11-26 quotes); deriving it on
  paper by substitution and leaving the Lean as it was.
* **What "for GL" rests on, as before**: `Fam` is derivability in GLS,
  proved sound and complete for the two-valued transitive, conversely
  well-founded models (S3, S5). That GLS derives exactly the theorems of
  the Hilbert system GL is from the literature and is not in Lean (the
  plan: not a goal).
* **Rests on it**: `GLS/InterpolationVars.lean`, the guards and pins at
  the end of `GLS/InterpolationTest.lean`.
* **Cost to reverse**: little.
