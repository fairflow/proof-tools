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

## Stops

*Each time the reviewer's word was needed (`SKILL.md`, "Deciding,
checking, stopping", 3). The turn was not ended at the first: the
question was sent to the session that started this one, and the work
that does not rest on the answer went on.*

| date | what was asked, and why only the reviewer can answer it | what went on meanwhile | the answer, in the reviewer's words |
|---|---|---|---|
| 2026-11-25 08:55 | May the thesis's PDF be downloaded ("Ian Shillito_Thesis_2023.pdf", 1.41 MB, `openresearch-repository.anu.edu.au/bitstreams/0bbb4f8c-19b1-4e28-96e8-4ca795c863bf/download`)? The operator's environment makes no download without the reviewer's word, and his words covered "the paper". | The campaign folder; the literature for Q2 and Q5; the authors' Coq formalisation read as web pages; the scratch screens of the encoding. No rule is entered in the rule table before a source in prose is read. | (not yet answered) |
