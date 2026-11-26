# DILL: the decisions

One entry for each choice the operator made, in order, and one for each
word of the reviewer. Written when the choice is made, not afterwards.
The closing page lists the entries by what they cost to reverse, the
costliest first.

The cost to reverse is one of:

* **little**: a name, a letter, the place of a file;
* **a stage**: the form of a goal, an encoding, which results are goals;
* **the campaign**: the source, the system, what "holds" means, the
  axiom policy.

## 2026-11-26 14:50 GMT. The target

*The first entry, and the one record of what it fixes: the other files of
the folder point here.*

* **The command's words**: "Dual intuitionistic linear logic, DILL: the
  two-zone sequent calculus Γ ; Δ ⇒ C (unrestricted zone Γ, linear zone
  Δ, one conclusion; connectives ⊸, ⊗, 1, &, ⊤, ⊕, 0 and !). Campaign
  folder calculi/DILL/. Phase 2 of the linear-logic round; phase 1 was
  calculi/MALL/." They reached the operator in a task written by another
  session of the reviewer's (the one that started the MALL campaign and
  amended the skill from its notes), which quotes the reviewer,
  2026-11-26: "Yes, start DILL". That task gives the source as the
  operator's to settle, recommends "the sequent calculus of Chang,
  Chaudhuri and Pfenning as the figure to transcribe, with Barber cited
  for the system", and lists what carries over from MALL and the
  candidate goals; each is decided below or in the plan. The skill was
  run as a command (the Skill tool), with the words above as argument.
* **The paper and its version**: B.-Y. E. Chang, K. Chaudhuri and
  F. Pfenning, *A judgmental analysis of linear logic*, technical report
  CMU-CS-03-131R, Carnegie Mellon University, 14 April 2003, revised
  29 December 2003 (34 pages). The revised report is the latest version;
  the work has no journal or conference version known to the operator.
  The system is in Section 3, "Sequent calculus for JILL", pp. 10-18:
  the judgment forms (pp. 10-11), Figure 2 (p. 12), Theorem 2
  (weakening and contraction of the valid zone), Principle 7 and
  Theorem 3 (three cuts admissible), Theorems 4 and 5 (against natural
  deduction), Lemma 6 (the invertible rules).
  Not taken, a line each:
  - A. Barber, *Dual intuitionistic linear logic*, ECS-LFCS-96-347
    (Edinburgh, 1996), 54 pages: the origin of the name and of the two
    zones; it has natural deduction with terms for I, ⊗, ⊸, ! only, no
    sequent calculus and no additives (its §7.1 leaves them as further
    work). Cited for the system and read for the translation to
    intuitionistic linear logic (its §5);
  - F. Pfenning, *Linear Logic*, lecture notes, draft of 26 January 2002
    (168 pages), chapter 3: the same sequent calculus without `?`, with
    quantifiers and ⊃ besides, Theorem 3.8 (two cuts admissible), 3.9
    (cut elimination), 3.11 (consistency), 3.12 (the disjunction
    property). Its title page says "Please do not cite or distribute
    this document": so it is not the source of record. It is read for
    the prose that the report compresses and for the results the report
    does not state, and the records say where a result is found only
    there;
  - L. Caires and F. Pfenning, *Session types as intuitionistic linear
    propositions*, CONCUR 2010: Figure 3 is the DILL sequent calculus
    with proof terms, for ⊸, ⊗, 1, &, ⊕, ! (no ⊤, no 0), with cut and
    cut! as rules; narrower in connectives;
  - K. Chaudhuri, *The focused inverse method for linear logic*, thesis,
    CMU 2006: the same calculus as the base of a focused one; not
    fetched, since the report states the system and its theorems.
  Could not be got: none of those tried.
* **The system**: the fragment of the sequent calculus for JILL
  (Figure 2 of the report) for the judgment `Γ ; Δ ⟹ C ; ·` (a goal that
  is true) and the connectives ⊗, 1, ⊸, &, ⊤, ⊕, 0, !. That is the
  figure without the rules `promote`, `?L`, `?R`, and with the right-hand
  side `γ` always of the form `C ; ·`: eighteen rules (init, copy, and
  sixteen for the connectives). The report says that JILL "contains, as
  fragments, both dual intuitionistic linear logic (DILL) [5] and
  hereditary Harrop logic" (p. 1); this fragment is that one, extended
  by the additives, and the campaign calls it DILL as the command does.
  With it, the two cuts of Principle 7 that stay in the fragment (7.1,
  on a formula of the unrestricted zone; 7.2, on a linear formula), as
  rules of a second family.
  Left out: the possibility judgment `· ; C` and `?`, with the third cut
  (7.3); ⊥, ¬ and the modal disjunction, which the report defines from
  `?`; ⊃ (it is `!A ⊸ B`, p. 9); natural deduction (Figure 1) and
  Theorems 1, 4 and 5 about it; Section 4 (classical linear logic
  interpreted) and the appendix (several conclusions). JILL whole is an
  extension, and a campaign of its own.
* **The results aimed at**: from the standing list, cut elimination
  (Theorem 3; Pfenning 3.8, 3.9) and the disjunction property (Pfenning
  3.12); the deduction theorems in the form the system has them, the
  inversions of ⊸R and !L (Lemma 6); the finite model property is
  expected to fail with `!` and to hold without (the Survey makes it
  exact). Beyond the list: weakening and contraction of the unrestricted
  zone (Theorem 2), and their refutation for the linear zone; the
  inversions of Lemma 6; identity expansion; the subformula property;
  the translation to and from one-zone intuitionistic linear logic;
  soundness and completeness for a phase semantics, if a readable source
  states one; decidability of the fragment without `!`. The plan accepts
  or rejects each.
* **The path**: adopted from the paper.
* **The place and the name**: `calculi/DILL/` of `proof-tools`, a lake
  project of its own (as `calculi/MALL/`), core Lean only, toolchain
  `leanprover/lean4:v4.31.0`; the Lean name is `DILL`.
* **The library**: the checkout the operator was started in, a worktree
  of `fairflow/proof-tools` at `d5e294c`; the remote's `main` is at
  `d5e294c` (`git ls-remote`, 14:47): the same commit, nothing to
  update. The skill's files were last changed in `94df876`.
* **The source's files**, fetched 2026-11-26 14:47 GMT into a folder of
  the session's scratchpad (`src/`; nothing is run from it; a reboot
  clears it). No LaTeX is public for any of them; the PDFs have a text
  layer; the figure is read from the page as an image.
  - `ccp03.pdf`, https://www.cs.cmu.edu/~fp/papers/CMU-CS-03-131R.pdf,
    272 702 bytes, 34 pages (the source);
  - `barber96.pdf`,
    https://www.lfcs.inf.ed.ac.uk/reports/96/ECS-LFCS-96-347/ECS-LFCS-96-347.pdf,
    682 508 bytes, 54 pages;
  - `pfenning-linear02.pdf`,
    https://www.cs.cmu.edu/~fp/courses/linear/handouts/linear.pdf,
    866 345 bytes, 168 pages;
  - `cairespfenning10.pdf`, https://www.cs.cmu.edu/~fp/papers/concur10.pdf,
    234 366 bytes, 15 pages.
  What the survey agent fetches besides is listed in
  `survey-report.md`, "Files fetched".
* **Pushing**: to `main` of `fairflow/proof-tools`, only as
  `git push origin HEAD:refs/heads/main`, after `git branch -vv` before
  the first push and a fetch and rebase before each (the task's words;
  the reviewer's standing rule that no `claude/*` branch is pushed).
* **Not touched**: every tracked file outside `calculi/DILL/`. Only the
  reviewer contacts the source's authors.
* **Told to the reviewer**: in the session's output, at this commit:
  "DILL campaign begun. The paper: Chang, Chaudhuri and Pfenning, *A
  judgmental analysis of linear logic* (CMU-CS-03-131R, revised
  December 2003), Figure 2, with Barber's report cited for the system
  and Pfenning's 2002 lecture notes read beside it. The system: the
  fragment of that figure for goals that are true, with ⊗, 1, ⊸, &, ⊤,
  ⊕, 0, ! (eighteen rules, without `?` and the possibility judgment),
  and the two cuts. Aimed at: both cuts admissible and cut elimination;
  weakening and contraction, proved for the unrestricted zone and
  refuted for the linear one; the inversions; the disjunction property;
  the translation to one-zone intuitionistic linear logic; a phase
  semantics if a readable source states one; decidability without `!`.
  The place: `calculi/DILL/`. Nothing is asked."
* **Before this text was read**: nothing of the calculus. The task named
  the skill as the first act, and it was.
