# Brünnler's system K: the gates

One entry for each time a gate is put to the reviewer, in order. A gate is
passed when its entry says so. The reviewer's words are copied, not
summarised.

## 2026-11-23 07:52 GMT. Stage 0: the target

*The first entry, and the one record of what it fixes: the other files of
the folder point here.*

* **The command's words**: "Brünnler's K".
* **Put to the reviewer** (in the session, as one message):
  - *The paper, and the version.* K. Brünnler, *Nested Sequents*,
    habilitation thesis, arXiv:1004.1845 v1 (2010), Chapter 2, §2.1: the
    only version the operator could get, the latest of the three, and
    arXiv lists its TeX source. The other candidates, from the thesis's
    bibliography (p. 69): [11] Brünnler, "Deep sequent systems for modal
    logic", Archive for Mathematical Logic 48(6), 2009, the peer-reviewed
    version (Springer's copy behind a login, the author's copy returning
    404; the reviewer would have to supply it); [10] the same title,
    Advances in Modal Logic 6, pp. 107–119, 2006, the conference version
    (aiml.net could not be reached). A slip in the source: p. 3 credits
    part of Chapter 2 to "[13] which is joint work with Lutz Straßburger",
    but [13] is Brünnler and Studer on common knowledge; the paper behind
    §2.2 is not in the bibliography.
  - *The system.* System K, the source's name: the rules
    `{∧, ∨, □, ◇k_c}` with the axiom `Γ{p, p̄}` (Figure 2.3, pp. 9–10).
    Left out: the extensions `◇d_c, ◇t_c, ◇b_c, ◇4_c, ◇5_c`; the variant
    `◇k` without built-in contraction (Figure 2.5); system `K_c + [X]` of
    §2.2; the deep inference systems of §2.3; Chapter 3. The search
    variant `K°` (pp. 14–15) is used as the source uses it, for the
    completeness proof, and is not a target of its own.
  - *The results aimed at.* Cut elimination: holds of this system
    (Theorem 2.35, p. 27), a goal by rule. The finite model property:
    holds of this system (Corollary 2.24, p. 19), a goal by rule.
    Deduction theorems: do not apply to this system (no derivability from
    hypotheses in Chapter 2); hold of the logic, proved elsewhere (Hakli
    and Negri, Synthese 187(3), 2012, abstract only read). Normalisation
    and the Church-Rosser property: do not apply, the source defines no
    term calculus. The disjunction and existence properties: do not
    apply, the logic is classical. Of the source's own theorems,
    soundness (Theorem 2.9) and completeness (Theorem 2.23) are goals by
    rule; Lemma 2.4, Lemma 2.14, Lemma 2.22 and Corollary 2.25 are to be
    proposed in the Survey, with sizes.
  - *The path.* Adopted from the paper. No mechanisation found in Lean,
    Coq or Isabelle (two web searches).
  - *The place and the short name.* `examples/BrunnlerK/` in proof-tools,
    core Lean only; the campaign folder `examples/BrunnlerK/campaign/`;
    the short name `BrunnlerK`.
  - *Asked.* (1) Checkout and branch: this session's worktree and its
    private branch, which holds `proof-tools-home` at `e6410cd`. (2)
    Pushing: commit locally and push nothing until the reviewer says;
    when he does, to `proof-tools-home`? (3) Not to be touched: nothing
    outside `examples/BrunnlerK/`; anything else? (4) The earlier draft
    `docs/brunnler-k/plan.md`, untracked and written before this gate:
    rewrite the plan from the skill's template into the campaign folder,
    say at its top that the reading came first, and remove the draft; the
    published artifact stays unless the reviewer wants it deleted.
* **Answer** (2026-11-23, in the session): "Yes, as proposed"
* **Fixed**: the reviewer: Matthew Fairtlough. The paper and version:
  Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Chapter 2, §2.1. The
  system: System K, `{∧, ∨, □, ◇k_c}` with the axiom `Γ{p, p̄}`; left
  out: as listed above. The results aimed at: as listed above. The files:
  `examples/BrunnlerK/` of the library. The library: the worktree
  `.claude/worktrees/brunnlers-k-calculus-ca0a03` of proof-tools, branch
  `claude/brunnlers-k-calculus-ca0a03`, at the merge `439bfd7` of
  `origin/proof-tools-home` (`e6410cd`). Pushing: nothing is pushed until
  the reviewer says; then to `proof-tools-home`. Not to be touched:
  everything outside `examples/BrunnlerK/`.

**How this gate was reached, which is not how the skill lays it down.**
The command was typed in a session whose worktree was cut from `main`,
where the skill is not installed, so the command did not run. The
operator worked from `docs/campaign.md`, read the source in full
(pp. 3–43 and the bibliography), and wrote and published a plan before
any target was fixed. The reviewer then said (2026-11-23): "we should be
working from an installation of calculus-campaign the entire purpose of
this session was to test that campaign. Please install it". The skill was
brought in by merging `origin/proof-tools-home`, and the reviewer chose
"Continue here" over a fresh session. The proposal above was put after
that. So the operator of this stage did not start cold, and the reading
that the first act forbids had already been done.

## 2026-11-23 09:11 GMT. Stage 0: the plan

* **Put to the reviewer**: the Survey's report and the plan, as one
  private page (rendered from `report-0-2026-11-23.md` and `plan.md` at
  commit `f940347`), with nine things to decide listed in the session.
* **Asked**: pass the plan's gate with the recommended choices, or
  changes first?
* **Answer** (2026-11-23, in the session): "yes you may download the
  source, surprised you need permission; puzzled as to how you can omit
  exchange if you do a direct encoding into type, avoiding Sets; it
  doesn't really matter about the warm test; I think examples is a poor
  choice of target directory so please amend skill accordingly; merge to
  main as there's no current need for branching; I don't like the
  generality of Valid as it implies EM if stated as written in your
  sources, can you make it less absolute so that doesn't happen, or do
  you have to state it indirectly as per current proposal? Oh, you can
  omit the cyclic check if it isn't relevant to K; but think about how to
  accommodate it later; as with all modal calculi, trying to follow the
  Greek convention and allowing Π and Σ as variable names is not ideal
  since those are extremely reserved symbols in Lean and you will have to
  work around them anyway. You can use Θ and Φ or Ξ (for Σ) and give me
  an Upsilon please."
* **Result**: not passed. The answer settles some decisions, changes
  others and asks two questions; it does not say which results are goals
  and does not pass the plan. What was done on it, before the gate is
  asked again:
  - *The TeX source* (decision 6): fetched and compiled outside the
    repository; `skeleton.md` has the labels.
  - *Exchange* (decision 4): a question. Answered in the session and in
    the plan's table of encodings, the row "lists for multisets". No
    change of proposal: lists, no exchange rule, exchange as goal 4.
  - *The place of the files*: `examples/` is rejected as the default.
    The skill is amended to `calculi/<Calculus>/` (the operator's choice
    of name, for the reviewer to change), and this campaign is moved to
    `calculi/BrunnlerK/`. **This replaces the place fixed in the first
    entry**; "not to be touched" is now everything outside
    `calculi/BrunnlerK/`, the skill excepted where the reviewer asks for
    a change to it.
  - *Pushing*: "merge to main as there's no current need for branching".
    **This replaces the first entry's "nothing is pushed … then to
    `proof-tools-home`"**: the campaign's commits go to `main`.
  - *"Valid"* (decision 2): the indirect form is not wanted. A direct
    form is proposed in its place: truth at every state of every
    two-valued model (the plan's Q2, with what was proved of it in
    scratch). To be confirmed.
  - *Cyclic leaves* (decision 3): left out for K. The plan's Q3 says
    where they would be brought in.
  - *Letters*: `Υ` for the source's `Π`, `Ξ` for its `Σ`, `Θ` and `Φ`
    for further sequents; in the plan's Q1, and in the skill
    (`reference/adopt.md` §3).
  - *The warm test*: "it doesn't really matter".
* **Set aside by the reviewer**: nothing yet.
* **Made goals by the reviewer**: nothing yet. Still open at this gate:
  which results are goals (the four by rule, and those proposed beyond
  the rule); the route to cut elimination (decision 1); whether `K°` is
  a family of its own (in decision 3); the rest of the encoding table
  (decision 4); who relies on the answers (decision 7).

## 2026-11-23 09:36 GMT. Stage 0: the plan, put again

* **Put to the reviewer**: the revised plan with what changed after the
  first answer, as one private page and on `main` at commit `f8609a9`
  (`plan.md`; `report-0-2026-11-23.md`, its last section). Five things
  were listed as still open: `Valid` over two-valued models; which
  results are goals; the route to cut elimination; `K°` as a family of
  its own and the rest of the table of encodings; who relies on the
  answers.
* **Asked**: "Pass the plan's gate with `Valid` over two-valued models
  and the recommended goals ("Pass as recommended"), or changes first
  ("Changes first")?"
* **Answer** (2026-11-23, in the session): "Pass as proposed"
* **Result**: passed. With it, as proposed in the plan at `f8609a9`:
  - "valid" is `Valid`: truth of `Γ_F` at every state of every
    two-valued model (decision 2);
  - cut elimination: the statement first by the source's short route,
    from completeness; whether the procedure of §2.1.4 is a further goal
    is decided at the report of Prove (decision 1);
  - the search has no cyclic leaves; `K°` is transcribed as a family of
    its own (decision 3);
  - the table of encodings, each row (decision 4);
  - who relies on the answers: as the plan's Q3 proposes (decision 7);
  - the folder `calculi/BrunnlerK/`, and commits to `main`, as the
    second entry records. The name `calculi` was not objected to.
* **Set aside by the reviewer**: none of the results that are goals by
  rule. The plan's non-goals stand as proposed: Proposition 2.5 at
  `ρ = k`; everything with `X ≠ ∅`, §2.2, §2.3 and Chapter 3 (left out at
  the target gate); soundness for `ValidF`; any statement of complexity.
  Deduction theorems, normalisation, the Church-Rosser property, the
  disjunction property and the existence property do not apply to this
  system (the plan's Q2).
* **Made goals by the reviewer**: all ten goals of the plan. By rule:
  soundness (1), completeness (8, 9), the finite model property (9), cut
  elimination (10). Beyond the rule: invertibility (2), the admissible
  rules `nec`, `wk`, `ctr` (3), exchange (4), general identity (5), `K°`
  into K (6), termination (7), decidability (in 9).

## 2026-11-23 14:07 GMT. Between stages: where Adopt runs

Not a gate. Recorded because it departs from rule 5 of the skill (a stage
starts in a fresh session) and from the brief's first line of "Done".

* **Put to the reviewer** (2026-11-23 09:36 GMT, the closing message of
  stage 0): Adopt starts in a fresh session, opened with
  `/calculus-campaign calculi/BrunnlerK/campaign/brief-1-1.md`, after a
  pull of `main`.
* **Answer** (2026-11-23, in the session): "Continue here with Adopt I
  have pulled in, you continue in your worktree.  I think a single
  session may be sensible, we'll see how much context is needed."
* **Result**: Adopt runs in the session of stage 0, in the operator's
  worktree, from `brief-1-1.md`. Nothing else of the brief changes.

## 2026-11-23 15:45 GMT. Stage 1: the rule table

* **Put to the reviewer** (2026-11-23 14:19 GMT, at `8ebe5e6`):
  `campaign/rule-table.md`, with its five things to sign: how a rule
  names its place (a path, the whole node `Θ`, the main formula by
  membership, and the functions `node?`, `setNode`, `add`, `erase`,
  `addBox`, `box?`, `setBox`); where a rule puts what it adds (in front;
  a new box last; the first occurrence erased); the axiom by membership;
  K° (the side condition of `□°` as D10, the proviso as `sameSet`, no
  proviso on the axiom); the divergences D1 to D14.
* **Asked by the reviewer first** (2026-11-23, in the session): "So the
  paper puts no constructors in the rule conclusion?"
* **Answered by the operator**: the paper's conclusions do carry
  structure, `Γ{A ∧ B}`; the structure is not made of constructors,
  since filling a hole and the comma of multisets are functions. A
  conclusion `Fam c (C.fill (Δ.add (A ⋏ B)))` would be a computed index;
  a conclusion of constructors only would say "at the root, at the head"
  and need rules the source does not have. So the pattern is stated as
  hypotheses on a variable (D2). Nothing proves that the two readings
  agree: the evidence is the table row by row and Example 2.3 as a term.
  Offered: after the signature, a type of contexts with `fill`, and each
  rule in the figure's own shape as a derived rule, for example
  `Fam c (C.fill (Δ.add A)) → Fam c (C.fill (Δ.add B)) → Fam c (C.fill (Δ.add (A ⋏ B)))`.
* **Answer** (2026-11-23, in the session): "As put thanks"
* **Result**: passed, as put. The five things are signed; no constructor
  changes. The offer of the derived rules was not taken up and not
  refused: it is carried to the report of the stage as a question.

## 2026-11-23 17:30 GMT. Between stages: the reviewer's test deferred; Prove begun

Recorded because it departs from the skill twice: the gate that ends
Adopt is not passed, and Prove is begun in the session of stages 0 and 1.

* **Put to the reviewer** (2026-11-23 15:55 GMT, at `5de5634`): the
  reviewer's test, with `report-1-2026-11-23.md` and
  `Play/BrunnlerK.lean`; and the report's four smaller decisions.
* **Answer** (2026-11-23, in the session): "I will test later since
  proving the next set of results may change what you already
  implemented so: /goal prove completeness and cut elimination"
* **Asked by the reviewer next** (2026-11-23, in the session): "We're
  still in the skill process right? Or off track?"
* **Answered by the operator**: in the process, at stage 2, with these
  two departures, both the reviewer's.
* **Result**: the reviewer's test is **not done and not passed**: it is
  deferred by the reviewer. The report's decisions 2 to 5 are not
  answered. Prove is begun, for two of the ten goals and what they rest
  on: completeness (goal 9, first line) and cut elimination (goal 10).
  A change that Prove makes to a module the exercises file rests on is
  recorded here when it is made.

## 2026-11-23 17:40 GMT. Stage 2: the definitions and the statements, first sending

* **Put to the reviewer** (2026-11-23 17:40 GMT; the commit is named in
  the message): `BrunnlerK/Semantics.lean`, all of it, and the entries
  of `statements.md` for goals 1, 8, 9 and 10. To sign:
  1. the models and truth (`Model`, `Model.sat`), Definition 2.6 clause
     by clause, with "or", "not", "there is" as Lean's;
  2. `Model.TwoValued` and `Valid`, as the plan has them;
  3. the corresponding formula (`Form.bot`, `Form.disj`, `NSeq.form`):
     `⊥` is `p ∧ p̄` at the proposition numbered 0; the disjunction is
     bracketed to the left; formulas first, then boxes, in the
     sequent's own order;
  4. a countermodel as data: a finite tree (`Tree`), a state of the
     model of all finite trees (`treeModel`); `Refutation Γ`;
  5. the statements `Soundness`, `SoundnessCut`, `ProofOrRefutation`,
     `Completeness`, `ValidDecidable`, `CutElimination`.
  With them, said in the note: the route proposed for goal 8 is not the
  source's (no K°, no Lemma 2.22); goals 2 to 7 are not on it and stay
  OPEN; the finite model property, in a form with a finite set of
  states, stays OPEN.
* **Screened first** (`BrunnlerK/Test/Semantics.lean`): the
  corresponding formula on five sequents; 21 rule instances and four
  instances of `cut`, on 28 564 trees of depth at most 2: no tree makes
  every premise true and the conclusion not; the empty sequent, `[∅]`
  and the six sequents of the exercises that are not derivable each
  have a refutation among those trees; four derivable ones have none.
* **Answer**: not yet given.
