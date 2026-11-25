# GLS: the closing page

Written 2026-11-25 13:31 GMT. The work is commit `96dad49` on `main` of
`fairflow/proof-tools` (this page is the commit after it). To build:

    (cd ~/Lean/Sources/proof-tools && git pull)
    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake build GLS glsrun)

## 1. What was adopted, proved, and runs

GLS, the sequent calculus on multisets for the provability logic GL,
with its proof-search variant PSGLS and GLS + (cut), from Goré,
Ramanayake and Shillito (TABLEAUX 2021). Read: the authors' Coq
formalisation (`ianshil/CE_GLS`, commit `3dd8619`) and chapter 12 of
Shillito's thesis (ANU 2023), which is that paper's content. **The paper
itself was not obtained** (paywall). The system is in
[`GLS/System.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/System.lean); the status board is
[`campaign/README.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/README.md).

**The goals.** Each PROVED statement is checked by the kernel, with no
`sorry`, within `[propext, Quot.sound]` (every theory file ends with
`#axioms_within_file [propext, Quot.sound]`). `Fam s` is the type of
derivations of `s` in GLS; `Valid s` is truth at every world of every
two-valued model of GL. From the standing list first:

    Cut admissibility (thesis Thm 12.7.1), a function, proved twice:
      (A : Form) → (Γ0 Γ1 Δ0 Δ1 : List Form) →
        Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ A :: Δ1) → Fam (Γ0 ++ A :: Γ1 ⇒ Δ0 ++ Δ1) →
        Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ Δ1)
      PROVED  cutAdmissible (GLS/Completeness.lean): by soundness and the search
      PROVED  cutBySource (GLS/Cut.lean): the source's induction; no model, no search

    Cut elimination from GLS + (cut) (thesis Thm 12.7.2), proved twice:
      (s : Seq) → FamCut s → Fam s
      PROVED  cutElimination, cutEliminationBySearch (GLS/CutRule.lean)

    The finite model property:
      ∀ s, (∀ M, M.GL → M.TwoValued → M.Finite → ∀ w, M.satSeq w s) → Valid s
      PROVED  finiteModelProperty (GLS/Completeness.lean)

The others:

    Soundness                ∀ s, Fam s → Valid s                          PROVED  soundness
    Completeness, as data    (s : Seq) → Fam s ⊕ Refutation s              PROVED  proofOrRefutation
    Completeness             ∀ s, Valid s → Nonempty (Fam s)               PROVED  completeness
    Decidability             (s : Seq) → Decidable (Valid s)               PROVED  validDecidable
                             (s : Seq) → Decidable (Nonempty (Fam s))      PROVED  derivableDecidable
    Identity                 (A) → A ∈ Γ → A ∈ Δ → Fam (Γ ⇒ Δ)             PROVED  Fam.id
    Termination of PSGLS     WellFounded PSPrem                            PROVED  psTermination
    PSGLS and GLS            (s : Seq) → (Fam s → PSFam s) × (PSFam s → Fam s)   PROVED  psEquivalent
    Exchange, weakening (left, right), inversion of →R and →L,
    contraction (left, right): seven functions, each returning
      { d' : Fam (…) // d'.height ≤ d.height }                            PROVED  each

A `Refutation s` is a finite tree, as data, at whose root `s` is false.
The seven structural statements are displayed in full in
[`statements.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/statements.md) (S11 to S17).

**OPEN**: nothing. **REFUTED**: nothing.

**Runs**: a proved search that returns a derivation or a countermodel;
certifiers for derivations, against validity and against derivability;
a proof that one side always answers (level 3); a second, unproved
search over sets whose answers are checked. The corpus: 16 sequents, 16
facts checked by the kernel. The frontier: the proved search is cut off
at 28 nested boxes (20 s), because GLR on multisets doubles the
antecedent at each nested box; the search over sets runs 256 nested
boxes in 0.3 s, and the kernel checks its tree of moves in 2 s.
[`measurements.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/measurements.md).

## 2. What to read

No tool checks that these say what the source means. They are what a
reader trusts beyond the kernel.

| definition | file, lines | length | the source's item |
|---|---|---|---|
| formulas, sequents | [`GLS/Form.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Form.lean#L19-L47), 19 to 47 | 29 | `MPropF`, `rel (list …)`; thesis p. 168 |
| `xbox`: `B, □B` for each boxed `□B` of the antecedent | [`GLS/Form.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Form.lean#L49-L56), 49 to 56 | 8 | `XBoxed_list (top_boxes Γ)`; the thesis's `⊠Γ` |
| the family of GLS (with [`rule-table.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/rule-table.md) beside the figure) | [`GLS/System.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/System.lean#L22-L38), 22 to 38 | 17 | `GLS_rules`; thesis Figure 12.1, p. 171 |
| the family of PSGLS, and its three predicates | [`GLS/System.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/System.lean#L40-L67), 40 to 67 | 28 | `PSGLS_rules`; thesis p. 178 |
| GLS + (cut) | [`GLS/CutRule.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/CutRule.lean#L24-L43), 24 to 43 | 20 | thesis p. 171, p. 186 |
| the models, truth, GL, `Valid` | [`GLS/Semantics.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Semantics.lean#L23-L64), 23 to 64 | 42 | thesis Defs 12.2.2, 12.2.3, p. 168; two-valuedness and truth of a sequent are the operator's |
| trees as models, `Refutation` | [`GLS/Semantics.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Semantics.lean#L70-L130), 70 to 130 | 61 | none: the operator's |
| the premise relation of PSGLS | [`GLS/Semantics.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Semantics.lean#L163-L176), 163 to 176 | 14 | the premises of `PSGLS_rules` |
| `step` (S1 and S2 tie it to the family) | [`GLS/Proof.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Proof.lean#L16-L62), 16 to 62 | 47 | |

Total: 266 lines. The statements themselves are 100 more lines of the
same file ([`GLS/Semantics.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/GLS/Semantics.lean#L132-L232),
132 to 232).

## 3. The checks of meaning

| check | run? | what it found |
|---|---|---|
| `#rules` and `#slime`, beside the figure | yes | five rules, six for PSGLS, six for GLS + (cut); no computed index; a control shows `#slime` able to say no |
| the source's worked derivations (8), as terms and by script | yes | all are derivations: the four cases of the Coq file's identity and one more; the thesis's Examples 12.4.1 (three trees) and 12.4.2, with the premise of each GLR checked by `rfl` or up to a permutation |
| the second transcription, by a cold reader | yes, twice | on the Coq file and on the thesis's pages: no difference in any rule; five remarks on the first, settled from the Coq file |
| the reading back of the definitions and the statements | yes | 18 statements read back by cold readers, all agree; S24 was read back after its proof |
| soundness and completeness, before the other goals | yes | both PROVED before goals 3 to 6 |
| S2: `step` refuses no instance of a rule | PROVED | |

Errors of transcription found: 0. What these checks do not show: the
paper's own figure was not seen, so the comparison is with the thesis's
Figure 12.1 and the Coq definitions; of the thesis only chapter 12 was
read (it leans on sections 2.1, 4.2 and 5.1 for notation); the
semantics has a source for one formula on the right (`Γ ⊨ ϕ`) and is
the operator's for a sequent.

## 4. The decisions

The costliest to reverse first, each by its entry in
[`decisions.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/decisions.md).

| decided | not taken | cost to reverse | doubt |
|---|---|---|---|
| `Valid`: truth at every world of every two-valued model of GL (transitive, conversely well-founded) | every model (gives excluded middle from `⇒ p, p → ⊥`); the indirect form; finite models only | the campaign | two-valuedness is the operator's restriction; classically it is no restriction |
| what holds for the explorer's moves is the family, into `Type` | validity as what holds | the campaign | none |
| every theory file within `[propext, Quot.sound]` | choice in the completeness file | the campaign, to tighten later | none: held throughout |
| the rules transcribed from the authors' Coq files while the prose could not be read | to wait for the download | the campaign, had the prose shown another system | settled at 13:21: no difference |
| sequents as two lists read as multisets; a rule removes one occurrence of its principal formula (`List.erase`); `xbox` on the whole antecedent | the Coq form with places in lists; the principal formula kept | a stage | none found: exchange and both weakenings are 171 lines here |
| cut first through the semantics, then by the source's induction | one route only | a stage | that the semantic route is in the literature for GLS rests on a report of Sambin and Valentini 1982, not read |
| a second certifier over sets, with an unproved search and a checked decision | to change the proved search; to leave the frontier at 28 | little | that a tree of moves over sets is always a tree of moves of GLS is not proved |
| goals 4 to 6 handed to an agent by a brief | to write them in the session | little | none: built and run by the operator |

Divergences from the source (`rule-table.md`): W 0, U 1, R 3. Those
that change what a statement says: none (D1: the variables are `Nat`,
where the source has any set with decidable equality).

Exceptions to the axiom policy: none.

## 5. The reviewer's

Stated, and not asked for.

* **Only the reviewer may**: contact the source's authors. Nothing
  arose that needs it: no error was found in the source. Two things an
  author might care to hear: the multiset GLR doubles antecedents under
  nested boxes (section 1, "Runs"), and cut admissibility here also has
  a four-line definition from soundness and the search that proves
  completeness (`cutAdmissible`), beside the source's induction.
* **Still unread**: the paper of 2021 itself. If the reviewer has a
  copy, its figure is to be laid beside `rule-table.md`.
* **To try, at any time**: the exercises
  ([`Play/GLS.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/Play/GLS.lean)) and the tutorial
  ([`Play/GLSTutorial.lean`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/Play/GLSTutorial.lean)), with
  [`users-guide.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/users-guide.md). Every exercise was
  run by script in the tests; no person has typed them.
* **To fill, if the method is to be costed**: the columns of
  [`cost-log.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/cost-log.md) that the operator cannot
  know (requests, tokens, cost).
* **Words of the reviewer during the campaign**: 2: the command, and
  the answer at the one stop (the download of the thesis, asked 08:55,
  answered 13:14). The work did not wait for it.

## 6. Cost, and the method

From the command (08:46) to this page: the clock time at its head. The
five stages ran in 71 minutes (08:46 to 09:57), with the agent's
proofs of goals 4 to 6 committed after the break; nothing ran from
09:57 to 13:14; the comparison with the thesis, cut elimination, one
repair and the closing took the rest. One session and five agents. Lean: 5 103
lines in 35 files, of which about 1 400 are tests, screens, exercises
and the tutorial.

Findings about the library (none was changed):

* `Cert` has no `DecidableEq`: two certificates are compared with `==`.
* A script printed by `Repr` over several lines is not always Lean
  source; the driver prints scripts on one line.
* The line the move tactic offers is placed after comment lines that
  follow a pattern, not only after a comment on the pattern's line.

Changes proposed to the skill, from
[`method-notes.md`](https://github.com/fairflow/proof-tools/blob/96dad49/calculi/GLS/campaign/method-notes.md) (26 notes), each with
its place in the text:

* The first act: downloads (notes 1 to 3). Settled already by commit
  `28e3aa8`.
* `reference/adopt.md` §1: where a source has a published
  formalisation, read its definitions beside the figure and say which
  rules where they differ (note 5); read every figure from the page's
  image, never from extracted text, which here lost `□` (note 23).
* "What a campaign proves": what to do when the source has no
  semantics (note 6).
* `reference/survey.md`: what is owed when the source arrives late: the
  comparison, the skeleton's numbers, a pass over the standing list,
  and nothing else unless a difference is found (note 21).
* Stage 2: the proofs may begin while the reading back runs (note 10);
  a brief that gives the statements as named Lean types and the tests
  to pass is enough to hand goals on, and the agent's files stay out of
  commits until it reports (notes 18, 19).
* `reference/certify.md` §4: add the pattern "an unproved fast search,
  wrapped as `if check then … else the proved decision`" (note 17); §5:
  `maxRecDepth` was tried and works (note 13); macOS has no `timeout`
  (note 15); the lazy kernel can be faster than the compiled producer,
  so measure the check even where the producer is slow (note 16); when
  a second search is slower than the first on a small member, suspect
  the code before the calculus (note 26).
