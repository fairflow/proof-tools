# MALL: the closing page

Written 2026-11-26 11:05 GMT. Commit `10becc3` and this page's own, on `main` of
`fairflow/proof-tools`. To build:

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build MALL mallrun)

Links below are to GitHub at `10becc3`; B is
`https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL`.

**Amended 2026-11-26 14:04 GMT**, at the reviewer's word after this page was first
published: section 7, a countermodel for every sequent with no
derivation. The rest of the page is as it was written.

**Amended again 2026-11-26 15:22 GMT**, by a command relayed from the reviewer: section
8, Craig and uniform interpolation.

## 1. What was adopted, proved, and runs

Propositional multiplicative-additive linear logic, in the one-sided
sequent calculus with cut of J.-Y. Girard, *Linear logic*, TCS 50 (1987),
Definition 1.15, without the exponentials and the quantifiers: ⊗, ⅋,
**1**, ⊥, &, ⊕, ⊤, **0** over letters and their negations, negation a
defined function, ten rules. The semantics is the source's phase
semantics (Definitions 1.1 to 1.14). Lean 4 core only, v4.31.0.

**The goals**, those from the standing list first. Each PROVED statement
is checked by the kernel, with no `sorry`, within `[propext, Quot.sound]`
(every theory file ends with `#axioms_within_file [propext, Quot.sound]`).
`Fam` is the family with cut, `CF` the family without,
`Derivable Γ := Nonempty (Fam Γ)`, `Γ ~ Δ` is `List.Perm`.

    (Γ : List Form) → Fam Γ → CF Γ                                   (cutElimination, MALL/Cut.lean)
    (A : Form) → (Γ Δ : List Form) → CF (A :: Γ) → CF (Aᗮ :: Δ) → CF (Γ ++ Δ)
                                                                     (cutAdmissible, MALL/Cut.lean)
    ∀ Γ, Derivable Γ → Nonempty (CF Γ)                               (cutEliminationProp, MALL/Completeness.lean)
    PROVED: cut elimination, as a function (standing entry 1) and, by a
    second route through the semantics, as a proposition

    ∀ Γ, (∀ S : PhaseStructure, S.Finite → S.Sat Γ) → Derivable Γ    (finiteModelProperty, MALL/FiniteModel.lean)
    PROVED: the finite model property (standing entry 2; Lafont 1997, Theorem 2)

    ∀ Γ, Derivable Γ → Valid Γ                                       (soundness, MALL/Soundness.lean)
    PROVED: Girard, Proposition 1.16

    ∀ Γ, Valid Γ → Nonempty (CF Γ)                                   (completeness, MALL/Completeness.lean)
    PROVED: Girard, Theorem 1.17, in the stronger form without cut (Lafont, Theorem 1)

    (Γ : List Form) → Decidable (Derivable Γ)                        (derivableDecidable, MALL/Results.lean)
    (Γ : List Form) → Decidable (Valid Γ)                            (validDecidable, MALL/Results.lean)
    PROVED: decidability (LMSS 1992, Theorem 2.2), by a search proved complete; the kernel runs it

    ∀ A B, Derivable [A ⊕ B] → Derivable [A] ∨ Derivable [B]         (disjunctionProperty, MALL/Results.lean)
    PROVED: the disjunction property for ⊕ (standing entry 6), for a sequent of one formula

    ∀ Ξ (d : CF Ξ), d.All fun Θ => ∀ C ∈ Θ, ∃ D ∈ Ξ, C.IsSub D       (subformulaProperty, MALL/Results.lean)
    PROVED: the subformula property (LMSS, Corollary A.4)

    ∀ Γ Γ' (e : Γ ~ Γ') (d : Fam Γ), (d.exch e).height = d.height    (exchangeKeepsHeight, MALL/Results.lean)
    PROVED: exchange, with the height kept. Trivial by the encoding; what has content is that the
    figure as it stands (`Lit`, with a rule EXCH) derives the same sequents (lit_iff_fam, MALL/Source.lean)

    (Γ : List Form) → CF Γ → { d : CF Γ // d.Atomic }                (identityExpansion, MALL/Results.lean)
    PROVED: the logical axiom restricted to letters (Girard, p. 22)

    CF (A ⅋ B :: Γ) → CF (A :: B :: Γ);   CF (⊥ :: Γ) → CF Γ;
    CF (A & B :: Γ) → CF (A :: Γ) × CF (B :: Γ)                      (parInversion, botInversion, withInversion, MALL/Cut.lean)
    PROVED: the inversions

**OPEN**: nothing.

**REFUTED**, as the source says they must be, each by a pair of sequents
decided in the kernel (`MALL/Results.lean`):

    ∀ Γ A, Derivable Γ → Derivable (A :: Γ)              weakening:   ⊢ 1 is derivable, ⊢ 1, 1 is not      (not_weakening)
    ∀ Γ A, Derivable (A :: A :: Γ) → Derivable (A :: Γ)  contraction: ⊢ a ⊕ a⊥, a ⊕ a⊥ is, ⊢ a ⊕ a⊥ is not  (not_contraction)

Nothing replaced them.

**Not goals**: PSPACE-completeness (it needs a theory of machines);
normalisation and confluence, which the source has for proof nets,
another system; deduction theorems and the existence property, which do
not apply. Each with its reason in [statements.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/statements.md).

**Runs**, at level 3 (one side always answers: `decided`,
`MALL/Run.lean`):

* for a derivation, a tree of moves whose ⊗ and cut moves name the
  split, checked by the kernel (`treeCert`). Two producers: the proved
  search, and a search by lazy splitting (input and output contexts,
  after Hodas and Miller and Cervesato, Hodas and Pfenning) that is not
  proved and not trusted. The lazy search takes 3 ms at 66 formulas; the
  kernel checks its tree in 3 to 6 s;
* against a derivation, either the kernel runs the proved search
  (practical to between 6 and 12 formulas where ⊗ must split), or it
  checks a finite phase structure on a cyclic group, given as data
  (`noDerivableBy`, `MALL/ModelRun.lean`): 0.8 to 1.5 s at 130 formulas;
* **the frontier**: a sequent with no derivation, ten or more formulas
  with ⊗, and no countermodel among the small structures the producer
  tries. The finite model property says a finite structure exists; the
  producer of structures is not complete (it settles 14 of the 15
  non-theorems of the corpus). [measurements.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/measurements.md).

## 2. What to read

No tool checks that these say what the source means. They are what a
reader trusts beyond the kernel.

| definition | file, lines | length | the source's item |
|---|---|---|---|
| formulas, linear negation | [Form.lean, 18-69](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Form.lean#L18-L69) | 50 | Girard, p. 21 |
| judgments | `List Form`, read as a multiset | | Definition 1.15; p. 24 |
| the family of rules, with [rule-table.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/rule-table.md) beside the figure | [System.lean, 30-84](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/System.lean#L30-L84): `Fam` and `CF`; the figure as it stands, `Lit`: [Source.lean, 22-47](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Source.lean#L22-L47) | 30, 25, 26 | Definition 1.15 |
| phase spaces, duals, facts, products | [Semantics.lean, 18-49](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Semantics.lean#L18-L49) | 33 | Definitions 1.1, 1.2, 1.3, 1.8 |
| phase structures, the interpretation | [Semantics.lean, 55-81](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Semantics.lean#L55-L81) | 28 | Definition 1.14; 1.5, 1.7, 1.8, 1.11 |
| a sequent in a structure, `Valid`, a finite structure | [Semantics.lean, 88-103](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Semantics.lean#L88-L103) | 14 | the proof of 1.16, p. 23; Lafont, p. 3 |
| the moves and `step` (S1 and S2 tie it to the family) | [Proof.lean, 18-81](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Proof.lean#L18-L81) | 64 | (ours) |

Total: about 270 lines. The goals as named statements, 141 lines:
[Statements.lean](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/MALL/Statements.lean).

## 3. The checks of meaning

| check | run? | what it found |
|---|---|---|
| `#rules` and `#slime`, beside the figure | yes | 10 rules of `Fam`, 9 of `CF`, 11 of `Lit`, each as the figure; no computed index in a conclusion |
| the source's worked derivations | the source draws none for this fragment | ten derivations of what it asserts stand in (`MALL/Source.lean`), as terms and by script |
| the second transcription, by a cold reader given four page images | yes | 11 rules in both readings, no difference; five ambiguities of the figure settled the same way by both |
| the reading back of the definitions and the statements, by a cold reader given an extract of 230 lines | yes | no definition or statement says other than what was meant. It found the refutations of weakening and contraction unprompted; its remark that validity is written through an order-dependent formula led to `valid_perm`. The model certifier (S19), written later, was not read back |
| soundness and completeness, before the other goals | yes | both PROVED, with no excluded middle; so the rules are fixed against the source's semantics |
| S2: `step` refuses no instance of a rule | PROVED | `famToDer`, `MALL/Proof.lean` |

Errors of transcription found: none, by any check. What these checks do
not show: both cold readers are the same model as the operator, so a
misreading shared by all three would pass; the phase semantics was
transcribed by the operator alone and checked only by the reading back
and by soundness and completeness holding together (a wrong semantics
for which both still hold is unlikely, not excluded). LMSS was read by
an agent, not by the operator. Lafont is cited from the author's
version, whose page numbers may differ from the journal's.

One departure from rule 2 of the skill: the goals were fixed as named
Lean types before any proof (commit `c81bc59`, 10:22), but the document
`statements.md` was first committed at 10:56, after the proofs.

## 4. The decisions

The costliest to reverse first; each is an entry of
[decisions.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/decisions.md).

| decided | not taken | cost to reverse | doubt |
|---|---|---|---|
| what `Valid` means: truth of the par of the sequent at the unit of every phase structure, the carrier in `Type`, sets as predicates | two-valued structures only; universe polymorphism | the campaign | none found: soundness and completeness are constructive, so the direct statement costs nothing |
| the axiom bound `[propext, Quot.sound]` | allowing `Classical.choice` | the campaign, to tighten | core Lean's permutation lemmas use choice, so the campaign has its own (`MALL/Perm.lean`, 177 lines) |
| **the split of ⊗, and exchange**: a sequent is a list; every rule concludes a variable `Ξ` under `Ξ ~ A ⊗ B :: (Γ ++ Δ)` (and so for each rule); EXCH is a function, not a rule | the figure as the working family; membership with `erase`; a Boolean mask; a quotient | a stage and every proof after it | it is the source's own "variant without exchange, adapted to multisets" (p. 24), and `Lit` is proved equivalent. Its price: constructors take their formulas and contexts explicitly |
| two families, `Fam` and `CF`, into `Type`; what holds is `Fam` | one family with a flag; a predicate "no cut" | a stage | none |
| cut elimination by structural recursion: a bound on the size of the cut formula, then the left derivation, then the right | a sum of heights (not needed: no rule uses a premise twice) | a stage | written by an agent from the operator's design; built, read and tested by the operator |
| completeness stated without cut; Okada's lemma proved once for an abstract model; the finite model by "small" sequents in place of Lafont's order ⊑ | Girard's own proof with cut; ⊑ as an inductive relation | a stage; little | the finite model is larger than Lafont's; the theorem is the same |
| the moves name the split: `tensor A B [Γ]`, `cut A [Γ]` | both contexts; a mask; positions | little | none |
| finite phase structures on cyclic groups as certificates | an arbitrary finite monoid by its table | little | the producer is not complete |
| the connective "with" is `wth`; `⊕` kept as the notation | `with` (a keyword); another glyph | little | `⊕` needs parentheses before `::` and `∈` |

Divergences from the source ([rule-table.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/rule-table.md)):
W 0, U 3 (which letters are lists; contexts may be empty; one letter
for each natural number), R 3 (multisets and EXCH as a function;
equations in `Lit` for computed indices; `wth`). None changes what a
statement says, given `lit_iff_fam`.

Exceptions to the axiom policy: none.

## 5. The reviewer's

Stated, and not asked for.

* **Only the reviewer may**: nothing arose. No author was contacted;
  nothing was published; the push is to `main`, as the task said.
* **To try, at any time**: the exercises
  ([Play/MALL.lean](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/Play/MALL.lean), ten) and the tutorial
  ([Play/MALLTutorial.lean](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/Play/MALLTutorial.lean), eight
  sections); [users-guide.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/users-guide.md). Every
  exercise was run by script in the tests; no person has typed them.
* **To fill, if the method is to be costed**: requests, tokens and cost
  of the session ([cost-log.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/cost-log.md)).
* **Words of the reviewer during the campaign**: none. No stop.

## 6. Cost, and the method

From the task to the last build: 74 minutes (09:46 to 11:00); to this
page, the time at its head. No time at a stop. One session, five agents
(survey, second transcription, cut elimination, the decision procedure,
the reading back: 26 minutes of their own time in all, partly in
parallel). 6 051 lines of Lean, of which 1 760 are tests, the
corpus and its generated facts; about 3 000 lines of documents.

**Not done**: a tutorial as a Markdown page with pins (the tutorial is
the Lean file, its claims pinned in `MALL/ExploreTest.lean`); Okada's
paper (TCS 227, 1999) was not obtained, and Lafont's proof of the lemma
was used; the two agents' briefs for Prove were given in the session
and are not kept as files; an unexplained variation in one timing
(`fanBad 32`: 0.5 s to 8.4 s) is reported as it is.

Findings about the library (none was changed):

* `perm_count` and the permutation lemmas free of `Classical.choice`
  are now written twice (GLS and here) and phase 2 will want them a
  third time: they belong in the library.
* A certifier whose certificate is `Unit` and whose check is a proved
  decision procedure gives an engine and level 3 with no written
  countermodel: `reference/certify.md` might say so.

Changes proposed to the skill, from
[method-notes.md](https://github.com/fairflow/proof-tools/blob/10becc3/calculi/MALL/campaign/method-notes.md) (22 notes); the ones
that would change its text most:

* `reference/adopt.md` §3: a third form for "judgments as data", for
  a calculus without weakening: a variable conclusion under a
  permutation hypothesis, with what it costs (note 1);
* §6: the list of where `Classical.choice` enters is short by the
  permutation lemmas (note 2);
* rule 5: an agent's half-written files are compiled by a default
  build under a glob; build by target (note 8); a brief should name
  the names already taken (note 9);
* `reference/certify.md` §4: where the proved search is the slow one,
  the "no" side wants a certificate of its own, and a finite model
  property is where it comes from (note 16);
* rule 6: say whether a certifier that the measurements show to be
  missing comes before the page (note 17);
* pitfall 11 as an order of work: evaluate, read, paste (note 18).

**For phase 2** (dual intuitionistic linear logic): the linear zone
takes this campaign's rule format and `MALL/Perm.lean` as they stand;
the intuitionistic zone takes membership, as in GLS; the cut measure
covers a cut on a linear formula, and a cut on the intuitionistic zone
wants a substitution function of its own; the decision procedure does
not carry over with `!`; the lazy search does. The end of
`method-notes.md` has each.

## 7. After the closing page: a countermodel for every sequent with no derivation

Asked by the reviewer: "Can you complete the counter model construction?
Decidability + completeness means there must be one." Commit `e2ba9e5`.

The producer of cyclic structures (section 1, "Runs") settled 14 of the
15 non-theorems of the corpus and could not be complete. There is now a
second certificate, which is:

    ∀ (D : List (List Form)) (Γ : List Form), refutedBy D Γ = true →
      ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat Γ                      (countermodel_of_refutedBy, MALL/Saturated.lean)
    PROVED: a saturated set of sequents presents a finite countermodel

    ∀ Γ, ¬ Derivable Γ → refutedBy (fullRefutation Γ) Γ = true         (refutation_complete, MALL/Saturated.lean)
    ∀ Γ, (∃ c, treeCert.check Γ c = true) ∨ (∃ D, noDerivableBySet.check Γ D = true)
                                                                       (certified, MALL/SatRun.lean)
    PROVED: the certificate is complete; every sequent has a written certificate, checked by the kernel

Both within `[propext, Quot.sound]`. Statements S20 and S21 of
[statements.md](https://github.com/fairflow/proof-tools/blob/e2ba9e5/calculi/MALL/campaign/statements.md).

**What to read** (two definitions, 22 lines):
[Saturated.lean, 58-75](https://github.com/fairflow/proof-tools/blob/e2ba9e5/calculi/MALL/MALL/Saturated.lean#L58-L75): `satAt` and
`saturated`. A set `D` is saturated when no member is `⊢ a, a⊥`, `⊢ 1` or
has ⊤, and at each formula of each member the rule that introduces it has
a premise in `D`: the premise of ⅋ and of ⊥; one of the two of &; both
that of 1⊕ and that of 2⊕; for every way to divide the context of a ⊗,
one of the two. `refutedBy D Γ` adds that `Γ` is a member.

**The countermodel** that a set presents (`satModel`): phases are the
parts of the members, with one more phase for all other sequents;
antiphases are the phases that are not members; the fact of a letter `a`
is `{a}⊥`. That no member holds in it is Okada's lemma, already proved
for completeness. The kernel checks the saturation and computes no
interpretation. As a check of meaning the structure is also computed by
tables in compiled code (not proved): for each of the 15 non-theorems,
no member of its set holds in the computed structure and all 23
derivable entries of the corpus do.

**The producer** (`refuteSet`, `MALL/Refute.lean`, not trusted): a search
that remembers every sequent it settles; where it says no, the sequents
it said no of are a saturated set. It ends on every input and never
returns nothing for a sequent with no derivation: the search space of
one sequent is finite. `halfDistribConv`, the entry the cyclic producer
missed, gets a set of 17 sequents (a structure of 35 phases).

**Its limit**, measured ([measurements.md](https://github.com/fairflow/proof-tools/blob/e2ba9e5/calculi/MALL/campaign/measurements.md)):
the set is exponential where ⊗ divides a context many ways (1 015
sequents at 7 formulas on `chainBad`), and the kernel's check, quadratic
in the set, passes a minute from about 300 sequents (86 sequents: 3.4 s).
On those families the cyclic structures remain the certificate to use.
So the frontier of section 1 is now a limit of size and not of method.

Not read back by a cold reader. Seven negative tests in the kernel
(`MALL/SatTest.lean`).

**The tutorial** (2026-11-26 14:11 GMT): `calculi/MALL/tutorial.md`, in the pinned
format of the GLS one: 25 graded exercises in five parts, 16 pinned
statements, both certificates of non-derivability explained. Written by
an agent of the operator; the operator ran the pin check and the build
and read the section on the certificates, not the whole page. Its
solutions are checked by the build (`MALL/TutorialTest.lean`); the
exercises to type are `Play/MALLExercises.lean`. The prose on how each
proof goes is a reading and is not checked. No person has typed the
exercises.

## 8. Interpolation

By command ("Yes, for MALL"; `decisions.md`). Commit `fe73047`. Statements
S22 to S25 of [statements.md](https://github.com/fairflow/proof-tools/blob/fe73047/calculi/MALL/campaign/statements.md), entered as
named types before their proofs.

    (Γ Δ : List Form) → CF (Γ ++ Δ) → Interpolant Γ Δ                  (craigInterpolation, MALL/Craig.lean)
      where an Interpolant Γ Δ is C with CF (C :: Γ), CF (Cᗮ :: Δ) and
      ∀ ℓ ∈ C.lits, ℓᗮ ∈ litsL Γ ∧ ℓ ∈ litsL Δ
    PROVED: Craig interpolation with Lyndon's condition, as a function on derivations without cut

    ∀ A B, Derivable [Aᗮ, B] → ∃ C, Derivable [Aᗮ, C] ∧ Derivable [Cᗮ, B] ∧
      ∀ a ∈ C.letters, a ∈ A.letters ∧ a ∈ B.letters                   (craigForFormulas, MALL/Craig.lean)
    PROVED: Craig interpolation for an implication

    ∀ (p : Nat) (Γ : List Form), ∃ I : Form,
      (∀ a ∈ I.letters, a ≠ p ∧ a ∈ lettersL Γ) ∧ Derivable (Iᗮ :: Γ) ∧
      ∀ Δ, (∀ a ∈ lettersL Δ, a ≠ p) → Derivable (Γ ++ Δ) → Derivable (I :: Δ)
                                                                       (uniformInterpolation, MALL/Uniform.lean)
    PROVED: uniform interpolation; the interpolant is the function ui p Γ (ui_spec)

    the same for a formula: ∀p A := forallP p A and ∃p A := existsP p A  (uniformInterpolationForFormulas)
    PROVED

All within `[propext, Quot.sound]`.

**What to read** (about 50 lines with their comments): [Statements.lean, 139-190](https://github.com/fairflow/proof-tools/blob/fe73047/calculi/MALL/MALL/Statements.lean#L139-L190),
the four statements; and `Form.lits`, `Form.letters`
([Form.lean, 99-127](https://github.com/fairflow/proof-tools/blob/fe73047/calculi/MALL/MALL/Form.lean#L99-L127)). To know which
interpolant: `uiBase`, `uiPick`, `uiStep`, `uiN`
([Uniform.lean, 69-107](https://github.com/fairflow/proof-tools/blob/fe73047/calculi/MALL/MALL/Uniform.lean#L69-L107)).

**Craig** is Maehara's method by structural recursion on the derivation,
for every division of its sequent; the condition on signs costs nothing
in negation normal form. Written by an agent from the operator's design
and inspected by the operator. Sixteen interpolants are pinned by the
kernel.

**Uniform** interpolation is by Pitts's method: the interpolant is the ⊕
of one formula for each way a derivation of `⊢ Γ, Δ` can end that
concerns `Γ`, by recursion on a bound of the size, simplified as it is
built; that it is the weakest is by induction on a derivation without
cut. The kernel computes it:

    ∀p (p ⅋ p⊥) = 1       ∀p (p⊥ ⅋ (p ⊗ q)) = q       ∃p (p ⊗ q) = ⊤ ⊗ q       ∃p (p & q) = q

(the third is not `q`: there is no weakening).

**The checks.** The statement of uniform interpolation was screened
before its proof: 21 formulas, both properties, against the decision
procedure over 264 test formulas, no failure. A cold reader given the
definitions and the four statements unnamed identified each and found
none false or trivial. It asked for one more statement, a condition on
signs for the uniform interpolant. The session that started this one
then made it a goal (its decision, not a word of the reviewer), and it
is S26:

    ∀ (p : Nat) (Γ : List Form), ∃ I : Form, (∀ ℓ ∈ I.lits, ℓ ∈ litsL Γ) ∧ … the three clauses above …
                                                                       (uniformInterpolationLyndon, MALL/UniformLyndon.lean)
    PROVED: every literal of ui p Γ is a literal of Γ; and every literal of ∀p A and of ∃p A a literal of A

Both forms were screened before the proof on 46 formulas for two
letters, with the other polarity for `∃p A` as a control, which fails on
21 of them. None of the sources read states such a condition.

**The sources** were read by an agent after the proofs
([interpolation-sources.md](https://github.com/fairflow/proof-tools/blob/fe73047/calculi/MALL/campaign/interpolation-sources.md)):
uniform interpolation for this logic is Theorem 4.3 of Alizadeh,
Derakhshan and Ono (2014), who call it InFLₑ and write no proof for this
case, and is covered by Akbar Tabatabai and Jalali (arXiv:1808.06258),
who call it CFLₑ; Lyndon's condition is in Roorda's thesis (1991). None
of the four reports a mechanised proof; that is a statement about those
four texts. The construction here was made before they were read and is
of the same kind as the first paper's table.

**Not done.** Roorda's fragment without interpolation, (⊸, ⅋), as a
REFUTED statement: his paper (JSL 1994) was not obtained; the thesis has
the counterexample but its proof was not read, and it is for a counting
form of the condition. The interpolant of a sequent of several formulas
is long: it is not simplified up to commutativity.

**The tutorial** has a section 5.8 with the two statements pinned and
three exercises (D6 to D8), their solutions checked by the build.

