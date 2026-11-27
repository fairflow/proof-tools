# DILL: the closing page

Written 2026-11-26 16:24 GMT, completed 16:33. The Lean of the theorems is at commit `5850b99`
on `main` of `fairflow/proof-tools`; this page and the tutorial are in
later commits of the same branch. To build:

    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake build DILL dillrun)

Links below are to GitHub at `5850b99`; B is
`https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL`.

Delivered 2026-11-26 16:34 GMT: on `main` (this file), and as a private
page for the reviewer, https://claude.ai/artifact/VNyYCXMHeVzVx1fCGvwopH
(as of commit `47234be`).

## 1. What was adopted, proved, and runs

Dual intuitionistic linear logic as a sequent calculus with two zones,
`Γ ; Δ ⟹ C`: `Γ` the valid (unrestricted) hypotheses, `Δ` the linear
ones, one conclusion; ⊗, 1, ⊸, &, ⊤, ⊕, 0 and `!` over atoms. The source
is B.-Y. E. Chang, K. Chaudhuri and F. Pfenning, *A judgmental analysis
of linear logic*, CMU-CS-03-131R (revised December 2003), Figure 2: the
eighteen rules of that figure for a goal that is true, without `?` and
the possibility judgment, and the two cuts of its Principle 7. The name
and the two zones are A. Barber's (ECS-LFCS-96-347, 1996). The paper is
proof theory only; the semantics is the intuitionistic phase semantics
of Kanovich, Okada and Terui (2006). Lean 4 core only, v4.31.0.

**The goals**, those from the standing list first. Each PROVED statement
is checked by the kernel, with no `sorry`, within `[propext, Quot.sound]`
(every theory file ends with `#axioms_within_file [propext, Quot.sound]`).
`Fam true` is the calculus with the two cuts, `CF = Fam false` the
figure, `Derivable j := Nonempty (Fam true j)`; `Γ ⨾ Δ ⟹ C` is how Lean
writes the sequent.

    (Γ Δ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ Δ ⟹ A) → CF (Γ ⨾ A :: Δ' ⟹ C) → CF (Γ ⨾ Δ ++ Δ' ⟹ C)
    (Γ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ [] ⟹ A) → CF (A :: Γ ⨾ Δ' ⟹ C) → CF (Γ ⨾ Δ' ⟹ C)
    (j : Seq) → Fam true j → CF j                             (cutAdmissible, cutUAdmissible, cutElimination, DILL/Cut.lean)
    ∀ j, Derivable j → Nonempty (CF j)                        (cutEliminationProp, DILL/Completeness.lean)
    PROVED: both cuts admissible without cut, and cut elimination (standing entry 1; the source's Theorem 3),
    as functions that the kernel runs, and a second time as a proposition, through the semantics

    ∀ Γ Δ A B, Derivable (Γ ⨾ A :: Δ ⟹ B) ↔ Derivable (Γ ⨾ Δ ⟹ A ⊸ B)
    ∀ Γ Δ A C, Derivable (A :: Γ ⨾ Δ ⟹ C) ↔ Derivable (Γ ⨾ (!A) :: Δ ⟹ C)       (deductionLinear, deductionUnrestricted, DILL/Invert.lean)
    PROVED: the two deduction theorems (standing entry 3): a linear hypothesis is discharged by ⊸, a valid one by !

    ∀ A B, Derivable ([] ⨾ [] ⟹ A ⊕ B) → Derivable ([] ⨾ [] ⟹ A) ∨ Derivable ([] ⨾ [] ⟹ B)   (disjunctionProperty, DILL/Goals.lean)
    PROVED: the disjunction property (standing entry 6), and consistency: ¬ Derivable ([] ⨾ [] ⟹ 𝟎)

    ∀ j, Derivable j → Valid j                                (soundness, DILL/Soundness.lean)
    ∀ j, Valid j → Nonempty (CF j)                            (completeness, DILL/Completeness.lean)
    PROVED: soundness and completeness without cut for the phase semantics (holds of the logic, proved elsewhere
    for one zone: Kanovich, Okada, Terui, Theorem 2.9 and Remark 2.11); so Valid j ↔ Derivable j

    Fam c (Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C);   Fam c (A :: A :: Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)   (weakeningU, contractionU, DILL/Results.lean)
    PROVED: weakening and contraction of the unrestricted zone (the source's Theorem 2); exchange in both zones, the height kept

    the inversions of ⊗L, 1L, ⊸R, &R, ⊕L, !L, and of !R at an empty linear zone                (DILL/Invert.lean)
    PROVED: the source's Lemma 6, the invertible rules, each a function on derivations without cut

    (j : Seq) → CF j → { d : CF j // d.Atomic }               (identityExpansion, DILL/Results.lean)
    ∀ j (d : CF j), d.All fun j' => ∀ C ∈ j'.forms, ∃ D ∈ j.forms, C.IsSub D        (subformulaProperty, DILL/Results.lean)
    PROVED: init at atoms only derives the same; the subformula property

    Fam c (Γ ⨾ Δ ⟹ C) → ILL c (Γ.map Form.bang ++ Δ) C;   ILL true (Γ.map Form.bang ++ Δ) C → Fam true (Γ ⨾ Δ ⟹ C)
    ∀ Γ Δ C, Derivable (Γ ⨾ Δ ⟹ C) ↔ ILLDerivable (Γ.map Form.bang ++ Δ) C      (toILL, ofILL, illEquivalence, DILL/Translate.lean)
    PROVED: `Γ ; Δ ⟹ C` exactly when `!Γ, Δ ⊢ C` in one-zone intuitionistic linear logic (the source's Theorem 7, items 1 and 3)

    (Δ : List Form) → (C : Form) → (∀ A ∈ C :: Δ, A.bangFree = true) → Decidable (Derivable ([] ⨾ Δ ⟹ C))   (bangFreeDecidable, DILL/Goals.lean)
    PROVED: derivability is decidable where `!` does not occur and the unrestricted zone is empty; the kernel runs it

**OPEN**: nothing.

**REFUTED**, as the source says they must be, each by a pair of sequents
that the kernel decides (`DILL/Goals.lean`; the table in
[statements.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/statements.md)
has each pair):

    weakening of the linear zone:    · ; · ⟹ 1 is derivable,        · ; a ⟹ 1 is not          (not_weakeningL)
    contraction of the linear zone:  · ; a, a ⟹ a ⊗ a is derivable, · ; a ⟹ a ⊗ a is not      (not_contractionL)
    the inversion of ⊗R, ⊸L, &L₁, &L₂, ⊕R₁, ⊕R₂ (the source's Lemma 6, "non-invertible"): six statements,
    each at a sequent with the same connective on both sides                                   (not_tensorRInv, …)

Nothing replaced them.

**Not goals**: the source's Theorems 4 and 5 against natural deduction
(another system, left out at the first act); the finite model property,
which fails with `!`; undecidability with `!` (cited, not proved);
normalisation and confluence (the sequent calculus has no terms). Each
with its reason in `statements.md`.

**Runs**, at level 2, as the plan set it: with `!` derivability is
undecidable, so no pair of sound checks can always answer.

* **For a derivation**: a tree of moves, checked by the kernel
  (`treeCert`, `DILL/Run.lean`); its ⊗R, ⊸L and cut moves name the
  division of the linear zone. The producer (`DILL/Lazy.lean`, not
  trusted) is a search without cut that passes the whole linear zone to
  the first premise and gives the rest to the second, with a budget on
  the uses of copy along a branch; found nothing at a budget is `flag`,
  never "no". On the corpus (56 sequents: 39 derivable, 17 not)
  every derivable entry is found, with a tree the checker accepts, at a
  budget of at most 2 copies, and the 17 others are flagged; the search
  agrees with the proved decision wherever both apply.
* **Against a derivation**, two certificates. (a) A saturated set of
  sequents, the record of a failed search (`refutedBy`,
  `not_cf_of_refutedBy`, `DILL/Saturated.lean`; `noDerivableBySet`,
  `DILL/SatRun.lean`): its soundness is proved from the rules alone, by
  induction on a derivation without cut, with no semantics. Proved with
  it: no saturated set has a member with a formula in its unrestricted
  zone, or with `!A` in its linear zone, so this certificate exists only
  where the failed search meets neither. (b) Where `!` does not occur
  and the unrestricted zone is empty, the kernel runs the proved search
  (`noDerivableDec`), and there one side always answers
  (`decidedBangFree`, `DILL/Engine.lean`).
* **The frontier**. For a derivation: the search answers three growing
  families at 1024 formulas in about 10 ms (not taken further), and the
  limit is the kernel's check of the tree as a stated fact: a chain of
  64 formulas in 8 s, not settled at 96 (with Lean's limits lifted, the
  kernel passes 8 GB there). The cost is in `step`: its check of a
  division of the linear zone is quadratic in the zone at every ⊗R and
  ⊸L; a check in one pass is named in the measurements, not made.
  Against a derivation: a set of 200 sequents is
  checked in about 19 s and one of 499 not in 120 s (a chain of seven
  and of eight formulas with its last link missing; the set is
  exponential there whatever the producer), and on that family the
  kernel running the proved search is the cheaper (35 s at nine
  formulas, not settled at ten in 120 s). A sequent with no derivation
  whose search puts a formula into the unrestricted zone, such as
  `· ; !p ⟹ q`, has no certificate of either kind: `flag`, by the
  plan. `campaign/measurements.md` (for a derivation; measuring was
  stopped by the operator before every family reached its limit, and the
  file says where) and
  [measurements-sat.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/measurements-sat.md).

## 2. What to read

No tool checks that these say what the source means. They are what a
reader trusts beyond the kernel.

| definition | file, lines | length | the source's item |
|---|---|---|---|
| formulas | [Form.lean, 17-36](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Form.lean#L17-L36) | 20 | CCP p. 1, p. 3 |
| sequents | [Form.lean, 86-98](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Form.lean#L86-L98) | 13 | CCP pp. 10-11 |
| the family of rules, with [rule-table.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/rule-table.md) beside the figure | [System.lean, 37-101](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/System.lean#L37-L101) | 65 | CCP Figure 2, p. 12; Principle 7, p. 11 |
| phase spaces, the sets `1` and `I`, closed sets | [Semantics.lean, 22-66](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Semantics.lean#L22-L66) | 45 | KOT Definitions 2.2, 2.4 |
| models, the interpretation | [Semantics.lean, 73-99](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Semantics.lean#L73-L99) | 27 | KOT Definitions 2.6, 2.4 |
| a sequent as a formula, `Sat`, `Valid` | [Semantics.lean, 102-118](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Semantics.lean#L102-L118) | 17 | KOT Definition 2.6; the formula of a sequent is ours |
| the one-zone calculus | [ILL.lean, 26-81](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/ILL.lean#L26-L81) | 56 | KOT Figure 1, p. 4, without ⊥ |
| the moves and `step` (S1 and S2 tie it to the family) | [Proof.lean, 19-141](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Proof.lean#L19-L141) | 123 | (ours) |
| a saturated set, `refutedBy` | [Saturated.lean, 74-169](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Saturated.lean#L74-L169) | 96 | (ours) |

Total: about 460 lines. The goals as named statements, 275 lines:
[Statements.lean](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/DILL/Statements.lean).

## 3. The checks of meaning

| check | run? | what it found |
|---|---|---|
| `#rules` and `#slime`, beside the figure | yes | 20 rules of `Fam`, 20 of `ILL`, each as its figure; no computed index. One misprint of the source: Figure 2 prints the conclusions of ⊕R₁ and ⊕R₂ with `A & B` (divergence W1) |
| the sources' worked derivations | yes: 13, as terms (`DILL/Source.lean`) and again by the tactic (`DILL/Test.lean`) | CCP draws three (pp. 16-18) and the inversion of ⊸R by cut; the seven laws of `!` are derivations of what the sources assert, chosen by the operator. The map out of each derivation built by the tactic is equal by `rfl` to the term |
| the second transcription, by a cold reader given four page images | yes | 20 rules in both readings for each calculus, no difference. It found the misprint W1 unprompted, and two more on those pages that touch no rule |
| the reading back, by a cold reader given an extract of 491 lines | yes | no definition or statement says other than what was meant. It gave, unprompted, an instance against each of the eight statements expected false; its remark that the formula of a sequent depends on the order of the hypotheses led to `valid_perm`; its remark that a type of functions says no more than its proposition is answered by the bound on axioms and by the kernel running each. The certifiers' statements (saturated sets, the engine) were not read back |
| soundness and completeness | yes, both PROVED, with no excluded middle | so the rules are fixed against a semantics stated without them. They were proved at the same time as the other goals, not before them (five agents at once) |
| S2: `step` refuses no instance of a rule | PROVED | `famToDer`, `DILL/Proof.lean` |

Errors of transcription found: none, by any check. What these checks do
not show: the cold readers are the same model as the operator, so a
misreading shared by all would pass. The semantics was taken from a
paper on one-zone logic with ⊥; nothing read states it for two zones,
and the formula of a sequent, the canonical model of pairs (a set and a
multiset) and the theorem that a saturated set refutes its members are
the campaign's own. The survey of the literature was made by an agent;
the operator read from the page only CCP §3, its Theorem 7, and KOT
pp. 3-4. The fetched papers were in a scratch folder that the machine's
restart cleared: their addresses and sizes are in the first entry of the
decisions and in the survey report.

Departures from the skill's order: `statements.md` was first written at
15:27, seven minutes after the proofs were begun (the statements were
fixed as named Lean types in a commit before any proof); the reading
back came in while proofs were being made, and faulted none.

## 4. The decisions

The costliest to reverse first; each is an entry of
[decisions.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/decisions.md).

| decided | not taken | cost to reverse | doubt |
|---|---|---|---|
| the source: the fragment of CCP's Figure 2 for a true goal, without `?`; the two cuts as rules of a second calculus | JILL whole; Pfenning's 2002 notes as the source of record (they ask not to be cited; read for consistency, the disjunction property and identity expansion, which only they state); Barber's natural deduction | the campaign | each of the paper's theorems is stated for JILL; the plan says why each holds of the fragment (a derivation without cut of a sequent of the fragment uses its rules only) |
| what `Valid` means: KOT's intuitionistic phase models, `!X := Cl(X ∩ I)` with `I` the strict idempotents of `1`; a sequent read as the formula `(!Γ ⊗ Δ ⊗ 1) ⊸ C` | Okada and Terui's models with a chosen submonoid of weak idempotents (more models: its soundness says more, its completeness less); two-valued models only (not needed) | two theorems | the semantics is "of the logic, proved elsewhere", for one zone |
| the axiom bound `[propext, Quot.sound]` | `Classical.choice` for completeness | the campaign, to tighten | none: the canonical model is a quotient |
| the encoding: `Seq` a structure; the linear zone in MALL's form (a variable zone under a permutation); the unrestricted zone by membership; one family with a Boolean for the cuts | two families; three indices; a multiset type | a stage and every proof after it | functions on the family must be stated over a variable sequent or Lean compiles them by well-founded recursion, silently (found by two agents; repaired with no statement changed) |
| cut elimination by structural recursion on a bound of the cut formula's size, the linear cut before the unrestricted one, with three unrestricted zones in the statement proved | heights; weakening inside the recursion | a stage | written by an agent from the operator's design; built and run by the operator |
| Run at level 2; a saturated set with a syntactic soundness proof; level 3 only where `!` does not occur | a phase model from the set (MALL's route); a search for sets under subsumption | a stage | the set is exponential where a zone divides many ways |
| the sign `⨾` between the zones; `(!A)` and `(A ⊕ B)` in parentheses where anything follows | `;` (it is Lean's between tactics: the first build failed); another glyph for `!` | little | a user must type `⨾`, and meets errors about `Bool` and `Sum` without the parentheses |
| the moves of the right rules name their formula (`tensorR A B Δ`); moves offered in the order of what loses nothing | `tensorR Δ` | little | none |

Divergences from the source ([rule-table.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/rule-table.md)):
W 1 (the misprint), U 4 (what `Γ` is; init at every formula; the atoms;
empty zones), R 5 (the two zones as lists; one family with a parameter;
`⨾`; the moves of the right rules). None changes what a statement says.

Exceptions to the axiom policy: none.

## 5. The reviewer's

Stated, and not asked for.

* **Only the reviewer may**: nothing arose. No author was contacted;
  nothing was published; the pushes are to `main`, as the brief said.
  One thing to know before anything about this work is shown outside:
  Pfenning's 2002 lecture notes carry "Please do not cite or distribute
  this document"; the records cite them for three results that the
  report does not state.
* **To try, at any time**: the exercises
  ([Play/DILL.lean](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/Play/DILL.lean), twelve),
  and the tutorial page (`calculi/DILL/tutorial.md`, with its exercises
  file; 27 graded exercises in four parts, 25 pinned statements of which
  5 in paraphrase for the eight refuted ones, each proof explained in a
  paragraph or two; written by an agent, of which the operator ran the
  pin check and the build and read the opening, not the whole page), the
  short tutorial in Lean (`Play/DILLTutorial.lean`) and the
  [user's guide](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/users-guide.md).
  Every exercise was run by script in the tests;
  no person has typed them.
* **To fill, if the method is to be costed**: requests, tokens and cost
  of the session ([cost-log.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/cost-log.md)).
* **Words of the reviewer during the campaign**: five (the cost log has
  each): a correction ("I declined no such thing"); two rules on
  builds, relayed, the second correcting the first; two questions about
  what the operator was waiting for. No stop was asked for by the
  operator's choice; one was taken wrongly (below).

## 6. Cost, and the method

From the brief to this page: 1 hour 46 minutes by the clock (14:47 to 16:33 GMT).
One session, twelve agents (the survey; two cold readers; five for the
proofs, in 3.3 to 12.0 minutes each; one for the tests; two for Run; one
for the tutorial). 10 345 lines of Lean, of which 3 439 are tests and
generated pins; about 8 100 lines of documents. Requests, tokens and
cost are not known to the operator.

Three stretches where the clock ran and the campaign did not, forty-three
minutes in all ([cost-log.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/cost-log.md),
"Time lost"): 15:00 to 15:12, a write recorded as declined when the
application interrupted the family of sessions, which the operator took
for the reviewer's refusal; 15:51 to 16:03, the machine's restart, of which
this campaign was probably a cause: the measuring agent's first runs had
no cap on memory, and its script's deadline ended `lake` and left the
Lean under it running (the kernel passes 8 GB on one such fact); 16:03 to
16:22, the operator holding the engine and the tutorial behind one
agent's timing runs, first under a rule since corrected and then by a
misjudgement of what the timings were for.

Findings about the library (none was changed):

* `perm_count` and the permutation lemmas free of `Classical.choice`
  are now written three times (GLS, MALL, here): they belong in the
  library. The enumerations of picks and divisions of a list, with
  their lemmas, are written twice (MALL, here).
* The explorer offers moves as one list: nothing marks where the rules
  that lose nothing end and the choices begin.

Changes proposed to the skill, from
[method-notes.md](https://github.com/fairflow/proof-tools/blob/5850b99/calculi/DILL/campaign/method-notes.md);
those that would change its text most:

* `reference/adopt.md` §6: a function on the family is to be stated over
  a variable judgment, and checked with `#print` and a `decide`: where
  the judgment is a structure, pattern matching on `Fam (Γ ⨾ Ξ ⟹ C)`
  compiles by well-founded recursion with no warning (note 6);
* stage 2: goals that do not rest on one another go to agents together,
  from one brief, with the joining file the operator's; the semantic cut
  elimination unblocks everything that needs only the proposition
  (notes 8, 9);
* `reference/adopt.md` §5: what a goal stated as a type asserts beyond
  its proposition, and a kernel test that it computes (note 10);
* stage 0, step 3: a notation is screened in a file with a tactic block;
  `;` and `!` beside `⊕` among the signs that are Lean's (note 4);
* the first act: a system that is a fragment of the paper's; a source
  that asks not to be cited (notes 1, 2);
* "The stops": a call refused at the moment of an interrupt is a stop
  from outside, not the reviewer's refusal (note 5);
* stage 3: a budget for measurements, in sizes or in minutes, set
  before the run; a lower bound on the frontier serves the page (note
  12).

**For phase 3** (focusing, or Benton's LNL): the inversions and identity
expansion proved here are the lemmas a focused calculus is built on;
the search of `DILL/Lazy.lean` already chains the left rules, unproved;
`toILL` and `ofILL` are the pattern for a translation between a
two-zone and a one-zone system, which LNL's adjunction would repeat.

## After the close

Added 2026-11-27. The page above is as it was delivered on 2026-11-26
(the published copy is that one); two of its sentences no longer hold.

* Section 1 gives two limits of the kernel: a tree of moves, "a chain of
  64 formulas in 8 s, not settled at 96", and a saturated set, "a set of 200
  sequents is checked in about 19 s and one of 499 not in 120 s". Each was a fault
  of the check's definition, found and repaired on 2026-11-27: the
  kernel now checks the tree of a chain of 64 in 0.9 s and of 256 in
  16 s, a set of 200 in 1.6 s and one of 2790 in 198 s (in 28 parts,
  each a theorem of its own); a set of 6366 it still does not, within
  4 GB. The definitions are unchanged; what is run is proved against
  them (statements S19 and S20). `measurements.md` and
  `measurements-sat.md`, "The cost of the check"; method note 23.
* `dillrun prove '<sequent>'` (2026-11-26, evening) answers for a
  sequent typed at a shell and prints a Lean file with the facts; the
  user's guide, "From the command line"; method notes 21 and 22.
