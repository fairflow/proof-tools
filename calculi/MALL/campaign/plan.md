# MALL: the plan

Written 2026-11-26 10:03 GMT. The target, the place of the files and the
rules of the project: `decisions.md`, the first entry.

## The source

* The paper: J.-Y. Girard, *Linear logic*, Theoretical Computer Science
  50 (1987) 1-102. The journal article is its only version.
* **Which file was read**: `linear.pdf`, the author's scan of the journal
  pages, as page images (it has no text layer). Read in full: the
  contents and pp. 1-7; Section 1 from p. 17 to the exponential rules on
  p. 26; pp. 40-44 (the cut rule and cut elimination for proof nets).
  Not read: the rest.
* The appendix: the paper has none.
* Other sources consulted, each for one thing (the files and where they
  came from: `decisions.md`, the second entry; the agent's report on
  them: [survey-report.md](survey-report.md)):
  - Y. Lafont, *The finite model property for various fragments of
    linear logic*, J. Symbolic Logic 62 (1997) 1202-1208, in the
    author's version (6 pages; cited by its own page numbers): Lemma 1
    (Okada), Theorem 1, Theorem 2 and the construction before it. Read
    by the operator as extracted text (pp. 1-4), and by the agent from
    the page images;
  - P. Lincoln, J. Mitchell, A. Scedrov, N. Shankar, *Decision problems
    for propositional linear logic*, Ann. Pure Appl. Logic 56 (1992)
    239-311: Theorems 2.1, 2.2, 2.12. Read by the agent only (OCR
    text); the operator has not opened it;
  - J. Hodas and D. Miller, *Logic programming in a fragment of
    intuitionistic linear logic*, Inform. and Comput. 110 (1994), and
    I. Cervesato, J. Hodas, F. Pfenning, *Efficient resource management
    for linear logic proof search* (the preprint of 1997 of the paper
    in TCS 232, 2000): for the search of stage 3. Fetched; not yet
    read.
  - M. Okada, TCS 227 (1999): not obtained (Elsevier refused the
    download). Lafont's Lemma 1 is the argument, with its attribution.

## Q1. What are the rules?

* **Formulas** (p. 21, not numbered): "(i) The atomic propositions are
  **1**, ⊥, ⊤, **0** together with propositional letters a, b, c, … and
  their duals a^⊥, b^⊥, c^⊥, … (ii) Propositions are constructed from
  atomic ones by applying the binary connectives ⊗, ⅋, ⊕, &." Linear
  negation is not a connective: it "is defined" by **1**^⊥ = ⊥,
  ⊥^⊥ = **1**, ⊤^⊥ = **0**, **0**^⊥ = ⊤, a^⊥⊥ = a, and the four De
  Morgan equations (p. 21). "This particular form of syntax without
  negation is not something deep" (p. 22).
* **Judgments** (Definition 1.15, p. 22): "the sequents will have no
  left-hand side, i.e., they will be of the form ⊢ A₁, …, Aₙ". They are
  sequences: "only the rule of exchange is left". The empty sequent is
  a sequent (p. 23: "when the list is void").
* **Notation**: a light capital is a formula; a bold capital (**A**,
  **B**, **C**, **D**) is a list of formulas, a "context" (p. 23: "the
  *contexts* (i.e., the unspecified lists of formulas **A**, **B**,
  **C**, etc.)"). In the figure a letter is light or bold by its place:
  in `⊢ A, **C**   ⊢ B, **C**  /  ⊢ A & B, **C**` the first two are
  formulas and **C** a context.
* **The figure of rules**: Definition 1.15, p. 22, eleven rules, all
  primitive: logical axioms, cut, exchange; additive: ⊤, &, 1⊕, 2⊕;
  multiplicative: **1**, ⊥, ⊗, ⅋. The source shows no rule admissible.
* **Side conditions stated in the prose** (all p. 22):
  - the axiom: "(It is enough to restrict it to the case of a
    propositional letter a.)": a remark, which is a claim (identity
    expansion), not a restriction of the rule;
  - exchange: "where **B** is obtained by permuting the formulas of
    **A**";
  - ⊤: "(axiom, **A** arbitrary) (no rule for **0**)".
* **Rules against restrictions on proof search**: every line is a rule.
  The source has no search.
* **Ambiguous or silent**, with what was decided (each of kind U):
  - U1. The letters "a, b, c, …": how many is not said. Decided: one
    for each natural number.
  - U2. The interpretation of a proposition "in a completely
    straightforward way" (Definition 1.14(ii)) is not written out.
    Decided: by the definitions on facts, S(a^⊥) = S(a)^⊥ (the proof of
    1.17 uses it, case (ii)), S(**1**) = ⊥^⊥ (1.5(ii)), S(⊥) = ⊥,
    S(⊤) = P (1.5(iii)), S(**0**) = P^⊥ (1.5(iv)), ⊗ and ⅋ by 1.8,
    & and ⊕ by 1.11.
  - U3. What a sequent means in a phase structure is said only in the
    proof of 1.16: "⊢ **A** must be read as the *par* of its components
    (and, when the list is void, as ⊥)". Decided: exactly that; a
    sequent of one formula is that formula.

## Q2. What is proved about it?

**The standing list.**

| entry | value, and why | source, and the system its theorem is about | a goal? |
|---|---|---|---|
| 1. cut elimination | holds | Girard 1987 proves it for proof nets, not for sequents (Theorem 2.12, p. 42, multiplicative nets; Section 4, PN2). For sequents: Lafont 1997, Theorem 1, (1) ⟺ (4), p. 2, for the one-sided calculus on multisets, which is this system without the exchange rule; and LMSS 1992, Theorem 2.1, p. 244 (from their Theorem A.3), for their one-sided presentation | by rule. The statement: a derivation with cut gives one without. Two routes, both taken: the induction on the cut formula and then on the two derivations, as a function on derivations (the goal of record; LMSS's appendix is of this kind); and Lafont's, through phase semantics, which gives the proposition only |
| 2. the finite model property | holds | Lafont 1997, Theorem 2, p. 3, the same calculus: "A is provable in MALL" iff "A is satisfied by all finite phase models" | by rule; by the task's words attempted last ("a stretch goal") |
| 3. deduction theorems | does not apply | Girard, Remark 1.18(i), p. 24: "We have given absolutely no meaning to the concept of 'linear logical theory'": there is no derivability from hypotheses. What stands nearest is the ⅋ rule with its inversion, since A ⊸ B is A^⊥ ⅋ B (1.9(i)) | no. The inversion of ⅋ is a goal below, for its own use |
| 4. normalisation | holds of the logic, proved elsewhere | Girard, Theorem 2.12 (multiplicative proof nets), Section 4 (PN2): for nets, which are another system. The sequent calculus defines no terms | no: proof nets are a campaign of their own |
| 5. Church-Rosser | holds of the logic, proved elsewhere | Girard, Proposition 2.11, p. 42, for multiplicative nets | no, as 4 |
| 6. the disjunction property | holds, for ⊕: if ⊢ A ⊕ B is derivable then ⊢ A or ⊢ B is. No source read that states it for this system (looked at: Girard's Sections I, II and 1; Lafont; the agent's reading of LMSS). It follows from cut elimination by the last rule of a cut-free derivation | none found | decided: yes. It costs a few lines after goal 1, and shows what the absence of contraction gives |
| 7. the existence property | does not apply | the fragment has no quantifiers | no |

**The source's theorems, and further results from the literature.**

| result | where | route | size | a goal? |
|---|---|---|---|---|
| soundness for phase semantics | Girard, Proposition 1.16, p. 23 | induction on the derivation, ten cases | a page | by rule; first |
| completeness for phase semantics | Girard, Theorem 1.17, pp. 23-24 | the phase space of multisets of formulas with the provable ones as antiphases; S(A) = Pr(A), which uses cut. Lafont's Lemma 1 proves the inclusion S(A) ⊂ {A}^⊥ only, which is enough and does not use cut | a page | by rule; second, by Lafont's route, for the cut-free calculus (it then gives cut elimination as a proposition) |
| the axiom may be restricted to letters | Girard, p. 22, a remark with no proof | induction on the formula | a few lines | decided: yes; the search uses it |
| exchange | a rule of the source | here a theorem (see the encoding) | a few lines | decided: yes, with heights |
| weakening and contraction fail | Girard, p. 22: "weakening is forbidden as well"; p. 5 | a derivable and a non-derivable sequent each | a line each, once derivability is decided | decided: yes, as REFUTED statements (the task asks) |
| "A ⊸ A ⊗ A is not derivable, but A ⊸ A & A is" | Girard, p. 5 | a derivation; a decision | a line each | tests, and known non-theorems |
| inversion of ⅋, ⊥, & | Girard uses the & case in the proof of 1.17(vii): "⊢ B & C, **D** is provable iff ⊢ B, **D** and ⊢ C, **D** are both provable" | by cut against an identity | a few lines each | decided: yes (the entry 3 above; and a search may use them) |
| decidability | LMSS, Theorem 2.2, pp. 244-245: every premise of a cut-free rule is smaller than its conclusion | a search by recursion on the size, proved complete | a file | decided: yes (the task asks: "a decision procedure proved correct") |
| PSPACE-completeness | LMSS, Theorem 2.12, p. 259 | a reduction from QBF | long, and needs a theory of machines the library has not | no |
| the subformula property | LMSS, Corollary A.4, p. 308; Lafont, p. 3 | an invariant on cut-free derivations | half a page | decided: yes, after the others (the finite model needs the closure it speaks of) |
| the semantic equations 1.9, 1.12, 1.13 | Girard, pp. 19-21 | on facts | a page | no, as statements about facts. Their syntactic forms (a linear equivalence derivable, or one half only) are the corpus of stage 3 and exercises |
| 1.4, 1.5, 1.6, 1.9.1, 1.13.1 | Girard, pp. 18-21 | on facts | lines | lemmas on the way, proved where used |

The kinds of result among the goals (`reference/adopt.md` §2):
soundness and completeness for a semantics (the model of completeness is
a definition, since the family is into `Type` only for derivations);
cut elimination (two families, a function on derivations, the measure
carried by structural recursion, no index added); a property stated of
models (the finite model, returned as a structure); a result read off
derivations (the disjunction property: a function on cut-free
derivations); decidability (a procedure by recursion on a bound of the
size).

**The semantics** (Definitions 1.1-1.3, 1.7, 1.8, 1.11, 1.14; U2, U3
above). A phase space is a commutative monoid P with a set ⊥ of
antiphases; G^⊥ = {p ; ∀q (q ∈ G → pq ∈ ⊥)}; a fact is a G with
G^⊥⊥ = G; a phase structure gives each letter a fact; S(A) is defined
by recursion on A; A is valid in S when 1 ∈ S(A); a linear tautology is
valid in every phase structure. No term calculus.

## Q3. What should run, and why?

* **Both sides**, and a decision procedure: (i) a search for cut-free
  derivations by recursion on a bound of the size, proved sound and
  complete, which gives `Decidable (Derivable Γ)`; (ii) a faster search
  that is not proved, by lazy splitting (Hodas and Miller; Cervesato,
  Hodas and Pfenning), whose answer is a tree of moves that the kernel
  checks; (iii) a check of a finite phase structure against a sequent,
  proved sound, with a small search for one.
* **Who relies on the answers**: the campaign itself (the REFUTED
  statements and the known non-theorems are decided by (i); the corpus
  by (ii)); the tutorial; and phase 2 of the round (dual intuitionistic
  linear logic), which will want to compare a search of its own.
* **The certificate of record**: the tree of moves (the default). The
  checker sees explicit splits: the ⊗ move carries the context of its
  left premise.
* **The route to countermodels**: the source gives none from a failed
  search. Lafont's Theorem 2 gives a finite phase structure for every
  sequent that is not derivable; as data it is far too large to write
  out (its phases are all sequents below a bound). So a countermodel as
  a certificate is a small structure found by enumeration, and a
  negative answer is, in general, the decision procedure's.
* **The level aimed at**: 3, by the direct decision
  (`reference/certify.md` §4): `Decidable (Derivable Γ)` is a proved,
  structural search. For models, level 2: a finite model is a number n,
  a multiplication table on `0, …, n−1`, the antiphases and one set for
  each letter, as lists; the check tests the monoid laws and the facts,
  and that 1 is not in the sequent's interpretation.
* **Does a search end by itself?** Yes, without cut: every rule read
  upwards removes a connective or a constant (LMSS, the proof of
  Theorem 2.2). The source says nothing of search. The cost is the 2ⁿ
  splittings of a context of n formulas at ⊗.

## Q4. How do people use it?

* **The source's worked derivations.** For this fragment it displays
  none: the only derivation drawn in Section 1 (p. 26) is of the
  exponentials. The choice is therefore ours, from what the source
  asserts: p. 5, "A ⊸ A ⊗ A is not derivable, but A ⊸ A & A is"; the
  identity `⊢ A^⊥, A` on a compound formula (the remark of p. 22); the
  two steps of p. 26 that are in the fragment (`⊢ A^⊥, A` to
  `⊢ A^⊥, A ⊕ B` by 1⊕); the syntactic forms of 1.9(ii) (⊗ and ⅋
  commutative, with units), 1.13(i) (⊗ distributes over ⊕) and 1.13(ii)
  (half-distributivity, and its converse as a non-theorem).
* **By hand**: the invertible rules first (⅋, &, ⊥, ⊤), then a choice:
  which ⊕ premise, how a context splits at ⊗. A reader does exchange
  without comment.
* **What the explorer should show**: a sequent as the source writes it,
  `⊢ A, B⊥, C ⊗ D`; a move names its principal formula, wherever it is
  in the sequent; the ⊗ move names what goes to the left premise; a
  failed attempt shows the leaf where no rule applies (a sequent of
  letters that is no axiom).

## Q5. Which calculi is it related to?

* **In the literature**: the proof nets of the source; two-sided
  presentations (Troelstra); the multiset form (Lafont), which is the
  form adopted here; dual intuitionistic linear logic (Barber 1996),
  phase 2 of this round, which adds `!` and a second zone; focusing
  (Andreoli 1992).
* **In this project**: none that is linear. `calculi/GLS/` and
  `calculi/BrunnlerK/` are modal, and both have weakening built into
  the rule format. From GLS this campaign takes one technique: a
  permutation proved by counting (`perm_count`), written again here
  since a package under `calculi/` requires only the library.
* **Existing formalisations** (the agent's survey, bounded to about
  twenty minutes; files and lines in `survey-report.md`):
  - **Yalla** (O. Laurent, Rocq; commit `a138437`): full linear logic,
    formulas with `var`/`covar` and a defined dual, sequents as lists
    with an explicit exchange rule, derivations in `Type`, the ⊗ rule
    `tens A B :: l2 ++ l1`, atomic axioms, cut admissibility by a
    nested induction (the size of the cut formula, then the sum of the
    sizes of the two proofs), focusing. Nothing specific to MALL; no
    phase semantics, finite model property or decision procedure;
  - **cslib** (Lean 4 with Mathlib; commit `907f934`):
    `Cslib/Logics/LinearLogic/CLL/` has classical linear logic over
    `Multiset`, no exchange rule, a general axiom, cut as a
    constructor, derivations in `Type`. Proved: inversions by cut,
    equivalences, eta expansion. Cut elimination is not proved (TODO
    signatures); phase semantics has the algebra of facts, with
    soundness and completeness TODO. So the task's belief is right as
    to the definitions, and there is nothing to import: it needs
    Mathlib, and this folder is core Lean;
  - **Abella** (Chaudhuri, Lima, Reis): cut admissibility for one-sided
    MALL with units;
  - **FormalizedFormalLogic/LinearLogic** (Lean 4, Mathlib): phase
    soundness for unit-free propositional linear logic;
  - **Coq**: `coq-ll` (Xavier, Olarte, Reis, Nigam), Larchey-Wendling's
    `Coq-Phase-Semantics` (Okada's lemma for intuitionistic linear
    logic), `ppedrot/ll-coq`.
  - **Not found**: a mechanisation of the finite model property of
    MALL, of a decision procedure for MALL, or of phase completeness
    and cut elimination for classical MALL by Okada's lemma.

## Choices of encoding

**What `deriving` gives**, tried in scratch on Lean v4.31.0 (three files,
not kept):

| type | `DecidableEq` | `Repr` | `Lean.ToExpr` | note |
|---|---|---|---|---|
| formulas (ten constructors) | yes | yes | yes | |
| judgments: `List Form` | from the library | yes | yes | |
| moves (two carry a `List Form`) | yes | yes | yes | |
| a finite model: a structure of a number and lists of lists | yes | yes | yes | |

Other things the scratch files showed:

* the source's notation: `⊗`, `⅋`, `&`, `⊕`, `⊤`, `⊥` work as scoped
  notations at precedences above that of `::` (so that `A ⅋ B :: Γ`
  reads as meant); `⊕` cannot be used in a pattern (core Lean's `⊕` for
  sum types makes it ambiguous there), so patterns name constructors;
  `𝟏` and `𝟎` stand for the source's bold **1** and **0**; `Aᗮ` for
  A^⊥ (a postfix `⊥` would collide with the constant);
* **core Lean's lemmas on permutations and `erase` use
  `Classical.choice`** (`List.isPerm_iff`, and so the instance that
  decides `List.Perm`; `List.perm_cons_erase`; `List.Perm.erase`;
  `List.cons_perm_iff_perm_erase`), while `List.Perm.count_eq`,
  `List.count_cons`, `List.count_append` and the constructors of
  `List.Perm` do not. So the campaign has a file of its own for
  permutations, by counting, and its own instance deciding `Perm`;
* a family whose every conclusion is a variable gives Lean nothing to
  infer the rule's data from: the constructors take the principal
  formulas and the contexts as explicit arguments;
* `#slime` reports no computed index on the family below; `#rules`
  prints its side conditions as `Ξ.Perm (A ⅋ B :: Γ)`.

| choice | the options weighed | chosen, why, and what it does to the rules |
|---|---|---|
| a judgment as data | (a) a list, with Girard's exchange rule as a constructor and each rule acting at the head, the ⊗ rule with an equation `Ξ = Γ ++ Δ`; (b) a list read as a multiset: every rule concludes a variable `Ξ` under a hypothesis `Ξ.Perm (…)`; (c) a list with the principal formula by membership and `erase` in the premises, as in GLS; (d) a quotient type of multisets | **(b)**. It is the source's own "variant without exchange, adapted to multisets of formulas" (p. 24), and Lafont's calculus. **Exchange needs no constructor**: `Fam Ξ` and `Ξ.Perm Ξ'` give `Fam Ξ'` by changing the hypothesis of the last rule, with the same premises, so the same height. (a) is kept as a second family, `Lit`, the figure letter for letter, proved equivalent to `Fam` both ways as functions: the rule table has the row for EXCH there. (c) hides the split of ⊗ in a second hypothesis and fixes the shape of the premises, so that exchange needs an induction; (d) has no `Lean.ToExpr`, and a rule could not match on it. **This is where weakening and contraction go**: a permutation keeps every count |
| how a rule, and a move, names what it acts on | by position; by a Boolean mask; by the formulas | by the formulas: a constructor takes `A`, `B` and the contexts; a move takes the principal formula and, for ⊗ and cut, the list that goes to the first premise. `step` then asks that the sequent be a permutation of what the rule concludes |
| the family: `Type` or `Prop` | | `Type`: the removal of cuts is a function, the search returns a derivation, the height is a function |
| what holds | the family; validity | **the family** `Fam` (the default). Validity in phase structures is a definition of stage 2, tied to it by 1.16 and 1.17 |
| two systems, and the measure | two families; one with a Boolean | **two families**: `Fam` (Definition 1.15, with cut) and `CF` (the same without cut), as GLS has `FamCut` and `Fam`. No index is added: the removal of a cut is by structural recursion, on a bound of the size of the cut formula and then on the derivations, and the height is a function on derivations |

**Screened** (stage 0, step 3). *The encoding*: the two splitting forms
(b) and the head form were written for five rules and checked on
`⊢ p ⅋ p⊥`, `⊢ p⊥, q, p ⊗ q⊥`. *What "valid" means*: the definitions of
Q2 were written as a Boolean evaluator over the cyclic groups ℤ/n,
n ≤ 4, with every set of antiphases and every pair of facts for two
letters (1 605 structures at n = 4), and run on ten sequents the source
or its semantics makes derivable and on eleven that must not be. All
ten were valid in every structure; each of the eleven was refuted in
some structure: among them `⊢ 1, 1` (weakening), `⊢ p ⊕ p⊥`
(contraction), the empty sequent, `⊢ 0`, `⊢ p⊥ ⅋ (p ⊗ p)` (p. 5), the
converse of half-distributivity, and `⊢ p ⅋ p⊥, q ⅋ q⊥` (the mix rule).
So the reading U2, U3 separates what it should on these cases, and a
cyclic group of order at most 4 already refutes each. The screen says
nothing about validity implying a classical principle; the proof of
completeness planned is constructive, which settles that when it is
done.

## Goals, non-goals, order

**Goals**, in order (a goal after those it rests on):

1. Soundness: `Fam Γ → Valid Γ` (1.16).
2. Completeness, cut-free: `Valid Γ → Nonempty (CF Γ)` (1.17 by Lafont's
   Lemma 1). With 1: cut elimination as a proposition.
3. Exchange, with heights; the family `Lit` of the figure equivalent to
   `Fam`.
4. The axiom restricted to letters (identity expansion).
5. Cut elimination as a function `Fam Γ → CF Γ`, by the induction.
6. Inversion of ⅋, ⊥, &.
7. The decision procedure: `Decidable (Derivable Γ)`, and with 1 and 2
   `Decidable (Valid Γ)`.
8. Weakening REFUTED; contraction REFUTED.
9. The disjunction property for ⊕.
10. The subformula property.
11. The finite model property (Lafont, Theorem 2). Last.

**Non-goals**: PSPACE-completeness (no theory of machines); proof nets,
their normalisation and confluence (another system); the semantic
equations of 1.9, 1.12, 1.13 as statements about facts; the
exponentials and quantifiers (an extension is a campaign of its own);
focusing (phase 3 of the round, if chosen).

## The development's axiom policy

Every theory file within `[propext, Quot.sound]`. Certifiers: the
default list of `lean-certify`, the same. No exception is planned. (The
multisets of the completeness proof are a quotient of lists, which is
what `Quot.sound` is for.)

## Dependencies

Core Lean only. `proof-tools` at the checkout's commit `906e2fa`
(= `origin/main`), required by path. Toolchain
`leanprover/lean4:v4.31.0`.

## Known non-theorems

| judgment | why it must fail | how it is expected to show here |
|---|---|---|
| `⊢ 𝟏, 𝟏` | weakening is forbidden (p. 22) | the move `one` refused: the sequent is not `⊢ 𝟏`; no other move applies |
| `⊢ p ⊕ p⊥` | contraction is forbidden | both ⊕ moves lead to a sequent of one letter, where no move applies |
| `⊢ p⊥ ⅋ (p ⊗ p)` | p. 5: "A ⊸ A ⊗ A is not derivable" | after ⅋ and ⊗, one premise is `⊢ p`: no move applies |
| the empty sequent; `⊢ 𝟎`; `⊢ ⊥`; `⊢ p` | no rule concludes them | a query where no move applies |
| `⊢ p ⅋ p⊥, q ⅋ q⊥` | the mix rule is not derivable | after the two ⅋, no split closes |
| `⊢ ((p ⊗ q) & (p ⊗ 𝟏))ᗮ, p ⊗ (q & 𝟏)` | only half of distributivity holds (1.13(ii)) | the search answers no |

Without cut every attempt ends: no search fails to end.

## Results that exist in Lean already, used and not re-proved

None of the calculus. From core Lean: `List.Perm` and its constructors,
`List.count`, and the lemmas named above that are within the policy.

## Budget

| stage | time expected | what closes the stage short of its goals |
|---|---|---|
| 0 Survey | 30 min | (done at 10:03) |
| 1 Adopt | 1 h | S2 left OPEN after two routes |
| 2 Prove | 4 h | a goal left OPEN after three routes tried; goal 11 not begun if the others are not done by the fourth hour |
| 3 Run | 1 h 30 | the lazy search left as a plain search if its tree is rejected after two repairs |
| 4 Explore | 1 h | none |

## The decisions that cost the campaign to reverse

The source and the system (the first entry of `decisions.md`); what
holds (the family `Fam`); what "valid" means (U2, U3, at universe
`Type`); the axiom policy. A stage: the multiset reading (b), two
families, which results are goals.
