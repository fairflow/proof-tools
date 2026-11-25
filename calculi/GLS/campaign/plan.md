# GLS: the plan

The Survey's deliverable. It can be read without opening any code. It is
read again at the start of every stage, and changed when a decision
changes, with the date.

Written 2026-11-25 09:05 GMT. The target, the place of the files and the
rules of the project: `decisions.md`, the first entry.

## The source

* The paper: R. Goré, R. Ramanayake, I. Shillito, *Cut-Elimination for
  Provability Logic by Terminating Proof-Search: Formalised and
  Deconstructed Using Coq*, TABLEAUX 2021, LNCS 12842, pp. 299-313,
  DOI 10.1007/978-3-030-86059-2_18. The version fixed at the first act
  to be read: the account in I. Shillito's thesis (ANU, 2023,
  DOI 10.25911/8F2P-AA86).
* **Which file was read.** When this plan was written, **neither the
  paper nor the thesis had been read**: the paper could not be got, and
  the thesis waits for the reviewer's word (`decisions.md`, "Stops").
  Read in full: Springer's page for the paper (abstract and reference
  list); and, of the authors' Coq formalisation
  `github.com/ianshil/CE_GLS` at commit `3dd8619`, the file
  `GL/GLS_PSGLS_calcs.v` (the language and both calculi) and
  `GL/README.md`. Read for their statements, not their proofs:
  `GL/GLS_exch.v`, `GLS_wkn.v`, `GLS_inv_ImpR_ImpL.v`, `GLS_ctr.v`,
  `PSGLS_termination_measure.v`, `PSGLS_termination.v`,
  `GLS_additive_cut.v`, `GLS_PSGLS_dec.v`, and the definition of
  derivations and their height in `general/ddT.v` and `general/dd_fc.v`.
  Everything below that cites a file and a line cites these.
  **Owed**: the comparison of Q1 with the figure and the prose of the
  thesis (or of the paper), entered here with its date when it is made.
  Until then Q1 is the Coq file's account, which is the object the
  paper's theorems are about, and not the paper's figure.
* The appendix: not known until the prose is read.
* Other sources consulted, each for one fact, none read in full: the
  results of four web searches (which papers exist; who formalised
  what), named where they are used.

### 2026-11-25 13:21 GMT: the thesis read, and what it changes

The reviewer allowed the download at 13:14 (`decisions.md`). Read then,
from the PDF of the thesis (246 pages; "Ian Shillito_Thesis_2023.pdf",
ANU Open Research), chapter 12, "Classical Provability Logic": sections
12.2 to 12.4 (pp. 168-171) in full, the figure from the page's image
(the text extraction loses `□` and `⊠`); of sections 12.5 to 12.7
(pp. 171-186) every numbered statement and the definition of PSGLS, and
of the proofs that of Theorem 12.7.2. The chapter has no appendix.
Sections 2.1, 4.2 and 5.1, which it cites for the language, the notion
of principal formula and the notion of model, were not read. The paper
itself could still not be got (the TU Wien host timed out again at
13:16).

* **Q1 is confirmed.** Figure 12.1 (p. 171) has the five rules of
  `GLS_rules`, on multisets ("we consider here sequents based on finite
  multisets, in our formalisation sequents are based on lists", p. 171),
  with GLR printed as `⊠Γ, □ψ ⇒ ψ` over `Φ, □Γ ⇒ □ψ, □Δ, Ψ` and the
  caption "Φ and Ψ do not contain any boxed formulas"; `⊠Γ` is
  `ϕ₁, □ϕ₁, …, ϕₙ, □ϕₙ` (p. 168). PSGLS (p. 178) is GLS with "(IdentBox)
  an additional identity rule (IdB)" and "(NoInit) the conclusion of the
  rule (GLR) is not permitted to be an instance of either (IdP) or (⊥L)
  or (IdB)". The comparison row by row is in the rule table. **No
  difference** from the Coq file's rules was found, and nothing built on
  them is built again.
* **The semantics stated by the operator is the thesis's.** Definition
  12.2.2 (p. 168): a GL-Kripke frame is transitive and "converse
  well-founded, i.e. there are no infinite ascending sequences";
  Definition 12.2.3: the four forcing clauses, as in the plan. The
  thesis proves soundness and (citing Segerberg) completeness for the
  Hilbert calculus GLH (Theorems 12.2.1 and 12.2.3, p. 169), and cites
  Sambin and Valentini for "GLS + (cut) … a sequent calculus for GLL"
  (Theorem 12.4.1, p. 171). It states no soundness or completeness
  theorem for GLS itself, and no finite model property.
* **Q2, a goal more.** Theorem 12.7.2 (p. 186): "The additive cut rule
  is eliminable from GLS + (cut)", by recursion on a derivation with
  cuts, using Theorem 12.7.1 at each cut. With Theorem 12.7.1 it is
  entry 1 of the standing list in the form the source states: **a goal
  by rule**, entered as S24.
* **Q2, two results get a source.** Proposition 12.6.1 (p. 181): a
  sequent has a proof in PSGLS iff it has one in GLS (goal 5).
  Corollary 12.6.1 (p. 182): provability in GLS is decidable (part of
  goal 2; the thesis's proof is by `mhd`, ours by the search).
* **Entry 3 of the standing list** stays "does not apply": the thesis
  proves a deduction theorem for its Hilbert calculus of K (Theorem
  4.1.1, as cited on p. 38), which is another system, and states none
  for GLS.
* **Q4, the source's worked derivations**: Examples 12.4.1 and 12.4.2
  (p. 171): four derivations, of which one is a proof and three have
  open leaves. They are in `GLS/Source.lean` as terms. Example 12.4.2
  is the loop that the plan's Q3 describes.

## Q1. What are the rules?

All places are in `GL/GLS_PSGLS_calcs.v` unless another file is named.

* **Formulas** (l. 41, `MPropF`): a propositional variable `# P`, with
  `P` in a set `V` whose equality is decidable (l. 23, 25); `⊥`; `A → B`;
  `Box A`. Four constructors, all primitive. Negation, conjunction,
  disjunction, `⊤` and the diamond are not in the language and are not
  defined in the file.
* **Judgments**: a pair of lists of formulas, `rel (list (MPropF V))`,
  written `(Γ, Δ)`: two-sided, flat. The file's opening comment (l. 32)
  says "two calculi based on multisets": the lists are read as
  multisets, and exchange is a theorem (`GLS_exch.v`, l. 1798, 1855),
  not a rule. The paper's abstract says the same of the calculus ("a
  multiset-based sequent calculus provides a more natural
  formulation").
* **Notation**: `Γ0 ++ A :: Γ1` is a list with `A` at some place.
  `XBoxed_list BΓ` (l. 154) puts, for each member `Box B` of `BΓ`, the
  two formulas `B, Box B`. `top_boxes l` (l. 161) is the list of the
  boxed formulas of `l`, in order. `nobox_gen_ext BΓ Γ0` (l. 121, with
  `univ_gen_ext`, `general/univ_gen_ext.v`) says that `Γ0` is `BΓ` with
  further formulas put in, none of them boxed.
* **The rules**: two systems (l. 306 and l. 314).

  GLS, five rules (`GLS_rules`), each a rule of inference:

      IdP    ─────────────────────────────          BotL   ────────────────
             Γ0, #P, Γ1 ⇒ Δ0, #P, Δ1                       Γ0, ⊥, Γ1 ⇒ Δ

             Γ0, A, Γ1 ⇒ Δ0, B, Δ1                  Γ0, Γ1 ⇒ Δ0, A, Δ1     Γ0, B, Γ1 ⇒ Δ0, Δ1
      ImpR   ──────────────────────────      ImpL   ──────────────────────────────────────────
             Γ0, Γ1 ⇒ Δ0, A → B, Δ1                 Γ0, A → B, Γ1 ⇒ Δ0, Δ1

             XBoxed_list BΓ, Box A ⇒ A
      GLR    ───────────────────────────      if every member of BΓ is boxed, and
             Γ0 ⇒ Δ0, Box A, Δ1               Γ0 is BΓ with formulas put in, none of them boxed

  So in GLR the list `BΓ` is exactly the boxed formulas of the
  antecedent `Γ0`, in order, and the rule weakens on both sides: by the
  formulas of `Γ0` that are not boxed, and by `Δ0, Δ1`. The file's
  comment (l. 294): "The next rule contains arbitrary weakening."

  PSGLS, six rules (`PSGLS_rules`), "a proof-search oriented version"
  (l. 35): IdP, BotL, ImpR, ImpL as above; a second axiom

      IdB    ───────────────────────────────────
             Γ0, Box A, Γ1 ⇒ Δ0, Box A, Δ1

  and GLR with three further side conditions: its conclusion is not an
  instance of IdP, nor of IdB, nor of BotL (l. 322-324).
* **Primitive, and admissible.** Primitive in GLS: the five rules. Shown
  admissible or derivable in GLS by the Coq files: the identity on every
  formula, and so IdB (`Id_all_form`, l. 331); exchange (`GLS_exch.v`);
  weakening (`GLS_wkn.v`); the inversions of ImpR and ImpL
  (`GLS_inv_ImpR_ImpL.v`); contraction (`GLS_ctr.v`); additive cut
  (`GLS_additive_cut.v`). GLS has no cut rule and no structural rule.
* **Side conditions stated in the prose**: not known until the prose is
  read. In the Coq file: those of GLR and of PSGLS's GLR, above.
* **Rules against restrictions on proof search.** GLS's five lines are
  rules. PSGLS is GLS restricted for search: its GLR is not applied to
  an axiom. IdB is a rule of PSGLS only.
* **Derivations and their height** (`general/dd_fc.v`, l. 131): a
  derivation is a tree of rule instances; an instance with no premise
  has height 1, and an instance with premises one more than the highest
  of them. (A leaf that is a hypothesis has height 0; the theorems
  about GLS are stated with no hypotheses, `fun _ => False`. PSGLS's
  termination is stated with every sequent allowed as a leaf,
  `fun _ => True`: its "derivations" are unfinished ones.)
* **Ambiguous or silent**, with what was decided (each a divergence of
  kind U, entered in the rule table when it is made):
  - the set `V` of variables is a parameter: here the natural numbers;
  - what else the prose leaves open: not known until it is read.

## Q2. What is proved about it?

**The standing list.**

| entry | value, and why | source, and the system its theorem is about | a goal? |
|---|---|---|---|
| 1. cut elimination | **holds**, in the form: the additive cut rule is admissible in GLS | the paper's abstract ("a direct proof of cut-admissibility"); `GLS_cut_adm`, `GLS_additive_cut.v` l. 692, about `GLS_rules` | **by rule**, in the form the source states: admissibility, from two derivations to one. Whether the source also states a procedure on derivations with cuts is looked for when the prose is read |
| 2. the finite model property | **holds of the logic, proved elsewhere**: GL is complete for finite transitive irreflexive frames | Segerberg 1971, as reported in Maggesi and Perini Brogi, arXiv:2205.03659 (seen in a search result, not read); nothing in the Coq files, which have no semantics | **decided: yes**, as a consequence of goal 2 below, because Run's countermodels and the fourth check of meaning want the construction of finite models |
| 3. deduction theorems | **does not apply**: GLS has no notion of derivability from hypotheses that the source states a theorem for (the Coq type of derivations takes a set of leaf sequents, and every theorem about GLS fixes it empty) | looked in: the Coq files' theorem lists | no |
| 4. normalisation | **does not apply**: no term calculus | the same | no |
| 5. the Church-Rosser property | **does not apply**: no term calculus | the same | no |
| 6. the disjunction property | **does not apply**: GL is a classical logic | | no |
| 7. the existence property | **does not apply**: propositional, classical | | no |

**The source's theorems, and further results from the literature.**

| result | where | by which route | its size | a goal? |
|---|---|---|---|---|
| soundness for Kripke models (transitive, conversely well-founded) | not in the Coq files. Literature: Sambin and Valentini, J. Philos. Logic 11 (1982), reference 13 of the paper (not read; a search result reports that it uses Kripke semantics to show cuts redundant) | induction on derivations | small: one case for each rule; GLR was proved in scratch in 20 lines | **decided: a goal**, the first: it is the fourth check of meaning, and the no side of Run rests on it |
| completeness for the same models, with a finite countermodel | the same | a terminating backward search that returns a derivation or a finite tree | medium: the search, its measure, the truth lemma | **decided: a goal**, the second: the fourth check of meaning; it gives entry 2, decidability, and entry 1 by a second route |
| identity on every formula (`Id_all_form`) | `GLS_PSGLS_calcs.v` l. 331 | induction on the formula | 30 lines of Coq | a goal: the search uses it |
| exchange, height-preserving | `GLS_exch.v` l. 2038, 2124 | induction on the derivation | 140 000 characters of Coq, because the rules name positions in lists | a goal, in the form the encoding gives (permutations); expected short |
| weakening, height-preserving | `GLS_wkn.v` l. 226, 374 | the same | 30 000 characters | a goal on the source's route to cut |
| inversion of ImpR and ImpL, height-preserving | `GLS_inv_ImpR_ImpL.v` l. 63 | the same | 51 000 characters | a goal on the source's route to cut |
| contraction, height-preserving | `GLS_ctr.v` l. 1051, 1064 | the same, with the inversions | 74 000 characters | a goal on the source's route to cut |
| the applicability of each rule is decidable | `GLS_PSGLS_dec.v` l. 313, 335 | by cases | 16 000 characters | not a goal of Prove: it is the function `step` of Adopt, whose S1 and S2 say it is right |
| termination of PSGLS: every sequent has an unfinished PSGLS derivation of maximal height (`PSGLS_termin`), and the maximal height `mhd` falls from the conclusion of a PSGLS rule to each premise (`RA_mhd_decreases`) | `PSGLS_termination.v` l. 1563, 1605; the measure `(number of usable boxes, number of implications)`, `PSGLS_termination_measure.v` l. 486, 542 | lexicographic induction on the measure; finitely many premises | 135 000 characters | **a goal in another form**: the relation "is a premise of, by a rule of PSGLS" is well-founded. `mhd` itself is a lemma on the source's route; if the proofs do not need it, it is decided again (stage 2, step 4) |
| additive cut is admissible (`GLS_cut_adm`) | `GLS_additive_cut.v` l. 692 | induction on the size of the cut formula, then on `mhd` of the conclusion | 57 000 characters, on all the above | **the goal by rule** (entry 1) |
| decidability of derivability | follows from completeness of the search | | with goal 2 | a goal, as data, with goal 2 |
| interpolation; arithmetical completeness (Solovay, reference 16 of the paper); the equivalence with a Hilbert system for GL | literature | | large, and about other systems | **not goals**: none is a result about this calculus that a goal rests on; a Hilbert system is a second calculus |

**Two routes to cut admissibility, costed** (`reference/adopt.md` §1).

* *(a) The source's*: weakening, the inversions and contraction, each
  height-preserving; the termination measure; then the double
  induction. In Coq 350 000 characters with exchange, 210 000 without.
* *(b) Through the semantics*: soundness; a search that returns a
  derivation or a finite countermodel; then a cut is admissible because
  both its premises are valid, so its conclusion is, so the search
  returns a derivation of it. It needs none of the structural lemmas.
  It is in the literature for a calculus of this name (Sambin and
  Valentini 1982, as reported; not read).

**Decided**: (b) first, since soundness and completeness come first by
the method anyway (stage 2, step 4) and then give the goal by rule in a
few lines. Then (a), for its own sake: the source's theorem is not only
that a derivation exists but that it is obtained from the two given
ones, and the abstract's third claim is exactly that ("faithful to the
input derivation"); route (b) ignores the input derivations. The two
proofs have the same Lean type. So the goal by rule is PROVED by the
first that is checked, and the second is recorded as a second proof,
with the function it defines.

The kinds of result among the goals (`reference/adopt.md` §2):
soundness and completeness for a semantics (the model construction
returns data); a property stated of models (the finite model property);
admissible rules, with a measure (the height, a function on derivations,
since the family is into `Type`); termination and decidability (a
well-founded relation; a procedure with a bound).

**The semantics** (not in the source's Coq files; stated here, and
screened: "Choices of encoding"). A model is a set of worlds `W`, a
relation `R` on it, and a valuation. Truth: `w ⊩ #p` iff `p` is true at
`w`; never `w ⊩ ⊥`; `w ⊩ A → B` iff `w ⊩ A` implies `w ⊩ B`; `w ⊩ □A`
iff `v ⊩ A` for every `v` with `w R v`. A GL model: `R` is transitive,
and its converse is well-founded. A sequent `Γ ⇒ Δ` is true at `w` if,
whenever every formula of `Γ` is true at `w`, some formula of `Δ` is.

## Q3. What should run, and why?

* **Both**: proof search, and countermodels. A decision procedure: the
  search of goal 2 ends on every sequent.
* **Who relies on the answers**: the request does not say. Decided: the
  campaign's own corpus and the explorer's users (a goal that the
  search refutes should be shown with its countermodel); so each answer
  is certified, a derivation by its tree of moves and a refutation by
  its tree model.
* **The certificate of record** for a derivation: the tree of moves
  (the default).
* **The route to countermodels**: the Coq files give none. The
  construction is this plan's, from the search: at a sequent with no
  implication at top level that is not an axiom, where every premise of
  GLR is refuted, the refuting trees become the children of a new root
  that makes true exactly the variables of the antecedent.
* **The level aimed at**: 3. A finite model, as data: a finite tree, at
  each node the list of the variables true there; `t R u` iff `u` is a
  proper descendant of `t`.
* **Does a search in this calculus end by itself?** Not in GLS as it
  stands: a premise of GLR contains the box it was applied to, and GLR
  applies again where the conclusion is an instance of IdB. What the
  source says ends it: PSGLS's side conditions on GLR
  (`GLS_PSGLS_calcs.v` l. 322), with the measure of
  `PSGLS_termination_measure.v` (l. 542): the number of usable boxes
  falls at GLR, and the number of implications at ImpR and ImpL.

## Q4. How do people use it?

* The source's worked derivations: the Coq files contain one,
  `Id_all_form` (the identity, by induction). The prose may have more:
  looked for when it is read. **Chosen by the operator** until then:
  the axioms of GL as sequents (K: `⇒ □(p → q) → □p → □q`; 4:
  `⇒ □p → □□p`; Löb: `⇒ □(□p → p) → □p`), and the identity on a boxed
  formula.
* The order by hand: the two implication rules first, since they are
  invertible; an axiom as soon as one applies; GLR last, choosing a box
  of the succedent.
* What the explorer should show: a sequent as `Γ ⇒ Δ` with the source's
  connectives; at a goal, the moves that apply; for a goal no move
  closes, its countermodel (served in Explore from the search).

## Q5. Which calculi is it related to?

* Translations in the literature: GLS and other sequent systems for GL
  (a 2024 preprint, *Unifying Sequent Systems for Gödel-Löb Provability
  Logic via Syntactic Transformations*, arXiv:2410.24053, seen in a
  search result, not read). Not used.
* Calculi already in this project: Brünnler's nested sequents for K
  (`calculi/BrunnlerK/`). Another logic and another shape of judgment.
  Nothing of it is imported; its model of finite trees
  (`BrunnlerK/Semantics.lean`) is the pattern for the one here, with
  "descendant" in place of "child".
* **Existing formalisations**, by four web searches on 2026-11-25:
  - Coq: the paper's own, `ianshil/CE_GLS` (found, read as above);
  - Isabelle/HOL: Dawson and Goré, LPAR 2010, reference 4 of the paper
    (Valentini's cut elimination for GLS; not read);
  - HOL Light: Maggesi and Perini Brogi, arXiv:2205.03659 (modal
    completeness of a Hilbert system for GL, and a decision procedure by
    a labelled calculus; not read);
  - Lean: none found for GLS. One preprint may be Lean work on GL
    (arXiv:2609.13780, *Mechanizing Gödel's Incompleteness Theorems and
    Provability Logic*; its prover was not confirmed). Not found is the
    claim; the search was four queries.

## Choices of encoding

**What `deriving` gives**, tried in scratch on Lean v4.31.0
(two files outside the repository, not kept):

| type | `DecidableEq` | `Repr` | `Lean.ToExpr` | where it does not derive |
|---|---|---|---|---|
| formulas (`var`, `bot`, `imp`, `box`) | yes | yes | yes | |
| sequents (a structure of two lists) | yes | yes | yes | |
| moves (`idP p`, `botL`, `impR A B`, `impL A B`, `glr A`) | yes | yes | yes | |
| a finite model: a tree, `node (val : List Nat) (kids : List Tree)` | **no** ("None of the deriving handlers … applied") | yes | yes | nothing may test two trees for equality. The model's worlds are the trees themselves, its relation is membership in the list of proper descendants, and truth at a tree is a Boolean function by recursion; none of these compares trees |

Also tried: truth at a tree, with `□` read over the proper descendants,
is evaluated by the kernel (`decide +kernel`) on three small cases:
Löb's formula true at the root of a tree of four nodes; `⇒ □p → p`
refuted at a leaf; `⇒ □p → □□p` not refuted at that tree.

| choice | the options weighed | chosen, why, and what it does to the rules |
|---|---|---|
| a judgment as data | (i) the Coq files' form: lists with the principal formula at a named place, `Γ0 ++ A :: Γ1`; (ii) lists, each rule finding its formula by membership and **keeping** it in the premises; (iii) lists, each rule finding its formula by membership and **removing one occurrence** of it (`List.erase`) in the premises | **(iii).** (i) puts `++` in every conclusion: a computed index, and exchange then costs what it cost in Coq. (ii) changes the calculus: a principal implication kept in the premise makes the number of implications not fall, and the source's termination measure is lost. (iii) is the multiset reading: the conclusion is a pair of variables, the side condition is a membership, the premise is computed. **What it does to the rules**: none of the five is lost and none is added; exchange needs no rule, as in the source, and is a theorem about permutations; in IdP, BotL and GLR the contexts `Γ0, Γ1`, `Δ0, Δ1` become memberships |
| the boxed part in GLR | (i) the Coq form: a list `BΓ` and two side conditions; (ii) one function `xbox` on the antecedent, which gives `B, □B` for each boxed `□B` of it, in order | **(ii)**: `XBoxed_list (top_boxes Γ)` as one recursion. The two side conditions of the Coq form say that `BΓ = top_boxes Γ0` (`nobox_gen_ext_top_boxes`, l. 245, and `nobox_gen_ext_injective`, l. 127), so the rule is the same; a divergence of representation, entered in the rule table |
| how a rule, and a move, names what it acts on | by position; by the formula | by the formula: `impR A B` acts on an occurrence of `A → B` in the succedent, `glr A` on `□A` there. Which occurrence does not matter in a multiset |
| the family: into `Type` or `Prop` | | into `Type`: a search returns a derivation, cut admissibility is a function on derivations, the height is a function, and the explorer's derivations map out to it as data |
| what holds | the family; or validity | **the family** (the method's default for an adopted calculus). Validity is a goal of Prove, not what the moves are sound for |
| the two systems | two families; one family with a Boolean parameter | two families, `GLS` and `PSGLS`: PSGLS has a rule more and side conditions on another, and a parameter would put a condition on every reading of GLS's GLR |
| a measure to induct on | an index; a function | the height as a function on derivations, with an instance without premises counted 1, as in `dd_fc.v` l. 131 |
| the letters | | the source's `Γ`, `Δ`, `A`, `B`, `P` stay (`p` for a variable's number); nothing of `Π`, `Σ`, `λ` occurs. The encoding adds no letter |

**What "valid" will mean in Lean**, screened in scratch before it is
fixed (the costliest choice after the source):

    Valid (Γ ⇒ Δ)  :=  ∀ M, M.GL → M.TwoValued → ∀ w, ((∀ A ∈ Γ, w ⊩ A) → ∃ B ∈ Δ, w ⊩ B)

with `M.GL`: `R` transitive and `WellFounded (fun x y => R y x)`; and
`M.TwoValued`: every formula is true or not true at every world.

* Screened: over **every** model the statement says too much: validity
  of `⇒ p, p → ⊥` in every GL model gives `P ∨ ¬P` for every
  proposition `P` (proved in scratch, on a model of one world). So the
  class is restricted to the two-valued models, the direct form over the
  class the literature means (`reference/adopt.md` §5; the reviewer's
  preference, recorded in the project's memory on 2026-11-23). It is the
  classical statement under excluded middle.
* Screened: GLR, in the Coq file's form, preserves `Valid`, by induction
  along the converse of `R`, with no axiom beyond `propext` (proved in
  scratch). The proof uses transitivity and the well-foundedness, and
  not the two-valuedness; ImpR will use it.
* Screened: the tree model's truth, computed, on the three cases above.

## Goals, non-goals, order

**Goals**, in order:

1. **Soundness**: `GLS (Γ ⇒ Δ) → Valid (Γ ⇒ Δ)`.
2. **Completeness, as data**: for every sequent a derivation in GLS or a
   refutation, a finite tree at whose root the sequent is false; and
   from it, with goal 1: `Valid s → Nonempty (GLS s)`; derivability and
   validity are decidable; **the finite model property** (entry 2): a
   sequent that is not derivable is false at a world of a finite GL
   model. On the way, and entered as statements: the identity on every
   formula; the well-foundedness of PSGLS's premise relation
   (termination, in this plan's form).
3. **Cut admissibility** (entry 1, by rule), in the source's form with
   the cut formula at any place. First proof: from 1 and 2.
4. **The source's structural theorems**, each with heights: exchange (as
   permutation), weakening, the inversions of ImpR and ImpL,
   contraction. On the source's route to goal 3, and off the route
   taken first: proved for their own sake, for the second proof of 3 and
   because a user of the calculus wants them as functions on
   derivations.
5. **The relation of the two systems**: a sequent is derivable in PSGLS
   exactly if it is in GLS.
6. **Cut admissibility again, by the source's induction** (the size of
   the cut formula, then the termination measure), as a function that
   uses the two given derivations. The same type as goal 3: recorded as
   a second proof, not a second statement.

**Non-goals**, with the reason for each: `mhd` as the source defines it
(a number read off a derivation of maximal height): the induction of
goal 6 can be on the measure itself, so `mhd` is decided again when
goal 6 is reached; a cut-elimination procedure for a calculus with a cut
rule: a second family, and the source's Coq files state admissibility
(to be looked at again when the prose is read); interpolation,
arithmetical completeness, a Hilbert system: above.

## The development's axiom policy

Every theory file within `[propext, Quot.sound]`: no `Classical.choice`.
The models are finite trees given as data, and validity is over
two-valued models, so nothing classical is needed. Certifiers: the
default list of `lean-certify`, `[propext, Quot.sound]`.

## Dependencies

Core Lean only. `proof-tools` at commit `818483e` (the checkout, by
path `../..`); Lean v4.31.0, the library's toolchain.

## Known non-theorems

| judgment | why it must fail | how it is expected to show here |
|---|---|---|
| `⇒ □p → p` | reflexivity is not valid in GL: false at a leaf where `p` is false | after `impR`: a query where no move applies (`□p ⇒ p` has no axiom, no implication, no box on the right); the search returns a tree of one node |
| `⇒ p` | not valid | a query where no move applies |
| `⇒ □⊥ → ⊥` | GL does not prove its own consistency: `□⊥` is true at a leaf | after `impR`, no move applies; a tree of one node |
| `⇒ □(□p → p)` | with Löb's axiom it would give `□p` | `glr`, then `impR`, then a query where no move applies: `□p, □(□p → p) ⇒ p` has no axiom, no implication at top level and no box on the right |
| `⇒ (□p → □q) → □(p → q)` | false at a root with one child where `p` is true and `q` false, and a second child where `p` is false | an attempt that stays open; the search returns a tree of three or more nodes |

## Results that exist in Lean already, used and not re-proved

None. The library's own theorems about attempts, trees of moves and
scripts are used as the method says.

## Budget

| stage | time expected, by the clock | what closes the stage short of its goals |
|---|---|---|
| 0 Survey | to 09:20 | the download unanswered: Adopt begins from the Coq files, and the comparison with the prose stays owed |
| 1 Adopt | 1.5 hours | |
| 2 Prove | 5 hours | goals 1 to 3 are not closed short. Goals 4 to 6: at 5 hours, or two routes tried on one goal, the rest ends OPEN |
| 3 Run | 1.5 hours | |
| 4 Explore | 1 hour | |

## The decisions that cost the campaign to reverse

Entered in `decisions.md`: the source and the system (the first entry);
that the transcription is made from the Coq files while the prose is
not read; what holds (the family); what "valid" means (two-valued GL
models, the sequent read as "all of `Γ` implies some of `Δ`"); the axiom
policy.
