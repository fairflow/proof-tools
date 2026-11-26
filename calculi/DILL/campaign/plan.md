# DILL: the plan

Written 2026-11-26 15:02 GMT, before any Lean of the calculus beyond the
scratch screens it reports. The target, the place of the files and the
rules of the project: [decisions.md](decisions.md), the first entry.
Read again at the start of every stage; changed, with the date, when a
decision changes.

## The source

* **The paper**: B.-Y. E. Chang, K. Chaudhuri, F. Pfenning, *A judgmental
  analysis of linear logic*, CMU-CS-03-131R, 14 April 2003, revised
  29 December 2003. Cited below as CCP, by its printed page.
* **Which file was read**: `ccp03.pdf` (34 pages). Read in full by the
  operator: Section 3 (pp. 10-18), as text and, for Figure 2 and p. 11,
  from the page as an image. Read in part: Section 2 (pp. 2-9), for what
  a judgment is. Not read: Section 4 and the appendix (classical linear
  logic interpreted; several conclusions), which are outside the
  fragment.
* **The appendix**: an alternative JILL with several conclusions; not in
  the fragment.
* **Other sources consulted**:
  - F. Pfenning, *Linear Logic*, lecture notes, draft of 26 January 2002,
    chapter 3 (pp. 45-60): the prose on labels and multiplicity of
    hypotheses (p. 46), cut elimination (3.9), consistency (3.11), the
    disjunction property (3.12), non-theorems (p. 60). Marked "Please do
    not cite or distribute": read, not the source of record. Cited as
    Pfenning.
  - A. Barber, ECS-LFCS-96-347 (1996): the system's origin; §5 for the
    translation to one-zone intuitionistic linear logic. Cited as Barber.
  - M. Kanovich, M. Okada, K. Terui, *Intuitionistic phase semantics is
    almost classical*, author's final version for MSCS (2006), §2
    (pp. 3-6): the one-zone calculus ILL (Figure 1, p. 4) and the phase
    semantics (Definitions 2.2, 2.4, 2.6, Theorem 2.9). Read by the
    operator from the pages as images (pp. 3, 4). Cited as KOT.
  - What the survey agent read besides (Okada and Terui, Lafont, Lincoln
    et al., formalisations) is in [survey-report.md](survey-report.md),
    each claim marked as read in a file or as from memory.

## Q1. What are the rules?

* **Formulas** (CCP p. 1, p. 3; propositional, p. 2: "we focus on
  propositional logic"): atomic propositions (the source's parameters),
  and ⊗, 1, ⊸, &, ⊤, ⊕, 0, !. All primitive; no normal form. `?`, ⊥, ¬ and
  the modal disjunction are left out with the possibility judgment; ⊃ is
  `!A ⊸ B` (p. 9) and is not a constructor.
* **Judgments** (CCP pp. 10-11): `A₁ valid, …, Aⱼ valid ; B₁ res, …, Bₖ
  res ⟹ C goal`, written `Γ ; Δ ⟹ C ; ·`. Two-sided, one conclusion,
  flat. The linear hypotheses "allow free exchange … while disallowing
  weakening and contraction" (p. 2): a multiset. The valid hypotheses
  admit weakening and contraction (Theorem 2, p. 11) and are labelled
  (Pfenning p. 46: "the order of the hypothesis (linear or unrestricted)
  is irrelevant", and two copies of `A` give two derivations): a
  multiset in the source, of which only the set of its members matters
  for derivability.
* **Notation**: `Γ` ranges over the valid (unrestricted) hypotheses, `Δ`,
  `Δ′` over the linear ones, `A`, `B`, `C` over formulas; `γ` over the
  right-hand side, here always `C ; ·`; `·` is the empty zone; `Δ, Δ′`
  is multiset union, so a rule with `Δ, Δ′` in its conclusion applies
  for every division of the linear zone.
* **The figure**: Figure 2, p. 12. In the fragment: 18 rules, all
  primitive: init, copy; ⊗L, ⊗R, 1L, 1R, ⊸L, ⊸R; &L₁, &L₂, &R, ⊤R, 0L,
  ⊕L, ⊕R₁, ⊕R₂; !L, !R. There is no left rule for ⊤ and no right rule
  for 0. Admissible, not primitive: weakening and contraction of `Γ`
  (Theorem 2), and the cuts (Principle 7, Theorem 3). The two cuts of
  the fragment (7.1 on a valid hypothesis, 7.2 on a linear one) are the
  two further rules of the system with cut (Pfenning p. 56 names them
  cut! and cut).
* **Side conditions stated in the prose or by the form of a rule**:
  init has exactly `A` in the linear zone, and any `Γ`; 1R and !R have an
  empty linear zone; !R's premise has an empty linear zone; copy keeps
  `A` in `Γ` (p. 11: "copying valid hypotheses in Γ into the linear
  context"); !L moves `A` to `Γ` and removes `!A`; the first premise of
  cut 7.1 has an empty linear zone.
* **Rules against restrictions on proof search**: all 18 lines are
  rules. The source states no restriction on search; Lemma 6 (p. 17)
  classifies rules as invertible, weakly invertible or not, which is a
  theorem.
* **Ambiguous or silent**, each a divergence of kind U or W:
  - **W1**: the figure prints the conclusions of ⊕R₁ and ⊕R₂ as
    `Γ ; Δ ⟹ A & B ; ·`. A misprint: the rules are ⊕'s (their names;
    Pfenning p. 47 prints `A ⊕ B`; with `A & B` the rule ⊕L would have
    no right rule and `A ⟹ A & B` would be derivable). Transcribed with
    `A ⊕ B`.
  - **U1**: whether `Γ` is a list, a multiset or a set. Decided: a list
    read through membership (below), since Theorem 2 makes the three
    agree on what is derivable.
  - **U2**: whether init is for every formula or for atoms. The figure
    says every `A` ("init rule has the following most general form",
    p. 11). Transcribed so; the restriction to atoms is a goal.
  - **U3**: the atoms. The source has propositional parameters with no
    stated supply. Decided: one for each natural number.

## Q2. What is proved about it?

**Why the paper's theorems hold of the fragment.** They are stated for
JILL whole. A derivation without cut of a sequent `Γ ; Δ ⟹ C ; ·` in
which `?` does not occur uses only rules of the fragment: read upwards,
no rule but `promote`, `?L`, `?R` has a premise or a conclusion of the
form `· ; C`, and none introduces `?`. So Theorem 3, rows 1 and 2, and
Lemma 6 for the fragment's rules are theorems of the fragment; their
proofs appeal to row 3 only in cases that have `?`.

**The standing list.**

| entry | value, and why | source, and the system its theorem is about | a goal? |
|---|---|---|---|
| 1 cut elimination | holds | CCP Theorem 3 (p. 12): the cuts 7.1 and 7.2 are admissible in the system without cut, for JILL; Pfenning 3.8 and 3.9 (pp. 57-59), for this fragment with quantifiers: every derivation with cut and cut! has one without | by rule: both forms, as functions on derivations |
| 2 the finite model property | fails of this system, for the phase semantics below: derivability with `!` is undecidable (Lincoln, Mitchell, Scedrov, Shankar 1992; the survey has the statement for the intuitionistic fragment), and a recursively axiomatised logic with the finite model property is decidable. Holds of the fragment without `!` (Okada and Terui 1999; the survey has the place) | proved elsewhere, for one-zone calculi | no: it fails. The fragment's form is not a goal (the budget); decidability of the fragment is, below |
| 3 deduction theorems | holds, in the form the calculus has it: its judgment is hypothetical, and each kind of hypothesis is discharged by a connective: `Γ ; Δ, A ⟹ B` iff `Γ ; Δ ⟹ A ⊸ B`, and `Γ, A ; Δ ⟹ C` iff `Γ ; Δ, !A ⟹ C` | CCP Lemma 6 (p. 17): ⊸R and !L are invertible | by rule: the two equivalences |
| 4 normalisation | does not apply: the sequent calculus has no terms. (Of natural deduction: Pfenning 3.10, by way of cut elimination; Barber §7.2 leaves rewriting as further work.) | | no |
| 5 Church-Rosser | does not apply, as 4 | | no |
| 6 the disjunction property | holds: if `· ; · ⟹ A ⊕ B` then `· ; · ⟹ A` or `· ; · ⟹ B` | Pfenning 3.12 (p. 60), stated for natural deduction and proved through the cut-free sequent calculus. CCP does not state it | by rule |
| 7 the existence property | does not apply: propositional | | no |

**The source's theorems, and further results.**

| result | where | by which route | size | a goal? |
|---|---|---|---|---|
| weakening and contraction of `Γ` | CCP Theorem 2 (p. 11) | structural induction, "omitted" | small | **goal** (the source's theorem). Proved as one statement: a derivation of `Γ ; Δ ⟹ C` gives one of `Γ′ ; Δ ⟹ C` whenever every member of `Γ` is a member of `Γ′` |
| weakening and contraction of `Δ` | CCP p. 2: disallowed | | | **goals, expected REFUTED**, each by a pair of sequents |
| exchange in both zones | CCP p. 2; Pfenning p. 46 | by the encoding | trivial | **goal**, with the height kept; said to be trivial where it is |
| cut 7.1, 7.2 admissible; cut elimination | CCP Theorem 3; Pfenning 3.8, 3.9 | nested structural induction: the cut formula, then row 2 before row 1, then the two derivations | the largest proof: 18 × 18 cases for 7.2 | **goal by rule** |
| soundness and completeness against natural deduction | CCP Theorems 4, 5 (pp. 14-17) | induction; completeness uses cut | natural deduction is a second system of about 18 rules | **not goals**: they are about Figure 1, which is left out (the first entry of the decisions). The fourth check of meaning is run against a semantics instead |
| the invertible rules | CCP Lemma 6 (p. 17): ⊗L, 1L, ⊸R, &R, ⊤R, ⊕L, 0L, !L invertible; 1R, !R weakly invertible; ⊗R, ⊸L, &L₁, &L₂, ⊕R₁, ⊕R₂ not | by cut; the failures by a sequent with the same connective on both sides | small, after cut | **goals**: the inversions of ⊗L, 1L, ⊸R, &R, ⊕L, !L and of !R at an empty linear zone (⊤R and 0L have no premise). The non-invertible rules: **goals, expected REFUTED**, one sequent each, decided by the kernel |
| consistency | Pfenning 3.11 (p. 59) | no rule concludes `· ; · ⟹ 0` | one line | **goal** |
| the subformula property | CCP p. 10 ("they must obey the subformula property"); Pfenning p. 56 | read off the rules | small | **goal** |
| identity expansion: init for atoms only derives the same sequents | no place found in CCP (its init is general); Pfenning p. 13 on local expansion is for natural deduction; the survey looks further | induction on the formula | small | **goal, of our own form**, since the search and a later focused calculus want it |
| soundness for the phase semantics | KOT Theorem 2.9 (p. 6), "only if", for one-zone ILL, attributed there to Abrusci 1990 and Troelstra 1992: holds of the logic, proved elsewhere | induction on the derivation | medium | **goal**: the source has no semantics, so the fourth check of meaning wants one (`SKILL.md`, "What a campaign proves") |
| completeness, without cut | KOT Theorem 2.9 "if", and Remark 2.11 for the form without cut (pointing to Okada 1996) | the canonical model on contexts, with a closure operator given by a family of sets (KOT Theorem 2.8, Lemma 2.10) | medium to large | **goal**, of the same kind. With soundness it gives cut elimination a second time, as a proposition |
| the translation: `Γ ; Δ ⟹ C` iff `!Γ, Δ ⊢ C` in one-zone ILL | Barber Theorem 3 and Lemmas 5.1.1, 5.1.2 (§5), for natural deduction with terms and I, ⊗, ⊸, !; the one-zone calculus is KOT Figure 1 | induction each way; from ILL, the inversion of !L, weakening and contraction of `Γ`, and cut | a second family of 21 rules, and two inductions | **goal**: it is the reading of a two-zone sequent, and it carries KOT's theorem to this calculus |
| decidability without `!` | Lincoln et al. 1992 (the survey has the theorem) | every rule but copy and !L has smaller premises | medium (MALL's was 409 lines) | **goal**, for sequents with empty `Γ` and no `!`: Run's "no" side and the refutations above rest on it |
| undecidability with `!` | Lincoln et al. 1992 | machines | large | **not a goal** (the brief says so; it needs a theory of machines) |
| the classical interpretation; the possibility judgment | CCP §4, §2.3 | | | **not goals**: outside the fragment |

**The kinds of result** (`reference/adopt.md` §2): cut elimination and
the admissible rules (two families or one with a parameter; functions
on derivations, so the family is into `Type`); soundness and
completeness (a structure of models; the model construction as data
where it can be); a translation (a second family; no computed index);
decidability (a search by structural recursion on a measure); results
read off derivations (after cut elimination).

**The semantics** (KOT Definitions 2.2, 2.4, 2.6, pp. 3-5). An
intuitionistic phase space is a commutative monoid `(M, ·, ε)` with a
closure operator `Cl` on its subsets: (Cl1) `X ⊆ Cl X`; (Cl2)
`Cl (Cl X) ⊆ Cl X`; (Cl3) `X ⊆ Y ⟹ Cl X ⊆ Cl Y`; (Cl4)
`Cl X · Cl Y ⊆ Cl (X · Y)`. A set is closed if `X = Cl X`. On sets:

    X ⊗ Y := Cl (X · Y)        1 := Cl {ε}
    X & Y := X ∩ Y             ⊤ := M
    X ⊕ Y := Cl (X ∪ Y)        0 := Cl ∅
    X ⊸ Y := {z | ∀ x ∈ X, x·z ∈ Y}
    !X := Cl (X ∩ I),  where I := {x ∈ 1 | x·x = x}

A model adds a valuation of the variables by closed sets; a formula `A`
is satisfied if `ε ∈ v(A)`. (KOT's valuation also gives a closed set to
the constant ⊥, which the fragment does not have.) KOT state
satisfaction for formulas only.

## Q3. What should run, and why?

* **Both**: proof search, and refutation where the search space is
  finite. Search with a budget: with `!` derivability is undecidable, so
  no procedure decides it and no sound certificate against a derivation
  is complete.
* **Who relies on the answers**: the reviewer and readers of the round
  on linear logic, who want a sequent of a linear type system or of a
  session type settled and its derivation to look at; and the Prove
  stage, whose refuted statements are decided by the kernel. So each
  answer is certified.
* **The certificate of record** for a derivation: the tree of moves
  (the default); the moves of ⊗R, ⊸L and cut name the division of the
  linear zone.
* **The route to countermodels**: the source gives none. Two are taken.
  (a) The record of a failed search, a finite saturated set of sequents
  (`reference/certify.md` §3, MALL's second form), whose soundness is
  here proved from cut elimination alone, with no model: no member of a
  saturated set has a derivation without cut. (b) For sequents with
  empty `Γ` and no `!`, the proved decision procedure, run by the kernel.
* **The level aimed at**: 2. Derivability is not decidable, so level 3
  is not a goal. The producer answers `flag` at its budget. Completeness
  of refutation is stated for the fragment with empty `Γ` and no `!`
  only (the decision procedure). A finite model as data is not built: a
  saturated set is the certificate, and nothing here turns it into a
  phase model (MALL did; here it is beyond the plan's level).
* **Does a search end by itself?** No: copy has a premise that contains
  its conclusion's material (pitfall 3), and !L feeds it. The source
  says nothing of what ends a search. Here: the search counts the uses
  of copy against a budget and answers `flag` when it is spent; the
  explorer's `within` sets nothing aside (no premise is within its
  conclusion: copy's premise is strictly larger), so a sequent with no
  derivation shows as a query where no move applies, or, with copy
  available, as an attempt that stays open.

## Q4. How do people use it?

* **The source's worked derivations**: CCP p. 16, `Γ, A ; · ⟹ A` (init,
  copy) and `Γ ; A, A ⊸ B ⟹ B` (init twice, ⊸L); p. 17,
  `Γ ; A & B ⟹ A`; p. 18, the inversion of ⊸R by cut. Pfenning p. 60:
  the non-theorem `· ; A ⊸ (B ⊗ C) ⟹ (A ⊸ B) ⊗ (A ⊸ C)`. CCP p. 17: the
  non-theorem `· ; · ⟹ A ⊗ ¬A ⊸ C` is outside the fragment; p. 18: the
  premisses of ⊸L at `· ; A ⊸ B ⟹ A ⊸ B`, "not derivable in general".
  Barber Lemma 2.3 (the equivalence of `!` with the zone), and the
  usual laws of `!`: `!A ⟹ A`, `!A ⟹ !!A`, `!A ⟹ !A ⊗ !A`, `!A ⟹ 1`,
  `!(A & B)` and `!A ⊗ !B` each from the other: derivations of what the
  sources assert, chosen by the operator where the source draws none.
* **The order by hand**: the invertible rules first (Lemma 6: ⊸R, &R,
  ⊗L, 1L, ⊕L, !L), then a choice; copy when a valid hypothesis is
  needed; the division of the linear zone at ⊗R and ⊸L is the step that
  takes thought.
* **What the explorer should show**: a sequent as `Γ ; Δ ⟹ C` with the
  source's signs; the invertible steps done at once by a tactic of the
  calculus; at a failed attempt, the open sequents.

## Q5. Which calculi is it related to?

* **Translations**: to and from one-zone ILL (Barber §5; a goal); from
  classical linear logic by double negation (CCP §4; not in the
  fragment); natural deduction (CCP Figure 1; not a goal).
* **In this project**: `calculi/MALL/` (one-sided, classical, no
  exponentials): the form of the linear zone, `Perm.lean`, the lazy
  search, the saturated set.
* **Existing formalisations**: the survey agent's search, bounded and
  recorded in [survey-report.md](survey-report.md), Q-D. None is used.

## Choices of encoding

**What `deriving` gives**, tried in scratch (a file outside the
campaign's folder, not kept; Lean v4.31.0, 2026-11-26):

| type | `DecidableEq` | `Repr` | `Lean.ToExpr` | note |
|---|---|---|---|---|
| formulas `Form` (nine constructors) | yes | yes | yes | |
| judgments `Seq` (a structure: two lists and a formula) | yes | yes | yes | |
| moves `Move` (with lists of formulas as arguments) | yes | yes | yes | |
| a saturated set (Q3): `List Seq` | by the above | | | |
| a phase model: a structure with the carrier a `Type` and sets as predicates | not asked | not asked | not asked | it is not a certificate here; nothing computes with it |

Also tried there, and what Lean answered: the notation
`Γ ; Δ ⟹ C` for a sequent is accepted and printed by `#rules`; a family
with a Boolean parameter for cut, seven of its constructors, `#slime`
clean, exchange and the monotonicity of `Γ` written by pattern matching
within `[propext, Quot.sound]`; and **`!` is core Lean's Boolean
negation**, read with all that follows it: `!A ⊗ B` and `!A :: Δ` are
refused ("expected Bool"), `(!A) ⊗ B` and `(!A) :: Δ` are accepted. The
source's sign is kept, with parentheses, as for ⊕ (`reference/adopt.md`
§3).

| choice | the options weighed | chosen, why, and what it does to the rules |
|---|---|---|
| a judgment as data | three indices; a structure | a structure `Seq` with fields `unr`, `lin`, `goal`, and the notation `Γ ; Δ ⟹ C`: the explorer wants one type of judgments, and `#rules` then reads as the figure |
| the linear zone | membership (wrong: it gives weakening); a list with an exchange rule; MALL's form | **MALL's form**: every rule that takes something from the linear zone concludes a variable `Ξ` under `Ξ ~ …` (`List.Perm`), the figure's zone on the right of it. Exchange in `Δ` needs no rule: it is a function. The rules that only add to the zone in a premise (⊸R, copy) or leave it (the right rules of the additives) need no hypothesis |
| the unrestricted zone | a multiset with rules of weakening and contraction; a finite set; a list with membership | **a list with membership**: copy asks `A ∈ Γ`, !L puts `A` at the head. Weakening, contraction and exchange of `Γ` need no rule: they are one function (monotonicity in the members). The source's "Γ, A" in the conclusion of copy is `A ∈ Γ` |
| how a rule, and a move, names what it acts on | positions; the formula | the principal formula; ⊗R, ⊸L and cut also name the part of the linear zone that goes to the first premise (as MALL's `tensor A B [Γ]`), and the rest goes to the second |
| the family: `Type` or `Prop` | | **`Type`**: cut elimination, the translations and the search are functions on derivations |
| the system with cut and the system without | two families (MALL); one with a Boolean parameter | **one family `Fam c`**, with `c : Bool` and the two cut constructors asking `c = true`; `CF := Fam false`. The structural functions are then written once for both. `#rules` shows the parameter and the side condition `c = true` |
| what holds | the family; validity | **the family with cut**, `Fam true` (the default): S1 is a definition, and the map out gives the calculus's own derivations. The source's soundness is a goal of its own |
| a measure to induct on | an index; a function | functions on derivations (`height`), and structural recursion on the cut formula's size |

## What "valid" means, and its screen

`Valid j` is: in every intuitionistic phase model (KOT Definition 2.6),
the unit `ε` is in the interpretation of the formula of the sequent,

    (!G₁ ⊗ … ⊗ !Gₙ ⊗ D₁ ⊗ … ⊗ Dₘ ⊗ 1) ⊸ C      for  G₁, …, Gₙ ; D₁, …, Dₘ ⟹ C

The carrier of a model is a `Type`, a set of phases is a predicate, and
`I` is the strict idempotents of `1`, as KOT have it. The formula of a
sequent is ours (KOT satisfy formulas only): it is the one-zone sequent
`!Γ, Δ ⊢ C` of Barber's translation read as a formula. A lemma is to say
that it is the inclusion of the product of the interpretations in that
of `C`, so that the order of the hypotheses does not matter.

Screened in scratch (not kept), with the model of KOT's Example 2.5
(`ℕ`, `+`, `0`, the identity closure) and the variable `a` as `{1}`:
`· ; a ⟹ 1` is not satisfied (linear weakening is not valid);
`· ; · ⟹ 0` is not; `· ; · ⟹ a ⊕ (a ⊸ 0)` is not (so validity does not
bring excluded middle with it by this route); and `a ; · ⟹ a` (copy) is
valid in every model, by a proof that uses (Cl1) to (Cl4) and that a
valuation is closed. All four within `[propext, Quot.sound]`. No form of
restriction to two-valued models was needed: the statements are about
sets given as predicates, and the proofs planned are constructive, as
MALL's were.

## Goals, non-goals, order

**Goals**, in order. S1 and S2 (Adopt). Then:

1. soundness for the phase semantics;
2. completeness without cut;
3. exchange in both zones, with heights; weakening and contraction of
   `Γ` (Theorem 2); linear weakening and contraction REFUTED;
4. cut 7.2 and cut 7.1 admissible in the system without cut; cut
   elimination, `Fam true j → Fam false j` (rests on 3);
5. the inversions of Lemma 6, and the two deduction theorems (rest on 4,
   or are direct by induction);
6. identity expansion; the subformula property; consistency; the
   disjunction property (rest on 4);
7. the translation to and from one-zone ILL (rests on 3, 5);
8. decidability for empty `Γ` and no `!` (rests on 4);
9. the non-invertible rules of Lemma 6, each REFUTED by a sequent
   (rests on 8).

Goals 1 and 2 are the fourth check of meaning and come first; the
others are handed to agents at the same time, since they do not rest on
1 and 2. None is a lemma only on the way to another.

**Non-goals**: Theorems 4 and 5 against natural deduction (another
system); the finite model property, which fails with `!` (its form for
the fragment without `!`: the budget); undecidability; normalisation
and confluence (no terms); the classical interpretation; a phase model
built from a saturated set.

## The development's axiom policy

Every theory file within `[propext, Quot.sound]`, from the first
definition (pitfall 4). Certifiers within the same list (the default of
`Harness.config`). The permutation lemmas of core Lean bring in
`Classical.choice`: `DILL/Perm.lean` is MALL's file, copied.

## Dependencies

Core Lean only. `proof-tools` at the checkout's commit, `d5e294c`, by
path (`../..`). Toolchain `leanprover/lean4:v4.31.0`. `calculi/MALL` is
not imported: what is taken from it is copied (a campaign changes and
requires nothing outside its folder).

## Known non-theorems

| judgment | why it must fail | how it is expected to show here |
|---|---|---|
| `· ; · ⟹ 0` | Pfenning 3.11 | a query where no move applies |
| `· ; a ⟹ 1`, `· ; a, b ⟹ a` | no linear weakening | 1R refused (the linear zone is not empty); init refused |
| `· ; a ⟹ a ⊗ a` | no linear contraction | every division of the zone leaves a premise where no move applies |
| `· ; a ⊸ (b ⊗ c) ⟹ (a ⊸ b) ⊗ (a ⊸ c)` | Pfenning p. 60 | attempts that stay open; decided by the kernel |
| `· ; a ⟹ !a` | !R needs an empty linear zone | !R refused |
| `· ; a ⊕ b ⟹ a`, `· ; a ⟹ a & b` | the additives | an open premise |
| `· ; !a ⊸ b ⟹ a ⊸ b` and the like with `!` on the left | | copy is always offered: the attempt stays open; the search answers `flag` |

## Results that exist in Lean already, used and not re-proved

None is imported. Copied from `calculi/MALL/MALL/Perm.lean` (this
project, same notions: `List.Perm` on lists of formulas, with
replacements free of `Classical.choice`): the file as it stands, with
the namespace changed.

## Budget

| stage | time expected, by the clock | what closes the stage short of its goals |
|---|---|---|
| 0 Survey | to 15:10 | |
| 1 Adopt | 30 minutes | |
| 2 Prove | 75 minutes, with agents in parallel | 17:00 by the clock, or an agent that reports a goal not reached after two routes: the goal ends OPEN with what was tried |
| 3 Run | 30 minutes | the frontier as measured |
| 4 Explore | 40 minutes | |

## The decisions that cost the campaign to reverse

The source and the system (the first entry of the decisions); what
holds: the family with cut; what "valid" means: KOT's models, with the
formula of a sequent as above; the axiom policy. Each is entered in
[decisions.md](decisions.md).
