# Brünnler's system K: the plan

The Survey's deliverable. It can be reviewed without opening any code.
**No Lean of the calculus until the reviewer has read it.**

Written 2026-11-23 07:55 GMT. Revised 2026-11-23 09:11 GMT, after the
reviewer's answer at the plan's gate (`gates.md`, the second entry):
decisions 2, 3 and 6 are answered, the letters for sequents are fixed,
and the files moved to `calculi/BrunnlerK/`. **Reviewed: passed, 2026-11-23 09:36 GMT**
(`gates.md`, the third entry), as proposed: every open decision below
went as recommended, and all ten goals are goals. The target and the
rules of the project: `gates.md`, the first entry, as changed by the
second.

**This plan was written after the reading it reports.** The source was
read, and an earlier plan written and published, before the target was
fixed (`gates.md` says how). That earlier plan is replaced by this one.

## The source

* K. Brünnler, *Nested Sequents*, habilitation thesis, Universität Bern,
  [arXiv:1004.1845](https://arxiv.org/abs/1004.1845) v1, 11 April 2010.
  The version agreed: this one, Chapter 2, §2.1.
* **Which file was read:** the PDF of v1, pages 3 to 43 (all of Chapter
  2) and 69 to 72 (the bibliography), from the page images. Not read:
  Chapter 3, pages 45 to 68, except page 67.
* **The TeX source** of v1 (`arxiv.org/src/1004.1845v1`, an archive of
  69 kB: `main.tex`, `main.bbl`, `virginialake.sty`) was fetched on
  2026-11-23 with the reviewer's leave, to a temporary folder outside
  the repository, and compiled there. It serves for labels and for
  searching; `skeleton.md` now has the labels, from the compiled `.aux`.
  Many items of §2.1 carry no label in the source (Definition 2.6,
  Theorem 2.9, Corollaries 2.24 and 2.25 among them): those are cited by
  the printed number and page of v1. The numbers and pages of the
  compiled source agree with the PDF that was read.
* The appendix: there is none.
* Other sources consulted: none of this calculus. The journal version
  ([11] of the thesis: Archive for Mathematical Logic 48(6), 2009) and
  the conference version ([10]: Advances in Modal Logic 6, 2006) could
  not be got. For the standing list: the abstract of Hakli and Negri,
  "Does the deduction theorem fail for modal logic?", Synthese 187(3),
  2012.

## Q1. What are the rules?

* **Formulas** (p. 6). Propositions `p` and their negations `p̄` are
  atoms. Negation normal form:

      A ::= p | p̄ | (A ∨ A) | (A ∧ A) | ◇A | □A

  Negation is defined: "its negation `Ā` is defined as usual using the De
  Morgan laws". `A ⊃ B` is `Ā ∨ B`; `⊥` is `p ∧ p̄` and `⊤` is `p ∨ p̄`
  "for some proposition p".
* **Judgments** (pp. 6–7). One-sided nested sequents: a finite
  **multiset** of formulas and boxed sequents,

      A₁, …, Aₘ, [Δ₁], …, [Δₙ]

  defined inductively (a finite multiset of formulas; the union of two
  sequents; the singleton `[Γ]`). The corresponding formula is `⊥` if
  `m = n = 0`, otherwise `A₁ ∨ … ∨ Aₘ ∨ □(Δ₁)_F ∨ … ∨ □(Δₙ)_F`. The
  corresponding tree has a node for each sequent, carrying its multiset
  of formulas.
* **Notation** (pp. 7–9). `Γ, Δ, Λ, Π, Σ` range over sequents; the comma
  is multiset union. `Γ{ }` is a unary context, a sequent with one hole
  in the place of a formula; `Γ{Δ}` is it filled; `depth(Γ{ })` counts
  the boxes around the hole. `p` ranges over propositions and `a, b, c, d`
  over atoms. **In Lean and in this campaign's documents** (the
  reviewer, 2026-11-23): `Υ` for the source's `Π` and `Ξ` for its `Σ`,
  because Lean reserves `Π` and `Σ` (tried: neither is accepted as a
  variable; `Υ`, `Ξ`, `Θ`, `Φ` and `Λ` are); `Θ` and `Φ` where a further
  sequent is needed. The rule table's notation table will carry this. `S ⊢ Γ` says there is a proof of `Γ` in system `S`. A
  *derivation* is a finite tree of sequents built by the rules, its
  leaves its premises; a *proof* is a derivation whose premises are all
  instances of the axiom `Γ{p, p̄}`.
* **The figure of rules**: Figure 2.3, p. 10. For system K, one axiom and
  four rules, all primitive ("System K is the set of rules
  {∧, ∨, □, ◇k_c}", p. 9):

                   Γ{A}   Γ{B}         Γ{A, B}         Γ{[A]}           Γ{◇A, [Δ, A]}
      Γ{p, p̄}    ∧ ────────────    ∨ ─────────    □ ────────    ◇k_c ───────────────
                    Γ{A ∧ B}          Γ{A ∨ B}        Γ{□A}            Γ{◇A, [Δ]}

  Shown admissible (Figure 2.4, p. 10; Lemma 2.4, Theorem 2.35):

            Γ               Γ{∅}              Γ{Δ, Δ}             Γ{A}   Γ{Ā}
      nec ─────       wk ────────      ctr ──────────       cut ──────────────
           [Γ]              Γ{Δ}               Γ{Δ}                 Γ{∅}

* **Side conditions stated in the prose**: none for the rules of K. The
  only side condition of Figure 2.3 is on `◇5_c`, which is left out.
* **Rules against restrictions on proof search.** Figure 2.3 has rules
  only. The restrictions are the systems `S°` (pp. 14–15): each rule
  keeps its main formula; `□°` applies only where the node of `□A` has
  no child containing `A`; every rule carries the proviso that the set
  sequent of each premise differs from that of the conclusion. They are
  used to prove completeness and are not rules of K.

      ∧°: Γ{A∧B, A}  Γ{A∧B, B} / Γ{A∧B}     ∨°: Γ{A∨B, A, B} / Γ{A∨B}
      □°: Γ{□A, [A]} / Γ{□A}                ◇k_c° = ◇k_c

* **Ambiguous or silent**, with a proposal for each:
  1. The modal clauses of `Ā` are not written out. Proposed: the dual of
     `□A` is `◇Ā` and of `◇A` is `□Ā`, as the cut rule and Definition
     2.28 use them.
  2. The axiom is for propositions only. That `Γ{A, Ā}` is provable for
     every `A` is used (the leaves `[Ā, A]` in the proof of Theorem 2.38)
     and stated nowhere. Proposed: a result of Q2, not a rule.
  3. The axiom is not among the rules: a proof's leaves are instances of
     it. Proposed: in the family a constructor with no premise, and in
     the explorer a move with no premise. A divergence, to be logged.
  4. Sequents are multisets. Proposed under "Choices of encoding".
  5. An empty box is something: `Γ{[∅]}` is not `Γ{∅}` (`◇k_c` with
     `Δ = ∅`). Proposed: kept distinct.
  6. The depth `|D|` of a derivation is not defined. Proposed: a leaf has
     depth 0; "depth-preserving" does not depend on the choice.
  7. `prove(Γ, X)` (Figure 2.6) leaves the order of application open.
     Proposed: any order; nothing proved depends on one.
  8. `⊥` and `⊤` depend on an unnamed proposition. Proposed: not defined
     here; the empty sequent has no corresponding formula in the Lean,
     since "valid" is stated on sequents (decision 2).

## Q2. What is proved about it?

**The standing list.**

| entry | value, and why | source, and the system its theorem is about | a goal? |
|---|---|---|---|
| 1. cut elimination | holds | Theorem 2.35, p. 27, for `K + ◇X_c` with `X` 45-closed; `∅` is 45-closed | by rule |
| 2. the finite model property | holds | Corollary 2.24, p. 19, for all `X` | by rule |
| 3. deduction theorems | does not apply to this system: Chapter 2 has no derivability from hypotheses. Holds of the logic, proved elsewhere | Hakli and Negri 2012, for an axiomatic system and an ordinary sequent calculus of K; abstract only read | the reviewer's to say; proposed: no |
| 4. normalisation | does not apply: no term calculus is defined | p. 19 only says a cut-elimination procedure "can serve as a starting point for a computational interpretation" | no |
| 5. the Church-Rosser property | does not apply, as 4 | | no |
| 6. the disjunction property | does not apply: the logic is classical | | no |
| 7. the existence property | does not apply: classical, and propositional | | no |

**The source's theorems, and further results.** Sizes are the length of
the published proof, read at `X = ∅`.

| result | where | by which route | its size | proposed |
|---|---|---|---|---|
| Soundness: `K ⊢ Γ` implies `Γ` valid | Theorem 2.9 (i), (iii), with Lemma 2.8, p. 13 | rule by rule; the context by induction on its depth | half a page | a goal (by rule) |
| Completeness: `Γ` valid implies `K ⊢ Γ`; and if `prove` fails there is a finite frame where `Γ` is not valid | Theorem 2.23, pp. 17–19 | a countermodel read off the finished sequent; three claims | one page at `X = ∅` | a goal (by rule) |
| `ctr` and `wk` admissible, depth-preserving | Lemma 2.4 (i), pp. 10–11 | induction on the depth of the proof; `ctr` by cases on where `◇A` and `[Δ]` lie | one page | a goal: 2.14 rests on it |
| the rules `∧`, `∨`, `□` invertible, depth-preserving | Lemma 2.4 (ii) | induction; the inverse of `◇k_c` is a weakening | a few lines | a goal: `ctr` rests on it |
| `nec` admissible | Lemma 2.4 (i) | "a routine induction" | one line | a goal: small, and the cut procedure uses it |
| `K° ⊢ Γ` implies `K ⊢ Γ` | Lemma 2.14, p. 15 | induction, with `ctr` and `wk` | two lines | a goal: completeness rests on it |
| `prove(Γ, ∅)` terminates | Lemma 2.22, p. 17 | the set of formulas at a node grows; cyclic leaves | ten lines | a goal: completeness rests on it |
| validity is decidable | Corollary 2.25, p. 19 | from 2.22 and 2.23 | one line | a goal: it falls out |
| cut elimination by the procedure | §2.1.4: Lemma 2.30, Lemma 2.34 (i), Theorem 2.35, pp. 19–27 | induction on cut rank, then on depth; the reduction lemma by induction on `|P₁| + |P₂|` | about two pages at `X = ∅` | the reviewer's to say (decision 1) |
| `K ⊢ Γ{A, Ā}` for every `A` | not stated; used on p. 29 | induction on `A` | not published | proposed as a goal: small, and the explorer wants it |
| provability is invariant under permutation inside a node | not stated: sequents are multisets | induction on the proof | not published | proposed as a goal: it is what entitles a list to stand for a multiset |
| `◇k` admissible; `◇k_c` derivable from `{◇k, ctr}` | Proposition 2.5 at `ρ = k`, pp. 11–12 | from weakening | two lines | proposed to set aside: only §2.2 uses it |

**Cut elimination is proved twice in the source.** Page 19: "cut
admissibility is an easy corollary of the completeness theorem". Then
§2.1.4 gives a procedure. The statement is the same,

    K + cut ⊢ Γ   implies   K ⊢ Γ

and it is a goal by rule. By the short route it costs the soundness of
cut over finite models, and completeness. By the procedure it costs the
two pages above, and Lemma 2.30 (Lemma 2.4 again with a cut rank).

**The kinds of result among the goals**, and what each means for the
encoding:

* Soundness and completeness for a semantics: a structure of models and a
  forcing relation; the completeness construction returns data.
* Admissible structural rules and cut elimination: functions on
  derivations, so the family is into `Type`; the depth of a derivation
  and the rank of a cut are functions on derivations, not indices.
* The finite model property: the model returned as data.
* Termination and decidability: a measure on sequents for the proof; the
  search that runs is written separately, in Run.

**The semantics** (Definition 2.6, p. 12). A frame is a nonempty set `S`
of states with a relation `→`; a model adds `V`, a subset of `S` for each
proposition.

    s ⊨ p    iff  s ∈ V(p)              s ⊨ p̄    iff  s ∉ V(p)
    s ⊨ A∨B  iff  s ⊨ A or s ⊨ B        s ⊨ A∧B  iff  s ⊨ A and s ⊨ B
    s ⊨ ◇A   iff  some t, s → t, t ⊨ A  s ⊨ □A   iff  all t, s → t implies t ⊨ A

A formula is valid if it holds at every state of every model; a sequent
is valid if its corresponding formula is.

**What "valid" will mean in Lean** (decision 2; revised after the
reviewer's answer). PROVED in scratch (Lean v4.31.0, within
`[propext, Quot.sound]`): with `→` into `Prop` and `V` into `Bool`,

    (∀ M s,  M, s ⊨ ◇p ∨ □p̄)   →   ∀ P : Prop, P ∨ ¬P

and `◇p, [p̄]` is provable in K. With `→` and `V` both into `Bool`, the
same assumption gives the limited principle of omniscience (take the
states to be `ℕ`). So Theorem 2.9, read with "every model" meaning every
structure the host logic can define, cannot be proved within
`[propext, Quot.sound]`.

The reviewer asked for a direct statement that is less absolute, in
place of the indirect "no model refutes the sequent" of the first
version. There is one: restrict the models, not the form of the
statement.

    M is two-valued   iff   for every formula A and state s of M:
                            M, s ⊨ A   or   not  M, s ⊨ A

    Valid Γ           iff   M, s ⊨ Γ_F  for every two-valued M and every
                            state s of M

`V` is into `Prop`, and `s ⊨ p̄` is `¬ V p s`, as in Definition 2.6. A
two-valued model is a model in the source's sense: the source's
metatheory is classical, so every model it speaks of is two-valued, and
`Valid` says what Theorem 2.9 says with that assumption written as a
hypothesis on the model. Under excluded middle every model is two-valued
and `Valid` is the source's validity.

PROVED in scratch (Lean v4.31.0; the first four with no axioms, the fifth
within `[propext, Quot.sound]`), for every two-valued `M` and state `s`:

    M, s ⊨ ◇p ∨ □p̄                                      the sequent above
    M, s ⊨ ◇A ∨ □(D ∨ A)   →   M, s ⊨ ◇A ∨ □D          the step of ◇k_c, at the root
    M, s ⊨ Ā   ↔   not  M, s ⊨ A                         the dual is the negation
    M, s ⊨ C ∨ A  →  M, s ⊨ C ∨ Ā  →  M, s ⊨ C         the step of cut, at the root
    a finite model given as data (n states, a Boolean relation,
    a Boolean valuation) is two-valued

So the two rules that need a case split on truth (`◇k_c` and `cut`) are
sound over two-valued models with no classical axiom, and the finite
models that the search returns are two-valued. Still OPEN: soundness for
the rules in a context of any depth (goal 1), which needs Lemma 2.8.

What the statements become:

    goal 1   K ⊢ Γ  →  Valid Γ
    goal 8   for every Γ:  K ⊢ Γ,  or a finite model M given as data and
             a state s with  not  M, s ⊨ Γ_F
    goal 9   Valid Γ  →  K ⊢ Γ        (from 8: the model of 8 is two-valued)

The relation "refutes" of the first version is in no statement now. It
may return inside the proof of goal 8, as the invariant of the search.
The source's form is kept in `statements.md` for comparison, with what
is known of it:

    ValidF Γ     iff   M, s ⊨ Γ_F for all M, s           (the source's words, read
                                                          in the host logic)
    ValidF Γ  →  Valid Γ                                 (immediate)
    (∀ P : Prop, P ∨ ¬P)  →  (Valid Γ → ValidF Γ)        (immediate)
    (∀ Γ, K ⊢ Γ → ValidF Γ)  →  ∀ P : Prop, P ∨ ¬P       (the screen above, with the
                                                          proof of ◇p, [p̄] in K,
                                                          which is by hand)

## Q3. What should run, and why?

* **Both**, as a decision procedure: a search that returns a derivation
  or a finite model. The source gives it (`prove`, Figure 2.6).
* **Who will rely on the answers.** Proposed, for the reviewer to
  correct: this is the library's first calculus adopted from a paper, and
  its first with judgments that are not flat; the certified answers are
  the test that the method reaches level 3 on such a calculus. No user
  outside the project is known.
* **The certificate of record**: the tree of moves, the default.
* **The route to countermodels**: a failed search read as a model. A
  finished sequent that is not axiomatic gives the model whose states are
  its nodes, with `→` from parent to child and `V(p)` the nodes
  containing `p̄` (Theorem 2.23 (ii), pp. 17–18; at `X = ∅` the closure
  `→^X` is `→`).
* **The level aimed at**: 3. A finite model as data: a number `n` of
  states `0, …, n − 1`; a list of pairs for `→`; a list of pairs (state,
  proposition) for `V`; a root.
* **Does a search end by itself?** In K, no: `◇k_c` keeps `◇A`, so its
  premise contains its conclusion's material and it applies again for
  ever. The source ends the search in `K°` by the set-sequent proviso and
  by stopping at finished sequents (pp. 14–16; Lemma 2.22). In the
  explorer, `within` sets aside a `◇k_c` that adds a formula the box
  already has.
* **Cyclic leaves: left out, and where they would go** (decision 3,
  answered: left out for K). The source's `prove` stops at a leaf whose
  set of formulas an inner node already carries (Definition 2.20), and
  its model sends such a leaf back to that node. In K the search makes a
  new box only for a formula `□A`, and puts into a box only the `A` of a
  `□A` or `◇A` of its parent, so the nesting it adds is bounded by the
  modal depth of the formulas of the sequent it started from, and the
  search ends without the test (expected; it is goal 7). For a system where it is needed
  (`4`, `5`), three places take a parameter, and nothing else changes:
  1. the search takes a test "stop at this leaf", given the sets of
     formulas on the path from the root; for K it is constantly false;
  2. "finished" is said relative to that test: a sequent is finished if
     each node is finished or is a leaf the test stops at;
  3. the map from a finished sequent to a model takes a list of further
     pairs for `→`, from the parent of a stopped leaf to the inner node
     it repeats; for K the list is empty. The model as data is already
     a list of pairs for `→`, not a tree, so its type and its checker do
     not change.
  The type of sequents, the family, the moves and the certificate are
  not touched; goals 7, 8 and 9 are stated without cyclic leaves and keep
  their statements, with a different measure in the proof of 7 (the
  number of sets of subformulas, as in Lemma 2.22, in place of the modal
  depth). The search and the model will be written with those three
  parameters only when a system needs them: for K it is a note in the
  files at the three places.

## Q4. How do people use it?

* **The source's worked derivations.** One in system K: Example 2.3,
  pp. 9–10, of `□(a ∨ b) ⊃ (□a ∨ ◇b)`, that is, of the sequent
  `◇(ā ∧ b̄), □a, ◇b`. Upwards: `∨` twice, `□`, `◇k_c`, `∧`, and `◇k_c`
  once more on the right branch. It is the first exercise of the
  reviewer's test. The source has no other, so four more are proposed,
  and the choice is ours: `□(a ∧ b) ⊃ (□a ∧ □b)`;
  `(□a ∧ □b) ⊃ □(a ∧ b)`; `□□(a ∨ ā)`, where the rules act two boxes
  deep; and one that must fail, `□a ⊃ □□a`.
* **The order by hand**: the rules that do not make boxes first, then
  `□`, then `◇k_c` into the boxes made (Figure 2.6 has the same order). A
  reader unfolds `⊃` and negation without comment: the last line of
  Example 2.3 is an equation, not a rule.
* **What the explorer should show**: a sequent in the source's brackets,
  `◇(ā ∧ b̄), [a, ā ∧ b̄], ◇b`, and on request as its tree; `⊃` accepted
  on input; a move that says where it acts, with as much as possible left
  to patterns; of a failed attempt, the open sequent, which is the
  countermodel.

## Q5. Which calculi is it related to?

* **Translations in the literature.** In the source: the variant with
  `◇k` and `ctr` (Proposition 2.5) and system `K_c` (§2.2); the deep
  inference system KSk, both ways, one way with cut (Propositions 2.54,
  2.55); the ordinary sequent calculus of K, whose `□` rule embeds
  (Remark 2.57). Compared in prose, with no translation (§2.4): the
  display calculus, labelled sequents, prefixed tableaux. Named as the
  origin of the formalism: Kashima 1994 ([30]); as a notational variant,
  Poggiolesi's tree-hypersequents ([38]).
* **Calculi already in this project.** The library's example, an
  intuitionistic sequent calculus, unrelated. In lax-logic-in-lean, the
  subframe tableau for lax logic, unrelated.
* **Existing formalisations.** Not found for this calculus in Lean, Coq
  or Isabelle. Searched: two web searches, 2026-11-23. Nearest found:
  [D'Abrera, Dawson and Goré](https://researchportalplus.anu.edu.au/en/publications/a-formally-verified-cut-elimination-procedure-for-linear-nested-s-2/),
  cut elimination for linear nested sequents for tense logic, in Coq;
  [Wu and Goré, ITP 2019](https://drops.dagstuhl.de/opus/volltexte/2019/11086/),
  tableau decision procedures for K, KT and S4 in Lean 3;
  [Hagemeier and Kirst](https://www.ps.uni-saarland.de/extras/iel-ext/paper.pdf),
  K in Coq with decidability by cut elimination (not nested sequents, as
  far as the search result shows).

## Choices of encoding, for the reviewer

Tried in four scratch files outside the repository, not kept: the
screens of "valid" above, and what derives for each type of sequents.

| choice | the options weighed | proposed, and why |
|---|---|---|
| a judgment as data | (a) a type holding a list of itself, `mk (fs : List Form) (boxes : List Seq)`: `DecidableEq` does not derive (tried). (b) the library's `RTree κ (List Form)`: its lookups and updates go by edge label, so each box needs a name, and sequents are then equal only up to renaming. (c) one list of items, each a formula or a box: everything derives (tried), but the formulas of a node are a filter. (d) `leaf (fs : List Form)` or `cons (inner) (rest)`, the node's boxes one at a time and then its formulas: `DecidableEq`, `Repr`, `ToExpr` derive, the functions tried are structural and reduce by `decide +kernel`, no axioms (tried) | (d). It is the source's displayed form `A₁,…,Aₘ,[Δ₁],…,[Δₙ]` and needs no groundwork for equality. A new box is added after the existing ones, so that the places of the others do not move |
| how a rule, and a move, names what it acts on | (i) a context as data and an equation, `Γ = C{A ∧ B}`: reads as the figure; but `◇k_c` names a formula and a box, which a list holds at two places, so its conclusion would be an equation up to permutation. (ii) a path of box positions to the node, and in the node the main formula (and for `◇k_c` the position of the box) | (ii). The conclusion of every constructor is the variable `Γ`; the functions in the side conditions and premises are the ones `step` uses. `#rules` will then print each rule with "if the node at `a` has `A ∧ B`", and the rule table sets that beside the figure |
| lists for multisets | (a) a multiset as a quotient of lists: Lean rejects a type that holds a quotient of lists of itself (tried: the kernel refuses the declaration), so a nested sequent cannot hold a multiset of nested sequents, whatever is done for the formulas. (b) lists, with exchange as a rule. (c) lists, no exchange rule, and exchange a theorem | (c). Exchange is not left out of the theory, only out of the rules. A sequent calculus on lists needs an exchange rule when its rules act at a fixed end of the list; here every rule finds its main formula at any position of the node (and `◇k_c` its box at any position), so nothing has to be brought to the front. What remains is that a rule puts its result at a fixed place, so `K ⊢ Γ` for one order of `Γ` does not give `K ⊢ Γ′` for another by definition: it is goal 4, by induction on the derivation (apply the same rule at the permuted position; the premises are permutations of the old premises), with the same depth. OPEN until proved; if it failed, the encoding would be wrong and (b) the fallback |
| the family: into `Type` or `Prop` | | `Type`: admissibility and cut elimination are functions on derivations, and depth is a function |
| what holds | the family itself; or validity | the family itself, `Fam`, the method's default: a step is an instance of a rule |
| two systems, and measures | two families; one with a parameter; functions on derivations | one family with a Boolean parameter that says whether `cut` is allowed. Depth and cut rank are functions on derivations. `K°` is a second family only if its lemma is proved through it (decision 3) |

## Goals, non-goals, order

**Goals**, in order. The statements go to the reviewer in Lean before
any proof, at the gate of Prove.

    1  K ⊢ Γ  →  Valid Γ                                         (Thm 2.9)
    2  K ⊢ Γ{A∧B} →ⁿ K ⊢ Γ{A} and K ⊢ Γ{B};   K ⊢ Γ{A∨B} →ⁿ K ⊢ Γ{A,B};
       K ⊢ Γ{□A} →ⁿ K ⊢ Γ{[A]}                                   (Lemma 2.4 ii)
    3  K ⊢ Γ →ⁿ K ⊢ [Γ];   K ⊢ Γ{∅} →ⁿ K ⊢ Γ{Δ};   K ⊢ Γ{Δ,Δ} →ⁿ K ⊢ Γ{Δ}
                                                                 (Lemma 2.4 i)
    4  Γ ~ Γ′  →  (K ⊢ Γ →ⁿ K ⊢ Γ′)                              (added)
    5  K ⊢ Γ{A, Ā}                                               (added)
    6  K° ⊢ Γ  →  K ⊢ Γ                                          (Lemma 2.14)
    7  the search terminates                                     (Lemma 2.22)
    8  for every Γ:  K ⊢ Γ,  or a finite model M, as data, and a state s
       with  not  M, s ⊨ Γ_F                                     (Thm 2.23)
    9  Valid Γ → K ⊢ Γ;  the finite model property;  validity is decidable
                                                                 (Thm 2.23 i, Cor. 2.24, 2.25)
    10 K + cut ⊢ Γ  →  K ⊢ Γ                                     (Thm 2.35)

`→ⁿ` means: with a proof of at most the same depth. `~` is permutation
inside every node. `Valid` is truth of `Γ_F` at every state of every
two-valued model (Q2). Goal 8 is a function into a sum type. Goals 2 to 5 are
stated in the encoding's terms at the gate of Prove; `Γ{…}` here is the
source's notation.

**Non-goals**, with the reason for each:

* Everything with `X ≠ ∅`; §2.2; §2.3; Chapter 3: left out at the target
  gate.
* Proposition 2.5 at `ρ = k`: used only by §2.2.
* Deduction theorems: no notion of derivation from hypotheses in the
  source.
* Soundness for `ValidF` (every model the host logic defines, two-valued
  or not): it implies excluded middle, as shown, so it is not provable
  within the policy.
* Any statement of complexity: the source has only the bound of Lemma
  2.22.

## The development's axiom policy

Every theory file within `[propext, Quot.sound]`. No exception is asked
for. Certifiers within the same list, which is `lean-certify`'s default.

## Dependencies

Core Lean only. proof-tools at `main` as of 2026-11-23 (the library's
Lean files as at `e6410cd`; later commits change documents and the skill
only). Toolchain: `leanprover/lean4:v4.31.0`.

## Known non-theorems

| judgment | why it must fail | how it is expected to show here |
|---|---|---|
| `◇p̄, ◇p` (axiom d, `□p ⊃ ◇p`) | one state with no successor | a query where no move applies: there is no box |
| `◇p̄, p` (axiom t, `□p ⊃ p`) | one state, no successor, `p` false | a query where no move applies |
| `p̄, □◇p` (axiom b, `p ⊃ □◇p`) | two states in a chain, `p` at the first only | after `□`, an attempt that stays open at `p̄, [◇p]` |
| `◇p̄, □□p` (axiom 4, `□p ⊃ □□p`) | three states in a chain, `p` at the second and not at the third | after `□`, `◇k_c`, `□`, open at `◇p̄, [p̄, [p]]`; a further `◇k_c` is set aside by `within` |
| `□p̄, □◇p` (axiom 5, `◇p ⊃ □◇p`) | a root with two successors, `p` at one | after `□` twice, open at `[p̄], [◇p]`: no move applies |
| `◇(p̄ ∧ q̄), □p, □q` (`□(p ∨ q) ⊃ □p ∨ □q`) | a root with two successors, `p` false at one and `q` at the other | one branch of `∧` stays open |

## Results that exist in Lean already, used and not re-proved

None about this calculus or its logic. Used from proof-tools:
`ProofTools.Explore` (attempts, the map out, certificates), `LeanCertify`,
`ProofTools.Audit`.

## Budget

| stage | sessions expected | what would make me stop and report |
|---|---|---|
| 0 Survey | this one | |
| 1 Adopt | 2 | `step` does not reduce in the kernel on a small sequent; `apply_move` cannot be made to name a place inside a sequent without a change to the library |
| 2 Prove | 4 | contraction (goal 3) or the truth lemma (goal 8) not closed in two sessions; an axiom outside the bound that cannot be removed |
| 3 Run | 1 | kernel time on the corpus beyond a minute for a sequent of modal depth 3 |
| 4 Explore | 1 | |

## Decisions reserved for the reviewer

*All answered: decisions 2 (in part), 3 and 6 on 2026-11-23 at the first
putting of the gate, the rest when the plan was passed as proposed
(`gates.md`, the second and third entries). The text below is as it was
put.*

1. **Cut elimination: which route.** The statement of goal 10 is a goal
   by rule. Proposed: prove it first by the source's short route (p. 19),
   and decide at the report of Prove whether the procedure of §2.1.4 is a
   further goal. Or say now that the procedure is the goal.
2. **What "valid" means.** *Answered in part, 2026-11-23:* the reviewer
   does not want the indirect form and asked whether a less absolute
   direct one exists. It does: `Valid`, truth at every state of every
   two-valued model (Q2, revised). To confirm: that this is the form
   wanted.
3. **The search of the completeness proof.** *Answered, 2026-11-23:*
   cyclic leaves are left out for K, and the plan says how they would be
   brought in (Q3, three parameters). Logged as a divergence from
   Definition 2.20 and Theorem 2.23 when the search is written. Still to
   confirm: that `K°` is transcribed as a family of its own (proposed:
   yes, four rules, its provisos as side conditions, since goal 6 is
   about it).
4. **The encoding**: the table above, each row. The row "lists for
   multisets" is rewritten to answer the reviewer's question about
   exchange.
5. **The added goals** 4 and 5, and the goals proposed beyond those by
   rule (2, 3, 6, 7, and decidability in 9).
6. **The TeX source.** *Answered, 2026-11-23: yes.* Done; see "The
   source" above.
7. **Who relies on the answers** (Q3).
