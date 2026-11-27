# MALL: a tutorial, with graded exercises

<!-- lean-pins: module MALL.TutorialPins; import MALL.Explore MALL.ModelRun MALL.Source MALL.Refute MALL.Craig MALL.Uniform MALL.UniformLyndon; open MALL -->

MALL is propositional multiplicative-additive linear logic: the linear
logic of ⊗, ⅋, 1, ⊥ (the multiplicatives) and &, ⊕, ⊤, 0 (the
additives), without the exponentials. This page teaches its one-sided
sequent calculus through twenty-eight exercises, and explains what has
been proved about it in Lean: its syntactic properties (exchange, the
failure of weakening and contraction, identity expansion, cut
admissibility and cut elimination, the inversions, the subformula and
disjunction properties, decidability) and its semantic ones (soundness
and completeness for phase semantics, the finite model property).

The calculus is that of J.-Y. Girard, *Linear logic*, Theoretical
Computer Science 50 (1987), Definition 1.15, and the semantics his phase
semantics, Definitions 1.1 to 1.14. The completeness argument without
cut and the finite model property follow Y. Lafont, *The finite model
property for various fragments of linear logic*, J. Symbolic Logic 62
(1997), read in the author's version. Decidability is Theorem 2.2 of
Lincoln, Mitchell, Scedrov and Shankar, *Decision problems for
propositional linear logic* (1992). The Lean development is
`calculi/MALL/` of
[fairflow/proof-tools](https://github.com/fairflow/proof-tools/tree/5e0d563/calculi/MALL).

**What is checked.** Every derivation, countermodel, height and message
quoted on this page is pinned in
[`MALL/TutorialTest.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/MALL/TutorialTest.lean),
which the build compiles. Every displayed statement with a line *Lean:*
under it is printed by Lean from the declaration it names, not typed;
the status on that line, PROVED or OPEN, and the axioms are computed by
Lean, and
[`MALL/TutorialPins.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/MALL/TutorialPins.lean)
fails the build if the page and the library ever differ. A line *Lean,
in paraphrase:* marks a statement written in the usual notation: its
declarations and their status are checked, its wording is not. Names
linked into the source are checked to exist. The prose that describes
how a proof goes is a reading of the Lean files and is not itself
checked.

Two statements on this page are REFUTED (section 5.2). The script that
writes the captions knows only PROVED and OPEN, so under a refuted
statement the caption names the theorem that is its negation, and the
PROVED there is of the negation.

## 0. Before you start

To build, and to open the file of exercises:

    (cd ~/Lean/Sources/proof-tools && git pull --ff-only)
    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build)

then open
[`Play/MALLExercises.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/Play/MALLExercises.lean)
in the editor, with the infoview. Parts A, B and C can also be done on
paper: the solutions at the end give each derivation as a list of rule
applications.

The grades:

| grade | what it asks |
|---|---|
| ★ | a move or two; reading a rule |
| ★★ | a short derivation, or a small countermodel |
| ★★★ | wants an idea |
| ★★★★ | a proof or a program in Lean |

## 1. The logic

**Formulas.** A propositional letter `p, q, r, …`, the dual `p⊥` of a
letter, one of the four constants `1`, `⊥`, `⊤`, `0`, or one of

    A ⊗ B   "times"       A ⅋ B   "par"       A & B   "with"       A ⊕ B   "plus"

Negation is not a connective. The **linear negation** `A⊥` of a formula
is defined, by De Morgan's laws:

    1⊥ = ⊥        ⊥⊥ = 1        ⊤⊥ = 0        0⊥ = ⊤        (p⊥)⊥ = p
    (A ⊗ B)⊥ = A⊥ ⅋ B⊥            (A ⅋ B)⊥ = A⊥ ⊗ B⊥
    (A & B)⊥ = A⊥ ⊕ B⊥            (A ⊕ B)⊥ = A⊥ & B⊥

so that `A⊥⊥` is `A` itself. Linear implication is an abbreviation:

    A ⊸ B  :=  A⊥ ⅋ B

In Lean, [`Form`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Form.lean#L16-L39 "MALL.Form") has ten constructors, and negation is
the function [`Form.neg`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Form.lean#L50-L64 "MALL.Form.neg"), written `Aᗮ`: a postfix
`⊥` would be read as the constant. The constants are typed `𝟏 ⊥ ⊤ 𝟎`,
and printed `1 ⊥ ⊤ 0`. This page writes `A⊥` in prose and in what Lean
prints, and `Aᗮ` in what you type. There is no notation for `⊸` in the
files: `p ⊸ q` is typed `pᗮ ⅋ q`.

**Two conjunctions, two disjunctions.** A formula is read as a resource
that a derivation uses exactly once. `A ⊗ B` is both `A` and `B`, side
by side. `A & B` is a choice of one of them, made by whoever uses it.
`A ⊕ B` is one of them, chosen by whoever provides it. `A ⅋ B` is the
dual of ⊗, and is best read through `A⊥ ⅋ B`: from `A`, exactly once,
to `B`. Neither conjunction implies the other, and `A ⊸ A ⊗ A` fails
(exercises B2 and C3).

## 2. The calculus

A **sequent** `⊢ A₁, …, Aₙ` is a finite multiset of formulas, all on the
right. In Lean it is a list, and no rule looks at the order.

There are ten rules.

     ───────── ax             ⊢ A, Γ     ⊢ A⊥, Δ
      ⊢ A, A⊥                ───────────────────── cut
                                    ⊢ Γ, Δ

     ───── 1                   ⊢ Γ
      ⊢ 1                    ──────── ⊥
                              ⊢ ⊥, Γ

      ⊢ A, Γ     ⊢ B, Δ        ⊢ A, B, Γ
     ─────────────────── ⊗    ──────────── ⅋
       ⊢ A ⊗ B, Γ, Δ           ⊢ A ⅋ B, Γ

     ──────── ⊤               (no rule for 0)
      ⊢ ⊤, Γ

      ⊢ A, Γ     ⊢ B, Γ        ⊢ A, Γ              ⊢ B, Γ
     ─────────────────── &    ──────────── 1⊕     ──────────── 2⊕
        ⊢ A & B, Γ             ⊢ A ⊕ B, Γ          ⊢ A ⊕ B, Γ

Five things to notice.

* **There is no weakening and no contraction.** The axiom is `⊢ A, A⊥`
  and nothing else, and the rule 1 is `⊢ 1` and nothing else: a formula
  that is not used cannot be dropped, and a formula cannot be used
  twice. Both structural rules fail as admissible rules too (section
  5.2).
* **⊗ splits the context, & shares it.** Read upwards, ⊗ asks which
  formulas of the context go to which premise, and every formula goes to
  one. & gives the whole context to both premises. The same difference
  separates cut, which splits, from the two rules of ⊕, which keep the
  context and choose a side.
* **⊤ is an axiom in any context; 0 has no rule.** A sequent whose only
  hope is a `0` is not derivable.
* **Four rules lose nothing, read upwards**: ⅋, ⊥, & and ⊤. Each can be
  applied as soon as its formula is there (section 5.5). ⊗ and ⊕ ask for
  a choice, and a wrong choice loses the derivation (exercises A6, B4).
* **Exchange is not a rule here.** The source's figure has a rule that
  permutes a sequent. In Lean every rule concludes any permutation of
  the conclusion the figure writes, so exchange is a function on
  derivations and not a constructor (section 5.1).

In Lean the calculus is an inductive family
[`Fam`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/System.lean#L28-L57 "MALL.Fam") `: List Form → Type`, one constructor for each
rule, and the calculus without the cut rule is a second family,
[`CF`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/System.lean#L59-L83 "MALL.CF"), with nine. A term of `Fam Γ` is a derivation, as
data: it can be measured, transformed, and printed. `Derivable Γ` says
that `Fam Γ` has an element.

### A worked derivation: ⊗ distributes over ⊕

One half of the distribution of ⊗ over ⊕ (Girard, 1.13(i)) is
`p ⊗ (q ⊕ r) ⊸ (p ⊗ q) ⊕ (p ⊗ r)`. As a sequent it is the negation of
the left side beside the right side, and the negation of `p ⊗ (q ⊕ r)`
is `p⊥ ⅋ (q⊥ & r⊥)`.

Read from the root upwards. Each line is a sequent and the rule that
concludes it; the premises of the rule are the lines one step in, below
it.

    ⊢ p⊥ ⅋ (q⊥ & r⊥), (p ⊗ q) ⊕ (p ⊗ r)   by ⅋ p⊥ ⅋ (q⊥ & r⊥)
      ⊢ p⊥, q⊥ & r⊥, (p ⊗ q) ⊕ (p ⊗ r)   by & q⊥ & r⊥
        ⊢ q⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   by 1⊕ (p ⊗ q) ⊕ (p ⊗ r)
          ⊢ p ⊗ q, q⊥, p⊥   by ⊗ p ⊗ q [p⊥]
            ⊢ p, p⊥   by ax p
            ⊢ q, q⊥   by ax q
        ⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   by 2⊕ (p ⊗ q) ⊕ (p ⊗ r)
          ⊢ p ⊗ r, r⊥, p⊥   by ⊗ p ⊗ r [p⊥]
            ⊢ p, p⊥   by ax p
            ⊢ r, r⊥   by ax r

The two rules that lose nothing come first: ⅋, then &, which copies the
context `p⊥, (p ⊗ q) ⊕ (p ⊗ r)` to both premises. Only then is a side of
⊕ chosen, the left one where the context has `q⊥` and the right one
where it has `r⊥`. At ⊗ the list in brackets is the part of the context
that goes to the first premise: `p⊥` goes with `p`, and what is left
goes with the other factor. The derivation has height 5 (an axiom has
height 1).

In the editor the same derivation is ten lines:

    def distrib : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
      mallmove par pᗮ (qᗮ & rᗮ)
      mallmove wth qᗮ rᗮ
      mallmove plus₁ (p ⊗ q) (p ⊗ r)
      mallmove tensor p q [pᗮ]
      mallmove ax p
      mallmove ax q
      mallmove plus₂ (p ⊗ q) (p ⊗ r)
      mallmove tensor p r [pᗮ]
      mallmove ax p
      mallmove ax r

| line | what it does |
|---|---|
| `mallmove` | lists the moves that apply at the first goal; none is made |
| `mallmove par` | makes the move if only one ⅋ applies; otherwise offers each |
| `mallmove par pᗮ (qᗮ & rᗮ)` | ⅋ on `p⊥ ⅋ (q⊥ & r⊥)`, its two parts in full |
| `mallmove wth qᗮ rᗮ` | & on `q⊥ & r⊥` (`with` is a keyword of Lean) |
| `mallmove plus₁ A B`, `mallmove plus₂ A B` | 1⊕ and 2⊕ on `A ⊕ B` |
| `mallmove tensor p q [pᗮ]` | ⊗ on `p ⊗ q`; `[pᗮ]` goes to the premise of `p`, the rest to that of `q` |
| `mallmove cut A [Γ]` | cut on `A`; `Γ` goes with `A`, the rest with `A⊥` |
| `mallmove ax p`, `mallmove one`, `mallmove top`, `mallmove bot` | the logical axiom, 1, ⊤, ⊥ |
| `mallmove where` | draws the attempt so far |
| `#eval IO.println distrib.render` | draws a finished derivation, as above |

A query lists every split of each ⊗ of the sequent, and no cut: the cut
formula is yours to choose. At the root of the worked derivation it
says

    mallmove: at goal 0, 3 moves apply; no move is made. Try these:
      [apply] mallmove par pᗮ (qᗮ & rᗮ)
      [apply] mallmove plus₁ (p ⊗ q) (p ⊗ r)
      [apply] mallmove plus₂ (p ⊗ q) (p ⊗ r)

What `mallmove` builds is a derivation of the explorer's proof system;
[`famOfDer`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Proof.lean#L128-L130 "MALL.famOfDer") carries it to a derivation in `Fam`,
which is what the theorems are about. The campaign's
[user's guide](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/campaign/users-guide.md)
has every line of the tactic and every message.

## 3. Exercises A and B: derivations, and resources

**Part A, derivations.**

* **A1** ★ Derive `⊢ p, p⊥`, then `⊢ 1`, then `⊢ ⊤, p, q`: the three
  rules with no premise.
* **A2** ★ Derive `⊢ p ⊸ p`, that is `⊢ p⊥ ⅋ p`; then `⊢ ⊥, 1`; then
  `⊢ 0 ⊸ p`. What is `0 ⊸ p` when the negation is worked out?
* **A3** ★★ Derive `⊢ (p ⊗ q)⊥, p ⊗ q` without the axiom at `p ⊗ q`.
  Then derive commutativity, `⊢ (p ⊗ q)⊥, q ⊗ p`. After ⅋ the tactic
  offers four splits: which one begins a derivation, and what do the
  others leave?
* **A4** ★ `1` is the unit of ⊗ (Girard, 1.9(ii)). Derive
  `⊢ (1 ⊗ p)⊥, p` and `⊢ p⊥, 1 ⊗ p`. Which uses the rule ⊥, and what is
  the split in the other?
* **A5** ★★ Derive `⊢ p ⊸ p & p` and `⊢ p & q ⊸ p`. In the first, how
  many times does the derivation use `p⊥`?
* **A6** ★★★ ⅋ distributes over &. Derive the half
  `(p ⅋ q) & (p ⅋ r) ⊸ p ⅋ (q & r)`, which is the sequent
  `⊢ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥), p ⅋ (q & r)`. Three rules apply at the
  root. What happens if the first move is 1⊕?
* **A7** ★★ Derive `⊢ p⊥, q⊥, q ⊗ p` with a cut on `p ⊗ q` as the last
  rule: the premises are `⊢ p ⊗ q, p⊥, q⊥` and `⊢ (p ⊗ q)⊥, q ⊗ p`.
  Then derive it without cut. Compare the heights.

**Part B, resources.** Sequents that are not derivable, and why.

* **B1** ★ `⊢ 1, 1`. Which moves does the tactic offer? What does
  `mallmove one` say?
* **B2** ★★ `⊢ p ⊸ p ⊗ p`, that is `⊢ p⊥ ⅋ (p ⊗ p)` (Girard, p. 5:
  "A ⊸ A ⊗ A is not derivable, but A ⊸ A & A is"). Go as far as the
  moves go. How many splits are there, and what does each leave?
* **B3** ★★ `⊢ p ⊕ p⊥` is not derivable, and `⊢ p ⊕ p⊥, p ⊕ p⊥` is.
  Derive the second, and say where the first stops. Is `⊢ p ⅋ p⊥`
  derivable?
* **B4** ★★★ At `⊢ p⊥, p ⊗ q⊥, q ⊗ r⊥, r` the tactic offers sixteen
  moves. Why sixteen? How many of them begin a derivation? Find the
  rule of thumb that picks them out.

## 4. The semantics

Girard's **phase semantics** interprets a formula as a set of elements
of a commutative monoid. It is a semantics of provability: it says which
sequents are derivable, and nothing about the derivations.

A **phase space** (Definition 1.1, [`PhaseSpace`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L15-L34 "MALL.PhaseSpace"))
is a commutative monoid `M`, whose elements are the phases, with a set
of phases `⊥`, the antiphases. For a set of phases `G`:

    G⊥  =  { m  :  m·n ∈ ⊥  for every n ∈ G }          the dual (1.2)
    G is a fact   if   G⊥⊥ = G                           (1.3)
    G·H =  { m·n  :  m ∈ G, n ∈ H }                      the product (1.8)

For every `G`, `G ⊂ G⊥⊥` and `G⊥⊥⊥ = G⊥`, so every dual is a fact
(exercise E2), and `G⊥⊥` is the least fact that contains `G`.

A **phase structure** (1.14, [`PhaseStructure`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L53-L59 "MALL.PhaseStructure"))
is a phase space with a fact for each letter. It gives every formula a
fact ([`interp`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L65-L81 "MALL.PhaseStructure.interp")):

    ⟦p⟧      the fact of p              ⟦p⊥⟧     = ⟦p⟧⊥
    ⟦1⟧      = ⊥⊥                       ⟦⊥⟧      = ⊥
    ⟦⊤⟧      = M                        ⟦0⟧      = M⊥
    ⟦A ⊗ B⟧  = (⟦A⟧·⟦B⟧)⊥⊥              ⟦A ⅋ B⟧  = (⟦A⟧⊥·⟦B⟧⊥)⊥
    ⟦A & B⟧  = ⟦A⟧ ∩ ⟦B⟧                ⟦A ⊕ B⟧  = (⟦A⟧ ∪ ⟦B⟧)⊥⊥

A sequent `⊢ A₁, …, Aₙ` is read as the formula `A₁ ⅋ … ⅋ Aₙ`, and the
empty sequent as `⊥` ([`parAll`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L85-L91 "MALL.parAll")). It **holds in the
structure** if the unit of the monoid is in the interpretation of that
formula ([`Sat`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L93-L96 "MALL.PhaseStructure.Sat")), and it is **valid** if
it holds in every phase structure ([`Valid`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Semantics.lean#L98-L100 "MALL.Valid")).

In Lean a set of phases is a predicate, and nothing asks that
membership be decidable. Soundness and completeness (section 6) are
proved with no excluded middle, so nothing is lost by that.

A phase structure in which a sequent does not hold is a **countermodel**
of it, and by soundness the sequent then has no derivation. The
development has two certificates of this kind that the kernel checks,
and this section shows both. The first is a phase structure on a cyclic
group, given as data: it is small and quick to check, and one need not
exist. The second is a saturated set of sequents, which presents a
finite phase structure: one exists for every sequent with no
derivation, and it can be large.

### The first certificate, worked: `⊢ 1, 1` in a cyclic group

Take the monoid ℤ/2, the numbers 0 and 1 under addition modulo 2, with
the one antiphase 1: `⊥ = {1}`. The duals of its four subsets are

    {}⊥ = {0, 1}        {0}⊥ = {1}        {1}⊥ = {0}        {0, 1}⊥ = {}

For example `{1}⊥` is the set of `m` with `m + 1 ∈ {1}`, which is `{0}`.
So

    ⟦1⟧ = ⊥⊥ = {1}⊥ = {0}
    ⟦1 ⅋ 1⟧ = (⟦1⟧⊥·⟦1⟧⊥)⊥ = ({1}·{1})⊥ = {0}⊥ = {1}

The unit of the monoid is 0, and 0 is not in `{1}`: the sequent
`⊢ 1, 1` does not hold in this structure. By soundness it has no
derivation. `⊢ 1` does hold there: 0 is in `{0}`.

The same structure, written as data and checked by the kernel:

    example : ¬ Derivable [𝟏, 𝟏] := noDerivableBy.verdict _ ⟨1, [false, true], []⟩

A [`ZModel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Model.lean#L27-L36 "MALL.ZModel") `⟨k, bot, val⟩` is a phase structure on
ℤ/(k+1): `bot` is the set of antiphases, as a list of Booleans, one for
each phase, and `val` has a set for each letter in the order `p`, `q`,
`r`, whose closure `G⊥⊥` is the letter's fact. The check computes the
interpretation by the clauses above and asks that 0 be not in it.

<!-- lean: MALL.ZModel.not_valid_of_refutes MALL.noDerivableBy -->

    theorem MALL.ZModel.not_valid_of_refutes (z : ZModel) {Γ : List Form} (h : z.refutes Γ = true) : ¬Valid Γ

    def MALL.noDerivableBy : Certify.Certifier (List Form) ZModel fun (Γ : List Form) => Derivable Γ → False

*Lean:* [`MALL.ZModel.not_valid_of_refutes`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Model.lean#L204-L211) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.noDerivableBy`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/ModelRun.lean#L28-L31) · PROVED · axioms: `Quot.sound`, `propext`

That the computed sets are the interpretation in a phase structure is
[`interp_eq`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Model.lean#L163-L202 "MALL.ZModel.interp_eq"), and the step from "not
valid" to "not derivable" is soundness. To ask the searches:

    #eval IO.println (explain [𝟏, 𝟏])

    ⊢ 1, 1
      is not derivable (decided by the proved search)
      refuted in ℤ/2 with antiphases {1}, p = {0, 1}, q = {0, 1}

and [`refuteBy`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/ModelRun.lean#L60-L66 "MALL.refuteBy") `Γ` returns a `ZModel` to paste
into the line above. Both look among a few small cyclic groups. They do
not find a structure for every sequent that has no derivation: for the
converse of half-distributivity,
`⊢ ((p ⊗ q) & (p ⊗ r))⊥, p ⊗ (q & r)`, the proved search decides that
there is no derivation and `refuteBy` returns nothing. The finite model
property (section 6.3) says that a finite structure exists; it does not
say that a cyclic group will do. The second certificate, below, is for
such sequents.

**Weights.** In ℤ/n with `⊥ = {0}`, a set of one phase `{w}` is a fact,
with dual `{−w}`. If every letter is given such a fact, a formula built
from letters, ⊗ and ⅋ is interpreted as one phase too: its weight, the
sum of the weights of its letters, a dual counting negatively. A
sequent of such formulas then holds exactly when its weights sum to 0.
This reading is not proved in Lean; the instances used below are
computed and checked. It is the phase-semantic form of counting
occurrences; the structure of exercise C3 is of this kind.

### The second certificate: a saturated set of sequents

A finite set `D` of sequents is **saturated**
([`saturated`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Saturated.lean#L72-L75 "MALL.saturated")) when

* no member is the conclusion of a rule with no premise: none is
  `⊢ p, p⊥` at a letter, none is `⊢ 1`, and none has a `⊤`;
* at every formula of every member, the rule that introduces the
  formula has a premise that is a member, up to the order of its
  formulas: the premise of ⅋ and of ⊥; one of the two premises of &; the
  premise of 1⊕ and that of 2⊕, both; and, for every way to divide the
  context of a ⊗, one of its two premises.

It is the record of a search that fails: whatever rule is tried at a
member, something it needs is again a member. A certificate that `Γ`
has no derivation is a saturated set of which `Γ` is a member. For
`⊢ p ⊕ p⊥` the set has three sequents:

    example : ¬ Derivable [p ⊕ pᗮ] := noDerivableBySet.verdict _ [[pᗮ], [p ⊕ pᗮ], [p]]

The formula `p ⊕ p⊥` asks for both `⊢ p` and `⊢ p⊥`, and those two ask
for nothing: neither is an axiom. Without `[pᗮ]` the check rejects the
set.

<!-- lean: MALL.countermodel_of_refutedBy MALL.refutation_complete MALL.certified -->

    theorem MALL.countermodel_of_refutedBy {D : List (List Form)} {Γ : List Form} (h : refutedBy D Γ = true) :
      ∃ (S : PhaseStructure), S.Finite ∧ ¬S.Sat Γ

    theorem MALL.refutation_complete (Γ : List Form) (h : ¬Derivable Γ) : refutedBy (fullRefutation Γ) Γ = true

    theorem MALL.certified (Γ : List Form) :
      (∃ (c : ProofTools.Explore.Cert S), treeCert.check Γ c = true) ∨
        ∃ (D : List (List Form)), noDerivableBySet.check Γ D = true

*Lean:* [`MALL.countermodel_of_refutedBy`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Saturated.lean#L272-L276) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.refutation_complete`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Saturated.lean#L365-L370) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.certified`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/SatRun.lean#L40-L48) · PROVED · axioms: `Quot.sound`, `propext`

All PROVED
([`MALL/Saturated.lean`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/MALL/Saturated.lean),
[`MALL/SatRun.lean`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/MALL/SatRun.lean)).
`refutedBy D Γ` is the check: `Γ` is a member of `D`, and `D` is
saturated.

The first statement is why the check is sound. A saturated set presents
a finite phase structure ([`satModel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Saturated.lean#L219-L224 "MALL.satModel")): its phases
are the parts of the members of `D`, and one more phase for every other
sequent; the product is juxtaposition; the antiphases are the phases
that are not members of `D`. It is the construction of section 6.3 with
`D` in the place of the small sequents that have no derivation, and by
Okada's lemma (section 6.2) no member of `D` holds in it. So this
certificate refutes validity as well as derivability
(`noValidBySet`), and the kernel checks the saturation only: it
computes no interpretation.

The second statement is that the certificate is complete:
`fullRefutation Γ` is the set of the small sequents of section 6.3 that
have no derivation without cut. The third joins it to the certificate
for derivations: every sequent has a tree of moves that checks, or a
saturated set that checks, so each side has something written that the
kernel checks.

`fullRefutation` is for the proof. To get a set, ask the producer:
[`refuteSet`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Refute.lean#L107-L112 "MALL.refuteSet") `Γ` returns the sequents that a
failed search visits, a far smaller set, and it returns one whenever
its own search for a derivation fails. The producer is code and is not
trusted; the kernel checks what it returns.
[`describeCountermodel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Refute.lean#L208-L219 "MALL.describeCountermodel") prints the set
and the structure it presents:

    #eval IO.println (describeCountermodel [p ⊕ pᗮ])

    ⊢ p ⊕ p⊥
      is refuted by a saturated set of 3 sequents:
        ⊢ p⊥
        ⊢ p ⊕ p⊥
        ⊢ p
      It presents a phase structure of 5 phases: the parts of those sequents, and ∞ for every other sequent.
      The antiphases are the phases that are not among the 3.
      Computed in it, the sequent holds: false.

**Which certificate.** The limit of the first is existence: `refuteBy`
tries a few cyclic groups and may find nothing. The limit of the second
is size. Every way to divide the context of every ⊗ needs a premise in
the set, so the set grows quickly with the number of ⊗. For the converse
of half-distributivity, where `refuteBy` finds nothing, `refuteSet`
returns seventeen sequents, and the check accepts them.

**The set in numbers.** `refutedBy` is the definition to read, and the
kernel runs it on a set of a few tens of sequents. It is not the form to
run on a large one: it lists the ways to divide a context with
repetition (`2ᵏ` for `k` formulas, where `k` copies of one formula have
`k + 1`), it looks for each premise through the whole set, and it
compares two sequents by counting every formula of both. Under 4 GB the
kernel was stopped on a set of 102 sequents. So a set is also written
in numbers (`CodeCert`, `MALL/Coded.lean`): its formulas listed once in
a table; a sequent one number, whose digit at a formula's place is how
many times the formula occurs; the set a search tree of those numbers.
`codeRefutes C Γ` is the same check read in numbers, and
`refutedBy_of_code` proves that it implies `refutedBy C.sequents Γ`, so
the theorems above hold of the set that the numbers stand for.
`Encode.encode D Γ` writes a set in numbers (code, not trusted);
`noDerivableByCode.verdict Γ C` is the certifier, and it is what
`mallrun prove` writes. Measured: a set of 1 003 sequents is checked by
the kernel in under 5 s (the campaign's
[measurements](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/campaign/measurements.md),
"Why the kernel could not check a set, and the check in numbers").

### Exercises C: phase semantics, and the two certificates

* **C1** ★★ In ℤ/3 with `⊥ = {0}`, compute the dual of each of the
  eight sets of phases. Which are facts? What is the least fact that
  contains `{0, 1}`?
* **C2** ★ In ℤ/2 with `⊥ = {0}`, compute `⟦1⟧`, `⟦⊥⟧` and `⟦1 ⅋ 1⟧`.
  Why does this structure not refute `⊢ 1, 1`?
* **C3** ★★ Refute `⊢ p⊥ ⅋ (p ⊗ p)` and `⊢ p ⊕ p⊥` in one structure on
  ℤ/2, by hand, and have the kernel check it as above.
* **C4** ★★★ `⊢ p ⊸ p ⊗ (p ⊗ p)` is not derivable either. Why does no
  weight in ℤ/2 refute it? Find a structure that does.
* **C5** ★★ Write by hand a saturated set for `⊢ p⊥ ⅋ (p ⊗ p)`, and
  one for `⊢ p & q, p⊥`, and have the kernel check each with
  `noDerivableBySet.verdict`. In the second, one premise of & is in
  your set and the other is not: why must the other be left out?
* **C6** ★★★ Write a saturated set for the sequent of C4. How many
  sequents does it need, against a cyclic group of which order? Then
  evaluate `refuteSet` on the converse of half-distributivity,
  `[((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]`, for which `refuteBy` finds
  nothing. Which of the two certificates would you use for a sequent
  of letters and twenty ⊗?

## 5. The syntactic properties

Each statement below is about the families `Fam` (with cut) and `CF`
(without). Where the Lean is a `def`, the statement is a function on
derivations: it takes derivations and returns one. The goals were
written as named types before any was proved, in
[`MALL/Statements.lean`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/MALL/Statements.lean);
the campaign's
[`statements.md`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/campaign/statements.md)
has each with its source.

### 5.1 Exchange

<!-- lean: MALL.lit_iff_fam -->

    theorem MALL.lit_iff_fam (Γ : List Form) : Nonempty (Lit Γ) ↔ Derivable Γ

*Lean:* [`MALL.lit_iff_fam`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Source.lean#L80-L82) · PROVED · axioms: none

PROVED. [`Lit`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Source.lean#L16-L46 "MALL.Lit") is the source's figure letter for
letter: sequents are sequences, every rule acts on the first formula,
and exchange is a rule. `Fam` is the form the source calls "the variant
without exchange, adapted to multisets of formulas" (p. 24): each rule
concludes any permutation of its conclusion. The theorem says the two
derive the same sequents. In `Fam`, exchange is the function
[`Fam.exch`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/System.lean#L107-L120 "MALL.Fam.exch"), which changes the last rule's proof
of permutation and nothing else, so it keeps the height
([`exchangeKeepsHeight`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L20-L22 "MALL.exchangeKeepsHeight")).

### 5.2 Weakening and contraction: REFUTED

<!-- lean: MALL.not_weakening MALL.not_derivable_one_one paraphrase -->

    weakening:      for every Γ and A,   if ⊢ Γ  then  ⊢ A, Γ
    refuted by:     ⊢ 1  is derivable,   ⊢ 1, 1  is not

*Lean, in paraphrase:* [`MALL.not_weakening`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L115-L117) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.not_derivable_one_one`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L112-L113) · PROVED · axioms: `Quot.sound`, `propext`

**REFUTED.** The statement is the proposition
[`Weakening`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Statements.lean#L67-L68 "MALL.Weakening"); the theorem in the caption is its
negation.

<!-- lean: MALL.not_contraction MALL.derivable_plus_plus MALL.not_derivable_plus paraphrase -->

    contraction:    for every Γ and A,   if ⊢ A, A, Γ  then  ⊢ A, Γ
    refuted by:     ⊢ p ⊕ p⊥, p ⊕ p⊥  is derivable,   ⊢ p ⊕ p⊥  is not

*Lean, in paraphrase:* [`MALL.not_contraction`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L126-L129) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.derivable_plus_plus`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L122-L124) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.not_derivable_plus`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L119-L120) · PROVED · axioms: `Quot.sound`, `propext`

**REFUTED.** The statement is
[`Contraction`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Statements.lean#L70-L71 "MALL.Contraction"); the first theorem in the
caption is its negation.

The source forbids both rules (p. 22). These two theorems say more:
neither is admissible. Each of the three facts about a particular
sequent is decided by the kernel, which runs the search of section 5.7.
Exercises B1 and B3 are the two pairs; the worked example of section 4
and exercise C3 refute the two sequents by a phase structure.

### 5.3 The axiom, from axioms at letters

<!-- lean: MALL.identityExpansion -->

    def MALL.identityExpansion : IdentityExpansion
      where MALL.IdentityExpansion :=
        (Γ : List Form) → CF Γ → { d : CF Γ // d.Atomic }

*Lean:* [`MALL.identityExpansion`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L91-L93) · PROVED · axioms: `Quot.sound`, `propext`

PROVED. [`d.Atomic`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Statements.lean#L48-L58 "MALL.CF.Atomic") says that every logical axiom
of `d` is `⊢ p, p⊥` at a letter. The source remarks that the axiom may
be so restricted (p. 22). The function replaces each axiom `⊢ A, A⊥` by
its derivation [`idExp`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L26-L49 "MALL.idExp") `A`, which is by recursion on
`A`: for `A ⊗ B` it is ⅋ on `A⊥ ⅋ B⊥`, then ⊗ with the split that sends
`A⊥` to `A`, then the two derivations for `A` and `B`; for `A & B` it is
&, then 1⊕ in one premise and 2⊕ in the other; for `1` it is ⊥ and then
1; for `⊤` it is ⊤ (exercises A3 and D1).

### 5.4 Cut admissibility and cut elimination

<!-- lean: MALL.cutAdmissible MALL.cutElimination -->

    def MALL.cutAdmissible : CutAdmissible
      where MALL.CutAdmissible :=
        (A : Form) → (Γ Δ : List Form) → CF (A :: Γ) → CF (Aᗮ :: Δ) → CF (Γ ++ Δ)

    def MALL.cutElimination : CutElimination
      where MALL.CutElimination :=
        (Γ : List Form) → Fam Γ → CF Γ

*Lean:* [`MALL.cutAdmissible`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L262-L264) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.cutElimination`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L266-L280) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED, as functions
([`MALL/Cut.lean`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/MALL/Cut.lean)).
`cutElimination` is by recursion on the derivation: every rule but cut
is kept, on the results for its premises, and at a cut `cutAdmissible`
is applied to the two results.

`cutAdmissible` is three recursions, one inside the other, each
structural:

* on a bound of the size of the cut formula `A`
  ([`cutN`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L256-L260 "MALL.cutN"));
* then on the left derivation, of `⊢ A, Γ`;
* then on the right derivation, of `⊢ A⊥, Δ`.

No sum of heights is needed, and no induction on a pair. The reason is
that no rule of MALL uses a premise twice: without contraction, a cut
that is moved above a rule meets each premise once.

The function [`push`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L87-L151 "MALL.push") takes a cut on a formula `C` up
through a derivation of `⊢ C, Γ`, with `Δ` the context of the other
side. Where the last rule introduces another formula, `C` is in the
context of that rule: the cut goes to the premises that have `C` (both
for &, one for ⊗, none for ⊤), and the same rule is applied below, with
`Δ` added to its context. Where the last rule introduces `C`, `push`
hands over to its argument.

On the left derivation that argument is [`reduce`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L155-L248 "MALL.reduce"):
the last rule on the left introduces `A`, and now the cut on `A⊥` is
pushed up the right derivation in the same way. Where it arrives at the
rule that introduces `A⊥`, the two rules are dual, and the cut is
replaced by cuts on the immediate subformulas, which are smaller:

    ⊗ against ⅋     from  ⊢ A₁, Γ₁   and   ⊢ A₂, Γ₂   and   ⊢ A₁⊥, A₂⊥, Δ:
                    a cut on A₁ gives  ⊢ Γ₁, A₂⊥, Δ;  a cut on A₂ gives  ⊢ Γ₂, Γ₁, Δ
    & against 1⊕    from  ⊢ A₁, Γ   and   ⊢ A₂, Γ   and   ⊢ A₁⊥, Δ:
                    a cut on A₁;  the premise of A₂ is dropped
    1 against ⊥     from  ⊢ Δ,  the premise of ⊥:  it is the result
    ⊤ against 0     no rule introduces 0:  the result is by ⊤
    an axiom        on either side:  the other derivation is the result

The same statement is PROVED a second time, as a proposition, through
the semantics:

<!-- lean: MALL.cutEliminationProp -->

    theorem MALL.cutEliminationProp : CutEliminationProp
      where MALL.CutEliminationProp :=
        ∀ (Γ : List Form), Derivable Γ → Nonempty (CF Γ)

*Lean:* [`MALL.cutEliminationProp`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L242-L244) · PROVED · axioms: `Quot.sound`, `propext`

PROVED, in one line: a derivable sequent is valid (soundness, 6.1), and
a valid sequent has a derivation without cut (completeness, 6.2). This
proof gives no way to compute the derivation from the one it is given.

### 5.5 The inversions

<!-- lean: MALL.parInversion MALL.botInversion MALL.withInversion -->

    def MALL.parInversion : ParInversion
      where MALL.ParInversion :=
        (A B : Form) → (Γ : List Form) → CF (A ⅋ B :: Γ) → CF (A :: B :: Γ)

    def MALL.botInversion : BotInversion
      where MALL.BotInversion :=
        (Γ : List Form) → CF (⊥ :: Γ) → CF Γ

    def MALL.withInversion : WithInversion
      where MALL.WithInversion :=
        (A B : Form) → (Γ : List Form) → CF (A & B :: Γ) → CF (A :: Γ) × CF (B :: Γ)

*Lean:* [`MALL.parInversion`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L284-L288) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.botInversion`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L290-L292) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.withInversion`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Cut.lean#L294-L300) · PROVED · axioms: `Quot.sound`, `propext`

All PROVED, each by one cut (two for &) against a small derivation: for
⅋ against `⊢ A⊥ ⊗ B⊥, A, B`; for ⊥ against `⊢ 1`; for & against
`⊢ A⊥ ⊕ B⊥, A` and `⊢ A⊥ ⊕ B⊥, B`. The source states the inversion of &
(p. 24, (vii)).

⊗ and ⊕ are not invertible. `⊢ p ⊕ q, p⊥ & q⊥` is derivable, and
neither `⊢ p, p⊥ & q⊥` nor `⊢ q, p⊥ & q⊥` is. `⊢ p ⊗ q, p⊥, q⊥` is
derivable, and the split that sends `q⊥` to `p` leaves `⊢ p, q⊥`, which
is not.

### 5.6 The subformula property and the disjunction property

<!-- lean: MALL.subformulaProperty MALL.disjunctionProperty -->

    theorem MALL.subformulaProperty : SubformulaProperty
      where MALL.SubformulaProperty :=
        ∀ (Ξ : List Form) (d : CF Ξ),
          CF.All (fun (Θ : List Form) => ∀ (C : Form), C ∈ Θ → ∃ (D : Form), D ∈ Ξ ∧ C.IsSub D) d

    theorem MALL.disjunctionProperty : DisjunctionProperty
      where MALL.DisjunctionProperty :=
        ∀ (A B : Form), Derivable [A ⊕ B] → Derivable [A] ∨ Derivable [B]

*Lean:* [`MALL.subformulaProperty`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L226-L228) · PROVED · axioms: `propext`; [`MALL.disjunctionProperty`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L158-L161) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. `d.All P` says that `P` holds of every sequent of the
derivation `d`, and `C.IsSub D` that `C` is a subformula of `D`. The
first is by induction on the derivation without cut: read upwards,
every rule of `CF` replaces a formula by its immediate subformulas (in
Lincoln, Mitchell, Scedrov and Shankar it is Corollary A.4).

The disjunction property is for a sequent of one formula: the last rule
of a derivation without cut of `⊢ A ⊕ B` can only be 1⊕ or 2⊕
([`disjunction_cf`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L133-L156 "MALL.disjunction_cf")), and cut elimination
supplies the derivation without cut. With a context it fails (exercise
D5).

### 5.7 Decidability

<!-- lean: MALL.derivableDecidable MALL.search_complete -->

    def MALL.derivableDecidable : DerivableDecidable
      where MALL.DerivableDecidable :=
        (Γ : List Form) → Decidable (Derivable Γ)

    theorem MALL.search_complete (n : Nat) (Γ : List Form) : ssize Γ ≤ n → Nonempty (CF Γ) → (search n Γ).isSome = true

*Lean:* [`MALL.derivableDecidable`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L103-L105) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.search_complete`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Decide.lean#L370-L392) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. Read upwards, every rule of `CF` removes a connective or a
constant, so the size of a sequent bounds the height of its derivations
without cut. [`search`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Decide.lean#L244-L255 "MALL.search") `n Γ` tries the logical
axiom, then the rule 1, then each formula of `Γ` in turn as the
principal formula of its rule: ⊤ succeeds; ⅋, ⊥ and & go to their
premises; ⊕ tries one side and then the other; ⊗ tries every split of
the rest of the sequent. It returns a derivation, so it is sound by its
type, and `search_complete` says that it finds one whenever there is
one. With cut elimination this decides `Derivable`.

Because the search is a Lean function by structural recursion, with no
axiom in its way, the kernel can run it:

    example : ¬ Derivable [𝟏, 𝟏] := by decide +kernel
    example : Derivable [p ⊕ pᗮ, p ⊕ pᗮ] := by decide +kernel

It tries every split, so it is slow where ⊗ must split a long context:
the campaign's
[measurements](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/campaign/measurements.md)
put the practical limit between 6 and 12 formulas. Beyond it there is a
second search, by lazy splitting, which is not proved; a derivation it
returns is checked by the kernel as a tree of moves.

### 5.8 Interpolation

<!-- lean: MALL.craigInterpolation MALL.craigForFormulas -->

    def MALL.craigInterpolation : CraigInterpolation
      where MALL.CraigInterpolation :=
        (Γ Δ : List Form) → CF (Γ ++ Δ) → Interpolant Γ Δ

    theorem MALL.craigForFormulas : CraigForFormulas
      where MALL.CraigForFormulas :=
        ∀ (A B : Form),
          Derivable [Aᗮ, B] →
            ∃ (C : Form), Derivable [Aᗮ, C] ∧ Derivable [Cᗮ, B] ∧ ∀ (a : Nat), a ∈ C.letters → a ∈ A.letters ∧ a ∈ B.letters

*Lean:* [`MALL.craigInterpolation`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Craig.lean#L391-L395) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.craigForFormulas`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Craig.lean#L405-L414) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. An [`Interpolant`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Statements.lean#L143-L156 "MALL.Interpolant") of a sequent
divided in two, `⊢ Γ, Δ`, is a formula `C` with derivations without cut
of `⊢ C, Γ` and of `⊢ C⊥, Δ`, every literal of which occurs in `Δ` and,
negated, in `Γ`. Read two-sided, `Γ⊥ ⊢ C` and `C ⊢ Δ`. The condition on
literals is Lyndon's: formulas are in negation normal form, so a letter
occurs in `C` only with a sign it has in `Δ` and, reversed, in `Γ`. That
the letters of `C` are common to `Γ` and `Δ`
([`Interpolant.letters`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Craig.lean#L397-L403 "MALL.Interpolant.letters")) follows, and
`craigForFormulas` is the usual statement for an implication `A ⊸ B`.

The function is Maehara's method, by recursion on the derivation
([`CF.interp`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Craig.lean#L373-L389 "MALL.CF.interp")), for every division of its sequent.
At each rule the principal formula is in `Γ` or in `Δ`. In `Γ`: the
rules ⊥, ⅋ and ⊕ pass the interpolant of the premise on; & gives the ⊕
of the two; ⊗ gives the ⅋ of the two, the context of each premise
divided as `Γ` and `Δ` divide it ([`split4`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Split.lean#L29-L56 "MALL.split4")); ⊤ gives
`0`; an axiom `⊢ A, A⊥` gives `A⊥` when the division separates its two
formulas and `⊥` when it does not. In `Δ` the interpolant is the dual,
got by reversing the division
([`Interpolant.flip`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Craig.lean#L139-L148 "MALL.Interpolant.flip")). The interpolant is
data: it is computed from the derivation, and two derivations of one
sequent can give two interpolants.

    (craigInterpolation [(p ⊗ (q ⊕ r))ᗮ] [(p ⊗ q) ⊕ (p ⊗ r)] d).C = (p ⊗ q) ⊕ (p ⊗ r)
    (craigInterpolation [(p ⊗ q)ᗮ] [(p ⊗ ⊤) ⊕ r] d).C = p ⊗ ⊤

where `d` is the derivation the proved search returns. In the second,
`q` is in the first part only and `r` in the second only, and neither is
in the interpolant.

Sources: interpolation with this condition on signs is D. Roorda's
(thesis, Amsterdam 1991, chapter V), by induction on a derivation
without cut; A. Akbar Tabatabai and R. Jalali (arXiv:1808.06256) prove
the form with the condition on letters, for a sequent divided in two,
for a family of calculi that has MALL. What each states is in the
campaign's
[note on the sources](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/campaign/interpolation-sources.md),
which was read after the proofs were written.

<!-- lean: MALL.uniformInterpolation MALL.uniformInterpolationForFormulas -->

    theorem MALL.uniformInterpolation : UniformInterpolation
      where MALL.UniformInterpolation :=
        ∀ (p : Nat) (Γ : List Form),
          ∃ (I : Form),
            (∀ (a : Nat), a ∈ I.letters → a ≠ p ∧ a ∈ lettersL Γ) ∧
              Derivable (Iᗮ :: Γ) ∧
                ∀ (Δ : List Form), (∀ (a : Nat), a ∈ lettersL Δ → a ≠ p) → Derivable (Γ ++ Δ) → Derivable (I :: Δ)

    theorem MALL.uniformInterpolationForFormulas : UniformInterpolationForFormulas
      where MALL.UniformInterpolationForFormulas :=
        ∀ (p : Nat) (A : Form),
          (∃ (U : Form),
              (∀ (a : Nat), a ∈ U.letters → a ≠ p ∧ a ∈ A.letters) ∧
                Derivable [Uᗮ, A] ∧ ∀ (B : Form), ¬p ∈ B.letters → Derivable [Bᗮ, A] → Derivable [Bᗮ, U]) ∧
            ∃ (E : Form),
              (∀ (a : Nat), a ∈ E.letters → a ≠ p ∧ a ∈ A.letters) ∧
                Derivable [Aᗮ, E] ∧ ∀ (B : Form), ¬p ∈ B.letters → Derivable [Aᗮ, B] → Derivable [Eᗮ, B]

*Lean:* [`MALL.uniformInterpolation`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L853-L853) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.uniformInterpolationForFormulas`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L893-L896) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. Uniform interpolation is stronger than Craig's: the
interpolant depends on one side only. For a sequent `Γ` and a letter `p`,
[`ui`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L106-L107 "MALL.ui") `p Γ` is a formula without `p` such that
`⊢ (ui p Γ)⊥, Γ`, and `⊢ ui p Γ, Δ` for every `Δ` without `p` with
`⊢ Γ, Δ` ([`ui_spec`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L840-L851 "MALL.ui_spec")). For a formula,
[`forallP`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L109-L110 "MALL.forallP") `p A` is the weakest formula without `p`
that implies `A`, and [`existsP`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L112-L113 "MALL.existsP") `p A` the strongest
that `A` implies; one is the dual of the other at `A⊥`.

The interpolant is computed along the rules read upwards (Pitts's
method). No rule of MALL contracts, so every premise is smaller than its
conclusion and the recursion is on a bound of the size
([`uiN`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L101-L104 "MALL.uiN")). `ui p Γ` is the ⊕ of one formula for each way a
derivation of `⊢ Γ, Δ` can end that concerns `Γ`
([`uiStep`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L95-L99 "MALL.uiStep")): `⊥` if `Γ` is empty; `A` if `Γ` is the
one formula `A` without `p`; `1` if `Γ` is `A, A⊥`; for a rule at a
formula of `Γ`, `⊤` for ⊤, the interpolant of the premise for ⊥, ⅋ and
each side of ⊕, the & of the two for &, and for ⊗ the ⊗ of the two for
each division of the rest; and, for a ⊗ of `Δ` whose premises divide `Γ`,
the ⅋ of the interpolants of the two parts. That `ui p Γ` implies `Γ` is
by recursion on the bound ([`uiN_below`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L457-L511 "MALL.uiN_below")); that it
is the weakest is by induction on a derivation without cut of `⊢ Γ, Δ`,
for every division ([`uiN_greatest`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Uniform.lean#L608-L836 "MALL.uiN_greatest")). The
formula is simplified as it is built: `0` is dropped from a ⊕ and
annihilates a ⊗, the units are removed, a disjunct is taken once.

    forallP 0 (p ⅋ pᗮ) = 𝟏                    existsP 0 (p ⊗ pᗮ) = ⊥
    forallP 0 (pᗮ ⅋ (p ⊗ q)) = q              existsP 0 (p ⊗ (pᗮ ⅋ q)) = q
    forallP 0 (p ⅋ p) = 𝟎                     existsP 0 (p ⊗ q) = ⊤ ⊗ q

The kernel computes each. The last shows the logic: in classical logic
`∃p (p ∧ q)` is `q`, but here `p ⊗ q ⊢ q` would be weakening, and the
strongest consequence of `p ⊗ q` without `p` is `⊤ ⊗ q`. For sequents of
several formulas the interpolant is long: it is not simplified up to the
commutativity of ⅋.

<!-- lean: MALL.uniformInterpolationLyndon MALL.uniformInterpolationLyndonForFormulas -->

    theorem MALL.uniformInterpolationLyndon : UniformInterpolationLyndon
      where MALL.UniformInterpolationLyndon :=
        ∀ (p : Nat) (Γ : List Form),
          ∃ (I : Form),
            (∀ (ℓ : Form), ℓ ∈ I.lits → ℓ ∈ litsL Γ) ∧
              (∀ (a : Nat), a ∈ I.letters → a ≠ p ∧ a ∈ lettersL Γ) ∧
                Derivable (Iᗮ :: Γ) ∧
                  ∀ (Δ : List Form), (∀ (a : Nat), a ∈ lettersL Δ → a ≠ p) → Derivable (Γ ++ Δ) → Derivable (I :: Δ)

    theorem MALL.uniformInterpolationLyndonForFormulas : UniformInterpolationLyndonForFormulas
      where MALL.UniformInterpolationLyndonForFormulas :=
        ∀ (p : Nat) (A : Form),
          (∃ (U : Form),
              (∀ (ℓ : Form), ℓ ∈ U.lits → ℓ ∈ A.lits) ∧
                (∀ (a : Nat), a ∈ U.letters → a ≠ p ∧ a ∈ A.letters) ∧
                  Derivable [Uᗮ, A] ∧ ∀ (B : Form), ¬p ∈ B.letters → Derivable [Bᗮ, A] → Derivable [Bᗮ, U]) ∧
            ∃ (E : Form),
              (∀ (ℓ : Form), ℓ ∈ E.lits → ℓ ∈ A.lits) ∧
                (∀ (a : Nat), a ∈ E.letters → a ≠ p ∧ a ∈ A.letters) ∧
                  Derivable [Aᗮ, E] ∧ ∀ (B : Form), ¬p ∈ B.letters → Derivable [Aᗮ, B] → Derivable [Eᗮ, B]

*Lean:* [`MALL.uniformInterpolationLyndon`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/UniformLyndon.lean#L187-L188) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.uniformInterpolationLyndonForFormulas`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/UniformLyndon.lean#L190-L193) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. The uniform interpolant also keeps the signs: every literal
of `ui p Γ` is a literal of `Γ`, and so every literal of `∀p A` and of
`∃p A` is a literal of `A` ([`ui_lits`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/UniformLyndon.lean#L166-L169 "MALL.ui_lits"),
[`forallP_lits`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/UniformLyndon.lean#L171-L175 "MALL.forallP_lits"),
[`existsP_lits`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/UniformLyndon.lean#L177-L185 "MALL.existsP_lits")). For `∃p A`, which is defined
as a negation at `A⊥`, the two negations cancel; the other polarity was
tested as a control and fails. None of the sources read states a
condition on signs for a uniform interpolant.

Sources: uniform interpolation for this logic is Theorem 4.3 of
M. Alizadeh, F. Derakhshan and H. Ono, *Uniform interpolation in
substructural logics* (Review of Symbolic Logic 7, 2014), who call the
logic InFLₑ, and is covered by Theorem 4.3 of A. Akbar Tabatabai and
R. Jalali (arXiv:1808.06258), who call it CFLₑ. Both use Pitts's method
on two-sided calculi. The construction here was made and proved before
those papers were read, and is of the same kind as the first paper's
table of clauses, in one-sided form; that paper writes out no proof for
this logic. Before the proof, the statement was screened: for 21
formulas, both properties against the decision procedure over 264 test
formulas ([`MALL/UniformTest.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/MALL/MALL/UniformTest.lean)).

### Exercises D: the theorems, used

* **D1** ★★ `d1 : CF [(p ⊗ q) & 𝟏, ((p ⊗ q) & 𝟏)ᗮ]` is one logical
  axiom, of height 1. Predict the height of
  `(identityExpansion _ d1).1` from the recursion in 5.3, and its rules,
  then evaluate.
* **D2** ★★ Apply `cutElimination` to your derivation of A7 that ends
  with a cut. Before you evaluate: which derivation will it return?
  Follow the case "⊗ against ⅋" of 5.4.
* **D3** ★★★★ Modus ponens for ⊸ is a derived rule. Write

      def mp {A B : Form} (d₁ : CF [Aᗮ ⅋ B]) (d₂ : CF [A]) : CF [B]

* **D4** ★★★ Prove, with no model and no search, that MALL does not
  derive the empty sequent:

      theorem consistent : Fam [] → False

  Where is cut elimination used, and why is it needed?
* **D5** ★★★ State the disjunction property for a sequent with a
  context, and refute it.
* **D6** ★★ `⊢ (p & q)⊥, p ⊕ r` is derivable. Divided between its two
  formulas, which letters may an interpolant have? Follow Maehara's
  clauses along a derivation by hand, then evaluate
  `craigInterpolation`.
* **D7** ★★ Predict `existsP 0 (p ⊗ q)`, `existsP 0 (p & q)` and
  `forallP 0 (p ⅋ pᗮ)`, then evaluate. Why is the first not `q`?
* **D8** ★★★ `q ⊢ p ⊸ p ⊗ q` is derivable. Without computing the
  interpolant, prove `Derivable [forallP 0 ((p ⊗ q) ⅋ pᗮ), qᗮ]` from
  `ui_spec`.

## 6. The semantic properties

### 6.1 Soundness

<!-- lean: MALL.soundness -->

    theorem MALL.soundness : Soundness
      where MALL.Soundness :=
        ∀ (Γ : List Form), Derivable Γ → Valid Γ

*Lean:* [`MALL.soundness`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Soundness.lean#L257-L258) · PROVED · axioms: `Quot.sound`, `propext`

PROVED (Girard, Proposition 1.16), by induction on the derivation
([`MALL/Soundness.lean`](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/MALL/Soundness.lean)).
The proof first puts "holds in a structure" in a form that follows the
rules. Call the *context* of `Γ` the product of the duals of the
interpretations of its formulas. Then `⊢ Γ` holds exactly if every
phase of its context is an antiphase
([`sat_iff_holds`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Soundness.lean#L154-L160 "MALL.PhaseStructure.sat_iff_holds")), and
`⊢ A, Γ` holds exactly if every phase of the context of `Γ` is in `⟦A⟧`
([`holds_cons`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Soundness.lean#L189-L199 "MALL.PhaseStructure.holds_cons")). The ten cases
are then short. For ⊗: a phase of the context of `Γ, Δ` is a product
`g·d`; by induction `g ∈ ⟦A⟧` and `d ∈ ⟦B⟧`, so `g·d` is in
`⟦A⟧·⟦B⟧`, which is inside its closure `⟦A ⊗ B⟧`. For cut: `g ∈ ⟦A⟧`
and `d ∈ ⟦A⟧⊥`, so `g·d` is an antiphase by the definition of the dual.
For &: the same phase of the same context is in `⟦A⟧` and in `⟦B⟧`,
which is why & shares its context.

### 6.2 Completeness, without cut

<!-- lean: MALL.completeness -->

    theorem MALL.completeness : Completeness
      where MALL.Completeness :=
        ∀ (Γ : List Form), Valid Γ → Nonempty (CF Γ)

*Lean:* [`MALL.completeness`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L238-L240) · PROVED · axioms: `Quot.sound`, `propext`

PROVED. Girard's Theorem 1.17 concludes a derivation with cut; this is
the stronger form of Lafont's Theorem 1, and it gives cut elimination
again (5.4).

The proof builds one phase structure, the **syntactical model**
([`synCF`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L219-L236 "MALL.synCF")). Its phases are the sequents, up to
permutation; the product is juxtaposition, and the unit is the empty
sequent. Its antiphases are the sequents that have a derivation without
cut. The fact of a letter `p` is `{p}⊥`: the contexts `Γ` with `⊢ p, Γ`
derivable without cut.

<!-- lean: MALL.RuleModel.okada paraphrase -->

    Okada's lemma:    ⟦A⟧ ⊂ {A}⊥     for every formula A
    that is:          if Γ ∈ ⟦A⟧ then ⊢ A, Γ has a derivation without cut

*Lean, in paraphrase:* [`MALL.RuleModel.okada`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L69-L97) · PROVED · axioms: none

PROVED (Lafont, Lemma 1), by induction on the formula. Each case uses
the rule of its connective and no cut. For `A ⊗ B`: by induction every
`Γ ∈ ⟦A⟧` has `⊢ A, Γ` and every `Δ ∈ ⟦B⟧` has `⊢ B, Δ`, so the rule ⊗
gives `⊢ A ⊗ B, Γ, Δ`: the phase `A ⊗ B` is in `(⟦A⟧·⟦B⟧)⊥`, and so
every phase of `(⟦A⟧·⟦B⟧)⊥⊥` makes an antiphase with it.

Completeness follows. By the lemma each formula `A` of a sequent `Γ`,
as a phase, is in `⟦A⟧⊥`, so the phase `Γ` is in the context of `Γ`. If
`Γ` is valid it holds in the syntactical model, every phase of its
context is an antiphase, and `Γ` is one: it has a derivation without
cut.

In Lean the lemma is proved once, for any phase space with a phase for
each formula whose antiphases are closed under the nine rules
([`RuleModel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L26-L52 "MALL.RuleModel")), and the model is built once, from
any congruence on sequents and any set of sequents closed under the
rules ([`Syn`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L115-L148 "MALL.Syn")). The monoid is a quotient of lists.

### 6.3 The finite model property

<!-- lean: MALL.finiteModelProperty MALL.finite_countermodel -->

    theorem MALL.finiteModelProperty : FiniteModelProperty
      where MALL.FiniteModelProperty :=
        ∀ (Γ : List Form), (∀ (S : PhaseStructure), S.Finite → S.Sat Γ) → Derivable Γ

    theorem MALL.finite_countermodel (Γ : List Form) (h : ¬Derivable Γ) : ∃ (S : PhaseStructure), S.Finite ∧ ¬S.Sat Γ

*Lean:* [`MALL.finiteModelProperty`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L235-L238) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.finite_countermodel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L240-L246) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED (Lafont, Theorem 2). The proof is the construction of 6.2
again, for one sequent `Γ₀` at a time
([`fmSyn`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L139-L189 "MALL.fmSyn")). Call a sequent *small* if its formulas
are subformulas of formulas of `Γ₀` and its size is at most that of `Γ₀`
([`Small`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L80-L82 "MALL.Small")); Lafont uses an order on sequents in its
place, and the file says so. Three properties of "small" are used: the
premises of a rule with a small conclusion are small; a part of a small
sequent is small; there are finitely many small sequents up to
permutation. The model identifies two sequents if they are permutations
of each other or neither is small, and its antiphases are the sequents
that are derivable without cut or not small. It has one phase for each
small sequent and one more for all the others, so it is finite
([`finiteModel_finite`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L215-L227 "MALL.finiteModel_finite")). Okada's lemma
holds in it, because it is an instance of `Syn`. If `Γ₀` holds in it
then `Γ₀` is an antiphase, and `Γ₀` is small, so it has a derivation
without cut ([`cf_of_sat_finiteModel`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/FiniteModel.lean#L229-L233 "MALL.cf_of_sat_finiteModel")).

This model is not one to compute with: its phases are classes of
sequents. What the kernel checks are the two certificates of section 4,
and the second of them is this construction for a set of sequents small
enough to write down.

### 6.4 Decidability of validity

<!-- lean: MALL.valid_iff_derivable MALL.validDecidable -->

    theorem MALL.valid_iff_derivable (Γ : List Form) : Valid Γ ↔ Derivable Γ

    def MALL.validDecidable : ValidDecidable
      where MALL.ValidDecidable :=
        (Γ : List Form) → Decidable (Valid Γ)

*Lean:* [`MALL.valid_iff_derivable`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Completeness.lean#L246-L249) · PROVED · axioms: `Quot.sound`, `propext`; [`MALL.validDecidable`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Results.lean#L107-L108) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED: the first is soundness and completeness, and with 5.7 it
gives the second. So validity over all phase structures, a statement
that quantifies over every monoid and every predicate on it, is
equivalent to a proposition the kernel decides:

    example : Valid [pᗮ ⅋ (p & p)] := by decide +kernel
    example : ¬ Valid [pᗮ ⅋ (p ⊗ p)] := by decide +kernel

### Exercises E: the semantics, in Lean

* **E1** ★ State and prove by `decide +kernel` the validity of one
  sequent you derived in Part A, and the non-validity of one from Part
  B.
* **E2** ★★★★ Directly from the definitions of section 4:

      theorem sub_dual_dual (P : PhaseSpace) (G : P.M → Prop) (m : P.M) (h : G m) :
          P.dual (P.dual G) m

      theorem dual_is_fact (P : PhaseSpace) (G : P.M → Prop) : P.IsFact (P.dual G)

  Which law of the monoid is used?
* **E3** ★★★ Validity is closed under cut:

      theorem valid_cut (A : Form) (Γ Δ : List Form)
          (h₁ : Valid (A :: Γ)) (h₂ : Valid (Aᗮ :: Δ)) : Valid (Γ ++ Δ)

  Prove it from the theorems of sections 5 and 6. At which phase
  structure does your proof use the hypotheses?

## 7. What rests on what

| claim | what stands behind it |
|---|---|
| the theorems of sections 5 and 6 | the kernel, with no `sorry`, within `propext` and `Quot.sound`; each statement and status is printed by Lean and pinned in `MALL/TutorialPins.lean` |
| that weakening and contraction are REFUTED | the two negations are theorems (5.2); the facts about the four sequents are decided by the kernel running the proved search |
| that `Fam` is the calculus of the source | a reading of 30 lines of Lean against Definition 1.15, made a second time by a reader with no other context, from page images; no difference was found. The figure as it stands, `Lit`, is proved to derive the same sequents (5.1) |
| that `Valid` is validity in phase semantics | the definitions of section 4, about 75 lines of Lean, read back once by a reader given only the definitions and statements; and that soundness and completeness both hold for them |
| the interpolants of 5.8 | Craig's is computed by a function on derivations and the kernel checks its three properties by its type; the uniform one is a function of the sequent, and its properties are theorems. Its statement was screened against the decision procedure before the proof. That the statements are the published ones rests on a reading of four sources by an agent, after the proofs |
| the certificates of section 4 | for a cyclic structure, the kernel computes the interpretation in the structure given, and `interp_eq` and soundness do the rest; its producer is not trusted and not complete. For a saturated set, the kernel checks the saturation, and `countermodel_of_refutedBy` does the rest; a set exists for every sequent with no derivation (`refutation_complete`), and its producer is not trusted |
| the solutions below | each is compiled by the build; where a height, a set of phases or a message is quoted it is pinned by a test |

The record of the adoption, with every decision and its cost to reverse,
is the campaign's
[closing page](https://github.com/fairflow/proof-tools/blob/5e0d563/calculi/MALL/campaign/report.md).

## 8. Solutions

Derivations are given as the lines typed after `mallmove`.

### Part A

**A1.** `ax p`; `one`; `top`.

**A2.** `par pᗮ p`, `ax pᗮ`. Then `bot`, `one`: the rule ⊥ leaves `⊢ 1`.
Then `par ⊤ p`, `top`: since `0⊥` is `⊤`, the formula `0 ⊸ p` is
`⊤ ⅋ p`, and after ⅋ the sequent `⊢ ⊤, p` is an instance of ⊤.

**A3.** `par pᗮ qᗮ`, `tensor p q [pᗮ]`, `ax p`, `ax q`. For
commutativity: `par pᗮ qᗮ`, `tensor q p [qᗮ]`, `ax q`, `ax p`. The four
splits offered at `⊢ p⊥, q⊥, q ⊗ p` are `[]`, `[qᗮ]`, `[pᗮ]` and
`[pᗮ, qᗮ]`, and only `[qᗮ]` begins a derivation. The split `[pᗮ]`
leaves `⊢ q, p⊥` and `⊢ p, q⊥`; the split `[]` leaves `⊢ q` as its first
premise, and `[pᗮ, qᗮ]` leaves `⊢ p` as its second.

**A4.** `par ⊥ pᗮ`, `bot`, `ax pᗮ`: the negation of `1 ⊗ p` is `⊥ ⅋ p⊥`,
and the rule ⊥ removes the `⊥`. For the other: `tensor 𝟏 p []`, `one`,
`ax p`. The split is empty: the rule 1 takes no context, so all of it
goes with `p`.

**A5.** `par pᗮ (p & p)`, `wth p p`, `ax p`, `ax p`. The one `p⊥` is
used twice, once in each premise of &: the two premises are
alternatives, of which one will be used. For the second:
`par (pᗮ ⊕ qᗮ) p`, `plus₁ pᗮ qᗮ`, `ax pᗮ`.

**A6.** `par p (q & r)`, `wth q r`, `plus₁ (pᗮ ⊗ qᗮ) (pᗮ ⊗ rᗮ)`,
`tensor pᗮ qᗮ [p]`, `ax pᗮ`, `ax qᗮ`,
`plus₂ (pᗮ ⊗ qᗮ) (pᗮ ⊗ rᗮ)`, `tensor pᗮ rᗮ [p]`, `ax pᗮ`, `ax rᗮ`.
Drawn:

    ⊢ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥), p ⅋ (q & r)   by ⅋ p ⅋ (q & r)
      ⊢ p, q & r, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by & q & r
        ⊢ q, p, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by 1⊕ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)
          ⊢ p⊥ ⊗ q⊥, q, p   by ⊗ p⊥ ⊗ q⊥ [p]
            ⊢ p⊥, p   by ax p⊥
            ⊢ q⊥, q   by ax q⊥
        ⊢ r, p, (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)   by 2⊕ (p⊥ ⊗ q⊥) ⊕ (p⊥ ⊗ r⊥)
          ⊢ p⊥ ⊗ r⊥, r, p   by ⊗ p⊥ ⊗ r⊥ [p]
            ⊢ p⊥, p   by ax p⊥
            ⊢ r⊥, r   by ax r⊥

If 1⊕ is the first move it leaves `⊢ p⊥ ⊗ q⊥, p ⅋ (q & r)`, which is
not derivable: the side of ⊕ was chosen before & had said which of `q`
and `r` is wanted, and the two premises of & want different sides. The
rules that lose nothing go first.

**A7.** `cut (p ⊗ q) [pᗮ, qᗮ]`, `tensor p q [pᗮ]`, `ax p`, `ax q`,
`par pᗮ qᗮ`, `tensor q p [qᗮ]`, `ax q`, `ax p`. Without cut:
`tensor q p [qᗮ]`, `ax q`, `ax p`. The heights are 4 and 2.

### Part B

**B1.** None: the query answers
`mallmove: no move applies at goal 0`, and `mallmove one` answers
`the move does not apply to goal 0: 1: the sequent is not ⊢ 1`. The
rule 1 has no context, and the sequent has no other formula for a rule
to act on.

**B2.** `par pᗮ (p ⊗ p)` is the one move offered, and it leaves
`⊢ p⊥, p ⊗ p`. There are two splits, `[]` and `[pᗮ]`. Each leaves
`⊢ p, p⊥` and `⊢ p`: the one `p⊥` can go to one side only, and at `⊢ p`
no move applies.

**B3.** `plus₁ p pᗮ`, `plus₂ p pᗮ`, `ax p`: the first formula gives
`p`, the second `p⊥`. At `⊢ p ⊕ p⊥` the two moves leave `⊢ p` and
`⊢ p⊥`, where no move applies: one copy of the formula can give one
side only. `⊢ p ⅋ p⊥` is derivable, by ⅋ and the axiom: the excluded
middle holds for the multiplicative disjunction and fails for the
additive one.

**B4.** Each of the two ⊗ formulas has a context of three formulas, and
so eight splits. Two of the sixteen moves begin a derivation:
`tensor p qᗮ [pᗮ]` and `tensor q rᗮ [pᗮ, p ⊗ qᗮ]`. The rule of thumb is
to count letters: a sequent of letters, ⊗ and ⅋ can be derivable only
if each letter occurs in it as often as its dual (the weights of
section 4, in ℤ; this is not proved in Lean). For `p ⊗ q⊥` the premise of `p` must have
exactly `p⊥`. A derivation: `tensor p qᗮ [pᗮ]`, `ax p`,
`tensor q rᗮ [qᗮ]`, `ax q`, `ax r`.

### Part C

**C1.**

    {}⊥ = {0, 1, 2}     {0}⊥ = {0}     {1}⊥ = {2}     {2}⊥ = {1}
    {0, 1}⊥ = {0, 2}⊥ = {1, 2}⊥ = {0, 1, 2}⊥ = {}

The dual of `{w}` is `{−w}`, and the dual of a set of two or more
phases is empty, since no `m` has `m + n = 0` for two different `n`.
Five sets are facts: the empty set, the three sets of one phase, and
the whole monoid. The least fact that contains `{0, 1}` is
`{0, 1}⊥⊥ = {}⊥ = {0, 1, 2}`.

**C2.** `⟦1⟧ = {0}⊥ = {0}`, `⟦⊥⟧ = {0}`, and `⟦1 ⅋ 1⟧ = {0}`. In this
structure `1` and `⊥` have the same interpretation, and the unit 0 is
in it: `⊢ 1, 1` holds, and the kernel rejects the structure as a
certificate. The antiphases must tell `1` from `⊥`, as `⊥ = {1}` does.

**C3.** ℤ/2 with `⊥ = {0}` and `p = {1}`:
`⟨1, [true, false], [[false, true]]⟩`. There `⟦p⟧ = ⟦p⊥⟧ = {1}`,
`⟦p ⊗ p⟧ = {0}`, and `⟦p⊥ ⅋ (p ⊗ p)⟧ = {1}`: the weights are 1 + 1 + 1.
And `⟦p ⊕ p⊥⟧ = ({1} ∪ {1})⊥⊥ = {1}`. In both the unit 0 is missing.

    example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
      noDerivableBy.verdict _ ⟨1, [true, false], [[false, true]]⟩

In the same structure `⟦p ⅋ p⊥⟧ = {0}`, as it must be (B3).

**C4.** In ℤ/2 the weight of `p⊥` is that of `p`, and the sequent has
four occurrences: its weight is 0 whatever `p` weighs. In fact no phase
structure on ℤ/2 refutes it, with any antiphases and any fact for `p`:
the test tries all sixteen. In ℤ/3 with `⊥ = {0}` and `p = {1}`,
`⟦p⊥⟧ = {2}` and `⟦p ⊗ (p ⊗ p)⟧ = {0}`, so the sequent is interpreted
as `{2}`: the weights are −1 + 3.

    example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] :=
      noDerivableBy.verdict _ ⟨2, [true, false, false], [[false, true, false]]⟩

Twelve of the sixty-four structures on ℤ/3 for one letter refute it.

**C5.** For `⊢ p⊥ ⅋ (p ⊗ p)`: the sequent, the premise of ⅋, and
`⊢ p`. The context `p⊥` of `p ⊗ p` can be divided in two ways, and each
leaves `⊢ p` as one premise; `⊢ p` asks for nothing.

    example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
      noDerivableBySet.verdict _ [[pᗮ ⅋ (p ⊗ p)], [pᗮ, p ⊗ p], [p]]

For `⊢ p & q, p⊥`: the sequent and `⊢ q, p⊥`.

    example : ¬ Derivable [p & q, pᗮ] := noDerivableBySet.verdict _ [[p & q, pᗮ], [q, pᗮ]]

& asks for one of its two premises. The other is `⊢ p, p⊥`, a logical
axiom at a letter, and a set that has it is not saturated: the check
rejects the set of all three.

**C6.** Four sequents, against a group of order 3:

    example : ¬ Derivable [pᗮ ⅋ (p ⊗ (p ⊗ p))] :=
      noDerivableBySet.verdict _ [[pᗮ ⅋ (p ⊗ (p ⊗ p))], [pᗮ, p ⊗ (p ⊗ p)], [p ⊗ p], [p]]

At `p ⊗ (p ⊗ p)` with the context `p⊥`, the division that sends `p⊥` to
the first premise leaves `⊢ p ⊗ p`, and the other leaves `⊢ p`; at
`⊢ p ⊗ p` the one division leaves `⊢ p`. For the converse of
half-distributivity `refuteSet` returns seventeen sequents, and
`refutedBy` accepts them. For a sequent of letters and twenty ⊗ the set
would be far larger than the 305 sequents the kernel did not check in a
minute. Look for a cyclic structure first: where weights refute the
sequent, the check is a sum.

### Part D

**D1.** 5, with the rules `&(1⊕(⅋(⊗(ax, ax))), 2⊕(⊥(1)))`. The
expansion of the axiom at `p ⊗ q` has height 3 (⅋, ⊗, the axioms at
letters), and at `1` height 2 (⊥, then 1). At `(p ⊗ q) & 1` it is &,
then 1⊕ above the first and 2⊕ above the second: two more than the
higher.

**D2.** The derivation without cut of A7: ⊗ on `q ⊗ p` above two
axioms, of height 2. The left premise of the cut ends with ⊗ on
`p ⊗ q`, from `⊢ p, p⊥` and `⊢ q, q⊥`; the right premise ends with ⅋,
from `⊢ p⊥, q⊥, q ⊗ p`. The two cuts on `p` and on `q` are each against
an axiom, so each returns the other side, and what is left is the
premise of ⅋.

**D3.** Invert ⅋ in the first derivation to get `⊢ A⊥, B`; cut on `A`
with the second.

    def mp {A B : Form} (d₁ : CF [Aᗮ ⅋ B]) (d₂ : CF [A]) : CF [B] :=
      cutAdmissible A [] [B] d₂ (parInversion Aᗮ B [] d₁)

**D4.** No rule of `CF` concludes the empty sequent: each asks that the
conclusion be a permutation of a sequent with a formula in it. In `Fam`
the cut rule can conclude any sequent, so the cut is removed first.

    theorem empty_not_cf : CF [] → False := by
      intro d
      cases d with
      | ax _ h => exact nomatch perm_nil_eq h.symm
      | top _ h => exact nomatch perm_nil_eq h.symm
      | wth _ _ _ h _ _ => exact nomatch perm_nil_eq h.symm
      | plus₁ _ _ _ h _ => exact nomatch perm_nil_eq h.symm
      | plus₂ _ _ _ h _ => exact nomatch perm_nil_eq h.symm
      | one h => exact nomatch perm_nil_eq h.symm
      | bot _ h _ => exact nomatch perm_nil_eq h.symm
      | tensor _ _ _ _ h _ _ => exact nomatch perm_nil_eq h.symm
      | par _ _ _ h _ => exact nomatch perm_nil_eq h.symm

    theorem consistent : Fam [] → False := fun d => empty_not_cf (cutElimination _ d)

**D5.** With a context the statement would be: if `⊢ A ⊕ B, Γ` is
derivable then `⊢ A, Γ` or `⊢ B, Γ` is. The instance of 5.5 refutes it:
`⊢ p ⊕ q, p⊥ & q⊥` is derivable and neither `⊢ p, p⊥ & q⊥` nor
`⊢ q, p⊥ & q⊥` is. The rule & on the context comes below the choice of
a side, as in A6.

    theorem no_disjunction_in_context :
        ¬ ∀ (A B : Form) (Γ : List Form),
          Derivable ((A ⊕ B) :: Γ) → Derivable (A :: Γ) ∨ Derivable (B :: Γ) := fun h =>
      (h p q [pᗮ & qᗮ] (by decide +kernel)).elim (by decide +kernel) (by decide +kernel)

The parentheses in `(A ⊕ B) :: Γ` are needed: before `::` Lean reads
`⊕` as the sum of two types.

**D6.** Only `p`: `q` is in the first part alone and `r` in the second
alone. The derivation the search returns ends with 1⊕ on `p⊥ ⊕ q⊥`, in the
first part, above 1⊕ on `p ⊕ r`, in the second part, above the axiom
`⊢ p, p⊥`, which the division separates. The unary rules pass the
interpolant on, and the axiom gives it:

    (craigInterpolation [(p & q)ᗮ] [p ⊕ r] d).C = p

**D7.** `⊤ ⊗ q`, `q` and `𝟏`. From `p ⊗ q` one cannot drop `p`: the
strongest formula without `p` that it implies keeps the place of `p`, as
`⊤`. From `p & q` one can choose `q`. And `p ⅋ p⊥` holds, so the weakest
formula that implies it is the weakest that holds, `𝟏`.

**D8.** The third part of `ui_spec`, at `Γ = [(p ⊗ q) ⅋ pᗮ]` and
`Δ = [qᗮ]`: `Δ` has no `p`, and `⊢ (p ⊗ q) ⅋ p⊥, q⊥` is derivable.

    example : Derivable [forallP 0 ((p ⊗ q) ⅋ pᗮ), qᗮ] :=
      (ui_spec 0 [(p ⊗ q) ⅋ pᗮ]).2.2 [qᗮ] (by decide) (by decide +kernel)

### Part E

**E1.** As in 6.4.

**E2.** Commutativity. `m ∈ G⊥⊥` asks that `m·n ∈ ⊥` for every
`n ∈ G⊥`; and `n ∈ G⊥` gives `n·m ∈ ⊥`.

    theorem sub_dual_dual (P : PhaseSpace) (G : P.M → Prop) (m : P.M) (h : G m) :
        P.dual (P.dual G) m := fun n hn => by
      rw [P.mul_comm]
      exact hn m h

    theorem dual_is_fact (P : PhaseSpace) (G : P.M → Prop) : P.IsFact (P.dual G) := fun m =>
      ⟨fun h n hn => h n (sub_dual_dual P G n hn), sub_dual_dual P (P.dual G) m⟩

Neither proof depends on any axiom. In the library they are
[`le_dual_dual`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Soundness.lean#L25-L27 "MALL.PhaseSpace.le_dual_dual") and
[`isFact_dual`](https://github.com/fairflow/proof-tools/blob/039e795/calculi/MALL/MALL/Soundness.lean#L36-L37 "MALL.PhaseSpace.isFact_dual").

**E3.** Completeness turns each hypothesis into a derivation without
cut; `cutAdmissible` joins them; soundness returns to validity.

    theorem valid_cut (A : Form) (Γ Δ : List Form) (h₁ : Valid (A :: Γ)) (h₂ : Valid (Aᗮ :: Δ)) :
        Valid (Γ ++ Δ) :=
      let ⟨d₁⟩ := completeness _ h₁
      let ⟨d₂⟩ := completeness _ h₂
      soundness _ ⟨(cutAdmissible A Γ Δ d₁ d₂).toFam⟩

The hypotheses are used at one structure only, the syntactical model of
6.2. A direct proof, in an arbitrary structure, is the case of cut in
the proof of soundness.
