# GLS: a tutorial, with graded exercises

<!-- lean-pins: module GLS.TutorialPins; import GLS; open GLS -->

GLS is a cut-free sequent calculus for the provability logic GL. This
page teaches the calculus through thirty exercises, and explains what
has been proved about it in Lean: its syntactic properties (identity,
weakening, inversion, contraction, cut admissibility and cut
elimination, terminating proof search) and its semantic ones (soundness,
completeness, the finite model property, decidability).

The calculus is that of Goré, Ramanayake and Shillito, *Cut-Elimination
for Provability Logic by Terminating Proof-Search: Formalised and
Deconstructed Using Coq* (TABLEAUX 2021), read here from the authors'
Coq files and from chapter 12 of Shillito's thesis (ANU, 2023). The
Lean development is `calculi/GLS/` of
[fairflow/proof-tools](https://github.com/fairflow/proof-tools/tree/9a11e68/calculi/GLS).

**What is checked.** Every derivation, countermodel, height and message
quoted on this page is pinned in
[`GLS/TutorialTest.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/TutorialTest.lean),
which the build compiles. Every displayed statement with a line *Lean:*
under it is printed by Lean from the declaration it names, not typed;
the status on that line, PROVED or OPEN, and the axioms are computed by
Lean, and [`GLS/TutorialPins.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/GLS/GLS/TutorialPins.lean)
fails the build if the page and the library ever differ. A line *Lean,
in paraphrase:* marks a statement written in the usual notation: its
declarations and their status are checked, its wording is not. Names
linked into the source are checked to exist. The prose that describes
how a proof goes is a reading of the Lean files and is not itself
checked.

## 0. Before you start

To build, and to open the file of exercises:

    (cd ~/Lean/Sources/proof-tools && git pull --ff-only)
    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake build)

then open
[`Play/GLSExercises.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/Play/GLSExercises.lean)
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

**Formulas.** A propositional variable `p, q, r, …`, the constant `⊥`,
an implication `A → B`, a boxed formula `□A`. The other connectives are
abbreviations:

    ¬A  :=  A → ⊥          ◇A  :=  ¬□¬A          ⊤  :=  ⊥ → ⊥

In Lean, `GLS.Form` has the four constructors `var`, `bot`, `imp`,
`box`. In a file an implication is typed `⟶`, because Lean reserves
`→`; goals are shown with `→`.

**GL** is the normal modal logic K with Löb's axiom

    □(□A → A) → □A

Read `□A` as "`A` is provable in Peano arithmetic". Löb's axiom then
says: if arithmetic proves that provability of `A` implies `A`, then it
proves `A`. Solovay's theorem (1976) says that GL derives exactly the
modal formulas that arithmetic proves under every such reading. That
background is not formalised here: this development has the sequent
calculus and the Kripke semantics, and no Hilbert system and no
arithmetic.

## 2. The calculus

A **sequent** `Γ ⇒ Δ` is a pair of finite multisets of formulas, the
antecedent and the succedent. It is read: if every formula of `Γ` holds
then some formula of `Δ` does. In Lean the two are lists, and no rule
looks at the order.

There are five rules.

     ─────────────── IdP                ──────────── ⊥L
      Γ, p ⇒ p, Δ                        Γ, ⊥ ⇒ Δ

      Γ, A ⇒ B, Δ                        Γ ⇒ A, Δ      Γ, B ⇒ Δ
     ─────────────── →R                 ───────────────────────── →L
      Γ ⇒ A → B, Δ                           Γ, A → B ⇒ Δ

      ⊠Γ, □A ⇒ A
     ───────────────── GLR
      Γ ⇒ □A, Δ

In GLR, `⊠Γ` is `B, □B` for each boxed formula `□B` of `Γ`; the
formulas of `Γ` that are not boxed are dropped, and so is `Δ`. For
example

    ⊠(□□p, □q, r, p → q)  =  □p, □□p, q, □q

Four things to notice.

* **The identity is on variables only.** `□p ⇒ □p` is not an axiom. It
  is derivable (exercise B1), and so is `A ⇒ A` for every `A` (section
  5).
* **There is no structural rule and no cut.** Weakening is built into
  the axioms and into GLR; contraction, exchange and cut are theorems
  about the calculus, not rules of it.
* **GLR loses information.** Read upwards it keeps only the boxed part
  of the antecedent and one boxed formula of the succedent. The other
  four rules are invertible; GLR is not. `⇒ □p, □(p → p)` is derivable,
  and GLR on `□p` leaves `□p ⇒ p`, which is not.
* **The premise of GLR has `□A` on the left.** This is the one place
  where GL differs from K4, whose rule has the premise `⊠Γ ⇒ A`. The
  extra `□A` is Löb's axiom in the form of a rule: to derive `□A` you may
  assume `□A` while deriving `A`.

In Lean the calculus is an inductive family `GLS.Fam : Seq → Type`, one
constructor for each rule
([`GLS/System.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/System.lean#L22-L38)).
A term of `Fam (Γ ⇒ Δ)` is a derivation, as data: it can be measured,
transformed, and printed.

### A worked derivation: Löb's axiom

Read from the root upwards. Each line is a rule and the sequent it
concludes; the premises of the rule are the lines one step in, below it.

    →R     ⇒ □(□p → p) → □p
    GLR      □(□p → p) ⇒ □p
    →L         □p → p, □(□p → p), □p ⇒ p
    GLR          □(□p → p), □p ⇒ □p, p
    IdP            □p → p, □(□p → p), p, □p, □p ⇒ p
    IdP          p, □(□p → p), □p ⇒ p

Both uses of GLR are on `□p`. The first puts `□p` on the left. After →L
on `□p → p` the left premise has `□p` on both sides, and the second GLR
unboxes the `□p` on the left to `p`, which closes the branch. The
derivation has height 5.

In the editor the same derivation is six lines:

    def lob : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
      glsmove impR □(□p ⟶ p) □p
      glsmove glr p
      glsmove impL □p p
      glsmove glr p
      glsmove idP 0
      glsmove idP 0

| line | what it does |
|---|---|
| `glsmove` | lists the moves that apply at the first goal; none is made |
| `glsmove impR` | makes the move if only one →R applies; otherwise offers each |
| `glsmove impL □p p` | the move with its principal formula `□p → p` in full |
| `glsmove glr p` | GLR on `□p` |
| `glsmove idP 0` | IdP on the variable numbered 0, which is `p` (`q` is 1, `r` is 2) |
| `glsmove botL` | ⊥L |
| `glsmove where` | draws the attempt so far |
| `#eval IO.println lob.render` | draws a finished derivation, as above |

## 3. Exercises A and B: derivations

**Part A, the propositional rules.**

* **A1** ★ Derive `p ⇒ p` and `⊥ ⇒ q`.
* **A2** ★ Derive `⇒ p → (q → p)`.
* **A3** ★★ Derive Peirce's law, `⇒ ((p → q) → p) → p`. At which sequent
  does the succedent hold two formulas, and why is that needed?
* **A4** ★★ Derive `⇒ ¬¬p → p`.
* **A5** ★ `⇒ p → q` is not derivable. Where do the moves stop? Describe
  a model with one world where the sequent is false.

**Part B, the modal rule.**

* **B1** ★ Derive `□p ⇒ □p`. Write out the premise of GLR in full.
* **B2** ★ Derive `⇒ □(p → p)`. What is the antecedent of the premise of
  GLR when the conclusion has an empty antecedent?
* **B3** ★★ Derive K, `⇒ □(p → q) → (□p → □q)`.
* **B4** ★★ Derive 4, `⇒ □p → □□p`. GLS has no rule for transitivity.
  Which part of the premise of GLR does its work?
* **B5** ★★ Derive `⇒ □⊥ → □p`.
* **B6** ★★★ Derive Löb's axiom without looking at section 2.
* **B7** ★★★ Derive `⇒ ¬□⊥ → ¬□¬□⊥`. Under the arithmetical reading
  this is the second incompleteness theorem: if arithmetic is consistent,
  it does not prove that it is.

## 4. The semantics

A **model** `M = (W, R, V)` is a set of worlds, a relation on it, and a
valuation saying which variables are true at which world. Truth of a
formula at a world:

    w ⊩ p         iff   V(p, w)
    w ⊩ ⊥         never
    w ⊩ A → B     iff   w ⊩ A implies w ⊩ B
    w ⊩ □A        iff   v ⊩ A for every v with w R v

and of a sequent:

    w ⊩ Γ ⇒ Δ     iff   if w ⊩ A for every A in Γ, then w ⊩ B for some B in Δ

A **model of GL** is one whose relation is transitive and conversely
well-founded: there is no infinite chain `w R w₁ R w₂ R …`. In
particular no world sees itself (exercise E2). In Lean:

    structure Model.GL (M : Model) : Prop where
      trans : ∀ x y z, M.R x y → M.R y z → M.R x z
      cwf   : WellFounded (fun x y => M.R y x)

A sequent is **valid** if it is true at every world of every two-valued
model of GL:

    def Valid (s : Seq) : Prop :=
      ∀ M : Model, M.GL → M.TwoValued → ∀ w : M.W, M.satSeq w s

`M.TwoValued` says that every formula is true or not true at every
world. Classically every model is two-valued, and the condition could be
dropped. It is there because the development assumes no excluded middle:
without the condition, soundness would itself give excluded middle, from
the derivable sequent `⇒ p, p → ⊥` and a one-world model whose valuation
is an arbitrary proposition. Exercise E4 asks which rule needs it.

**Finite trees as models.** One model of GL has every finite tree as a
world. A tree is a node carrying the list of variables true there, and a
list of children. `t R u` holds if `u` is a proper subtree of `t`, at
any depth, so the relation is transitive by construction and conversely
well-founded because a subtree is smaller. A **refutation** of a sequent
is a tree at whose root the sequent is false.

    #eval IO.println (explain ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]))

    ⇒ (□p → □q) → □(p → q)
      is not derivable in GLS: it is false at the root of
    {}
      {}
      {p}

Each line is a world with the variables true there; its children are
one step in. The root sees two worlds. At the first `p` is false, so
`□p` is false at the root and `□p → □q` is true there. At the second `p`
is true and `q` false, so `□(p → q)` is false at the root.

The same tree, written as data and checked by the kernel:

    example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
      noDerivable.verdict _ (.node [] [.node [] [], .node [0] []])

### Exercises C: countermodels

For each sequent find a tree that refutes it, by hand, and have the
kernel check it as above. `explain` shows the search's own answer.

* **C1** ★ `⇒ □p → p`. First go as far as the moves go: at which sequent
  does no move apply?
* **C2** ★★ `⇒ □□p → □p`. Why does a single world not do?
* **C3** ★★ `⇒ (□p → □q) → □(p → q)`, with the page closed. Why does
  one world below the root not do? Must the two be siblings?
* **C4** ★★ `⇒ ¬□⊥`: GL does not derive its own consistency.
* **C5** ★★ `□(□p → p) ⇒ p`. Compare with B6: what does Löb's axiom
  conclude, and what does it not?
* **C6** ★★★ `⇒ □□□⊥ → □□⊥`. How many worlds are needed? Say what
  `□ⁿ⊥` expresses about a world.

## 5. The syntactic properties

Write `⊢ₙ Γ ⇒ Δ` for "there is a derivation of `Γ ⇒ Δ` of height at
most `n`". Each statement below is a function on derivations in Lean:
it takes derivations and returns one. All are PROVED. The types are in
[`GLS/Semantics.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/Semantics.lean#L132-L232).

### 5.1 Identity

<!-- lean: GLS.Fam.id paraphrase -->

    ⊢ Γ, A ⇒ A, Δ        for every formula A

*Lean, in paraphrase:* [`GLS.Fam.id`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Identity.lean#L11-L23) · PROVED · axioms: `Quot.sound`, `propext`

[`Fam.id`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Identity.lean#L11-L23 "GLS.Fam.id"), by recursion on `A` (the source's `Id_all_form`). The case
`□A` is GLR followed by the identity on `A`, which is on the left of the
premise because `⊠` unboxes.

### 5.2 Height-preserving admissible rules

| property | statement | Lean |
|---|---|---|
| exchange | if `⊢ₙ Γ ⇒ Δ`, and `Γ'`, `Δ'` are permutations of `Γ`, `Δ`, then `⊢ₙ Γ' ⇒ Δ'` | [`exchange`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Structural.lean#L158-L159 "GLS.exchange") |
| weakening | if `⊢ₙ Γ ⇒ Δ` then `⊢ₙ Γ, A ⇒ Δ` and `⊢ₙ Γ ⇒ A, Δ` | [`weakeningL`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Structural.lean#L161-L163 "GLS.weakeningL"), [`weakeningR`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Structural.lean#L165-L167 "GLS.weakeningR") |
| inversion of →R | if `⊢ₙ Γ ⇒ A → B, Δ` then `⊢ₙ Γ, A ⇒ B, Δ` | [`inversionImpR`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Invert.lean#L135-L136 "GLS.inversionImpR") |
| inversion of →L | if `⊢ₙ Γ, A → B ⇒ Δ` then `⊢ₙ Γ ⇒ A, Δ` and `⊢ₙ Γ, B ⇒ Δ` | [`inversionImpL`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Invert.lean#L138-L139 "GLS.inversionImpL") |
| contraction | if `⊢ₙ Γ, A, A ⇒ Δ` then `⊢ₙ Γ, A ⇒ Δ`; and the same on the right | [`contractionL`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Contract.lean#L169-L171 "GLS.contractionL"), [`contractionR`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Contract.lean#L173-L175 "GLS.contractionR") |

Each returns the new derivation together with a proof that its height
is at most the old one, for example

<!-- lean: GLS.weakeningL -->

    def GLS.weakeningL : WeakeningL
      where GLS.WeakeningL :=
        (A : Form) →
          {Γ0 Γ1 Δ : List Form} → (d : Fam (Γ0 ++ Γ1 ⇒ Δ)) → { d' : Fam (Γ0 ++ A :: Γ1 ⇒ Δ) // d'.height ≤ d.height }

*Lean:* [`GLS.weakeningL`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Structural.lean#L161-L163) · PROVED · axioms: `Quot.sound`, `propext`

Exchange is a theorem here and not a convention because sequents are
lists. Weakening is by recursion on the derivation; at GLR the premise
is weakened by `⊠` of the new formula. Contraction is by induction on
the height and uses both inversions. In the thesis these are Lemmas
12.5.1 to 12.5.5, pp. 172 to 176. GLR has no inversion: see section 2.

### 5.3 Cut admissibility

<!-- lean: GLS.cutBySource GLS.cutAdmissible paraphrase -->

    if  ⊢ Γ ⇒ A, Δ  and  ⊢ Γ, A ⇒ Δ   then  ⊢ Γ ⇒ Δ

*Lean, in paraphrase:* [`GLS.cutBySource`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Cut.lean#L191-L197) · PROVED · axioms: `Quot.sound`, `propext`; [`GLS.cutAdmissible`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Completeness.lean#L65-L72) · PROVED · axioms: `Quot.sound`, `propext`

This is the additive cut: both premises have the same context (thesis,
Theorem 12.7.1). It is PROVED twice.

**`cutBySource`** follows the source's proof. It makes a derivation of
the conclusion from the two given ones, with no model and no search
([`GLS/Cut.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/Cut.lean)).
The induction is the point of the source's paper. It is on the pair

    (size of the cut formula A,  measure of the conclusion Γ ⇒ Δ)

ordered lexicographically, where the second component is the measure
that makes proof search terminate (section 5.5). It is not the heights
of the two given derivations: the termination of proof search does the
work that a parameter on derivations does elsewhere. (Background from
the literature, not read for this development: Valentini's proof of
1983 carries a third induction parameter, the width.)

The conclusion `Γ ⇒ Δ` is examined first.

* If it is an axiom, it is derived at once.
* If it has an implication at top level, both premises of the cut are
  inverted on it, the cut is made at the premise or premises of that
  rule, which have smaller measure, and the rule is applied.
* Otherwise the last rule of the first premise decides. For IdP the cut
  formula is contracted in the second premise. For →R the cut formula is
  `C → D`, and the cut becomes two cuts, on `C` and on `D`, which are
  smaller formulas. For GLR on a box of `Δ`, the same GLR concludes
  `Γ ⇒ Δ`.

The remaining case is the one that is special to GL. The cut formula is
`□B`, the first premise ends with GLR on it, and the second premise can
then only end with GLR on some `□C` of `Δ`:

    d₀ :  ⊠Γ, □B ⇒ B                 (the premise of GLR in the first)
    e₀ :  B, □B, ⊠Γ, □C ⇒ C          (the premise of GLR in the second)

Three steps:

* a cut on `B`, a smaller formula, of `d₀` (weakened) with `e₀`, gives
  `□B, ⊠Γ, □C ⇒ C`;
* GLR on `□B` from `d₀` (weakened) gives `⊠Γ, □C ⇒ □B, C`;
* a cut on `□B` of those two gives `⊠Γ, □C ⇒ C`. The cut formula has not
  become smaller, but the conclusion of this cut is a premise of GLR at
  `Γ ⇒ Δ`, so its measure is smaller.

GLR on `□C` then gives `Γ ⇒ Δ`.

**`cutAdmissible`** is four lines: both premises are valid by soundness,
cut preserves validity, so the conclusion is valid, so the search of
section 6 returns a derivation of it. The derivation it returns owes
nothing to the two it was given.

### 5.4 Cut elimination

GLS + (cut) is the family `FamCut`: the five rules and the additive cut
as a sixth.

<!-- lean: GLS.cutElimination GLS.cutEliminationBySearch -->

    def GLS.cutElimination : CutElimination
      where GLS.CutElimination :=
        (s : GLS.Seq) → FamCut s → Fam s

    def GLS.cutEliminationBySearch : CutElimination
      where GLS.CutElimination :=
        (s : GLS.Seq) → FamCut s → Fam s

*Lean:* [`GLS.cutElimination`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/CutRule.lean#L70-L72) · PROVED · axioms: `Quot.sound`, `propext`; [`GLS.cutEliminationBySearch`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/CutRule.lean#L74-L76) · PROVED · axioms: `Quot.sound`, `propext`

PROVED, by recursion on the derivation, removing each cut with
`cutBySource` (thesis, Theorem 12.7.2). `cutEliminationBySearch` does
the same with `cutAdmissible`.

### 5.5 Terminating proof search: PSGLS

Read upwards, GLR can be repeated for ever: from `□p ⇒ □p` it leaves
`p, □p, □p ⇒ p`, and nothing in GLS forbids applying it where an axiom
would do. The source's remedy is a second calculus, **PSGLS**: the rules
of GLS, a further axiom IdB (`Γ, □A ⇒ □A, Δ`), and GLR restricted to
conclusions that are not an instance of IdP, IdB or ⊥L.

<!-- lean: GLS.psEquivalent GLS.psTermination -->

    def GLS.psEquivalent : PSEquivalent
      where GLS.PSEquivalent :=
        (s : GLS.Seq) → (Fam s → PSFam s) × (PSFam s → Fam s)

    theorem GLS.psTermination : PSTermination
      where GLS.PSTermination :=
        WellFounded PSPrem

*Lean:* [`GLS.psEquivalent`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/PS.lean#L43-L44) · PROVED · axioms: `Quot.sound`, `propext`; [`GLS.psTermination`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Measure.lean#L271-L276) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. `PSPrem p c` says that `p` is a premise of an instance of a
rule of PSGLS with conclusion `c`, so the second statement says that
there is no infinite sequence of sequents each a premise of the one
before. The thesis states termination in another form (Theorem 12.6.1:
every sequent has a derivation attempt of maximal height, and that
height falls from conclusion to premise), with the same measure.

The measure. Let `U` be the boxed subformulas of the sequent at the
root. For a sequent `Γ ⇒ Δ` met during the search let `b` be the number
of members of `U` that are not in `Γ` (the *usable boxes*), and `i` the
number of implication signs in the sequent. The implication rules lower
`i` and do not raise `b`. Restricted GLR lowers `b`: the box `□A` it is
applied to enters the antecedent and was not there before, since the
conclusion is not an instance of IdB. It may double `i`. The source
compares the pairs `(b, i)` lexicographically; the Lean file joins them
in one number that falls at every step,

    weight U (Γ ⇒ Δ)  =  (i + 1) · 3ᵇ

### Exercises D: the theorems, used

* **D1** ★★ `Fam.id` on `□(p → q)` gives a derivation of
  `□(p → q) ⇒ □(p → q)`. Predict its height from the recursion in 5.1,
  then evaluate `d1.height`.
* **D2** ★★★ Necessitation is a derived rule. Write

      def nec {A : Form} (d : Fam ([] ⇒ [A])) : Fam ([] ⇒ [□A])

* **D3** ★★★★ Modus ponens is a derived rule. Write

      def mp {A B : Form} (d₁ : Fam ([] ⇒ [A ⟶ B])) (d₂ : Fam ([] ⇒ [A])) : Fam ([] ⇒ [B])

* **D4** ★★★★ Löb's rule: from `⇒ □A → A` to `⇒ A`. Write

      def lobRule {A : Form} (d : Fam ([] ⇒ [□A ⟶ A])) : Fam ([] ⇒ [A])

  Which instance of GLR is Löb's rule already?
* **D5** ★★ In GLS + (cut), build a derivation of `□p ⇒ □□□p` whose last
  rule is a cut on `□□p`, and eliminate the cut with `cutElimination`
  and with `cutEliminationBySearch`. Compare the heights.
* **D6** ★★★ Prove, with no model, that GLS + (cut) does not derive the
  empty sequent:

      theorem consistent : FamCut ([] ⇒ []) → False

  Where is cut elimination used, and why is it needed?
* **D7** ★★★★ Prove, with no model, that GLS does not derive `⇒ □⊥`.
* **D8** ★★ From `□⁶p ⇒ □⁷p` apply GLR six times, each time to the one
  formula of the succedent. How many formulas does each antecedent hold?
  Which admissible rule of 5.2 would remove the repetitions?

## 6. The semantic properties

### 6.1 Soundness

<!-- lean: GLS.soundness -->

    theorem GLS.soundness : Soundness
      where GLS.Soundness :=
        ∀ (s : GLS.Seq) (a : Fam s), Valid s

*Lean:* [`GLS.soundness`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Soundness.lean#L11-L68) · PROVED · axioms: `Quot.sound`, `propext`

PROVED, by induction on the derivation
([`GLS/Soundness.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/Soundness.lean)).
The case of GLR is where the two conditions on a model of GL are used.
Suppose every formula of `Γ` is true at `w`, and let `w R v`; we want
`v ⊩ A`. By induction along the converse of `R`, assume `u ⊩ A` for
every `u` with `v R u` (each such `u` is seen from `w`, by
transitivity). Then `v ⊩ □A`. For each `□B` in `Γ`, `v ⊩ B` because
`w R v`, and `v ⊩ □B` by transitivity. So the antecedent `⊠Γ, □A` of the
premise is true at `v`, and the premise, valid by the induction on the
derivation, gives `v ⊩ A`.

### 6.2 Completeness, as a function

<!-- lean: GLS.proofOrRefutation -->

    def GLS.proofOrRefutation : ProofOrRefutation
      where GLS.ProofOrRefutation :=
        (s : GLS.Seq) → Fam s ⊕ Refutation s

*Lean:* [`GLS.proofOrRefutation`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Search.lean#L389-L394) · PROVED · axioms: `Quot.sound`, `propext`

PROVED: for every sequent, a derivation or a finite tree at whose root
it is false
([`GLS/Search.lean`](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/GLS/Search.lean)).
From it and soundness:

<!-- lean: GLS.completeness -->

    theorem GLS.completeness : Completeness
      where GLS.Completeness :=
        ∀ (s : GLS.Seq), Valid s → Nonempty (Fam s)

*Lean:* [`GLS.completeness`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Completeness.lean#L12-L16) · PROVED · axioms: `Quot.sound`, `propext`

The function is a proof search in the order of PSGLS.

* An axiom (IdP, ⊥L, or a boxed formula on both sides): a derivation.
* An implication at top level: its rule is applied. The rule is
  invertible, and semantically so: a tree that refutes a premise refutes
  the conclusion.
* Otherwise the sequent has only variables and boxed formulas, with no
  variable on both sides. GLR is tried on each `□A` of the succedent. If
  one premise has a derivation, GLR gives one. If every premise
  `⊠Γ, □A ⇒ A` has a refuting tree `t_A`, the refutation of `Γ ⇒ Δ` is
  the tree with the variables of `Γ` true at the root and the `t_A` as
  children.

That the new root refutes the sequent is the truth lemma of the
construction ([`prime_refuted`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Search.lean#L198-L249 "GLS.prime_refuted")). A boxed `□B` in `Γ` is true at the new
root because every `t_A` makes `B` and `□B` true, which is what `⊠Γ` on
the left of each premise provides. A boxed `□A` in `Δ` is false at the
root because `A` is false at `t_A`. This is why the countermodel of the
converse of K in section 4 has two children: one for each box of
`⇒ □p, □(p → q)`.

The search ends because of the measure of 5.5, with which its number of
steps is bounded in advance.

### 6.3 The finite model property and decidability

<!-- lean: GLS.finiteModelProperty GLS.validDecidable GLS.derivableDecidable -->

    theorem GLS.finiteModelProperty : FiniteModelProperty
      where GLS.FiniteModelProperty :=
        ∀ (s : GLS.Seq), (∀ (M : Model), M.GL → M.TwoValued → M.Finite → ∀ (w : M.W), M.satSeq w s) → Valid s

    def GLS.validDecidable : ValidDecidable
      where GLS.ValidDecidable :=
        (s : GLS.Seq) → Decidable (Valid s)

    def GLS.derivableDecidable : DerivableDecidable
      where GLS.DerivableDecidable :=
        (s : GLS.Seq) → Decidable (Nonempty (Fam s))

*Lean:* [`GLS.finiteModelProperty`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Completeness.lean#L30-L37) · PROVED · axioms: `Quot.sound`, `propext`; [`GLS.validDecidable`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Completeness.lean#L18-L22) · PROVED · axioms: `Quot.sound`, `propext`; [`GLS.derivableDecidable`](https://github.com/fairflow/proof-tools/blob/dbcc34b/calculi/GLS/GLS/Completeness.lean#L24-L28) · PROVED · axioms: `Quot.sound`, `propext`

All PROVED, each a few lines from `proofOrRefutation` and soundness. A
refutation is a finite tree, and the part of the tree model below it is
a finite model of GL. Because the decision procedure is a Lean function
with no axioms in its way, the kernel can run it:

    example : Valid ([] ⇒ [□p ⟶ □□p]) := by decide +kernel
    example : ¬ Valid ([] ⇒ [□p ⟶ p]) := by decide +kernel

### Exercises E: the semantics, in Lean

* **E1** ★ State and prove by `decide +kernel` the validity of one
  sequent you derived in part B, and the non-validity of one you refuted
  in part C.
* **E2** ★★★★ No world of a model of GL sees itself:

      theorem irrefl (M : Model) (h : M.GL) (w : M.W) : ¬ M.R w w

* **E3** ★★★★ Löb's axiom is true at every world of every model of GL,
  directly from the definition of truth:

      theorem lob_true (M : Model) (h : M.GL) (A : Form) (w : M.W) :
          M.sat w (□(□A ⟶ A) ⟶ □A)

* **E4** ★★ The statement of E3 does not ask that the model be
  two-valued; `Valid` does. Which rule of GLS needs it? Find the line in
  `GLS/Soundness.lean`.

## 7. What rests on what

| claim | what stands behind it |
|---|---|
| the theorems of sections 5 and 6 | the kernel, with no `sorry`, within `propext` and `Quot.sound`; each statement and status is printed by Lean and pinned in `GLS/TutorialPins.lean` |
| that `Fam` is the calculus of the source | a reading of 17 lines of Lean against the authors' Coq definition and the thesis's Figure 12.1, made twice by readers with no other context; no difference was found. The 2021 paper itself was not obtained |
| that `Valid` is validity for GL | the definitions of section 4, 42 lines of Lean. The source's Coq files have no semantics; this one is the usual Kripke semantics of GL, chosen by the campaign, with the two-valued restriction explained there |
| the solutions below | each is compiled by the build; where a height or a tree is quoted it is pinned by a test |

The record of the adoption, with every decision and its cost to reverse,
is the campaign's
[closing page](https://github.com/fairflow/proof-tools/blob/9a11e68/calculi/GLS/campaign/report.md).

## 8. Solutions

Derivations are given as the lines typed after `glsmove`.

### Part A

**A1.** `idP 0`; and `botL`.

**A2.** `impR p (q ⟶ p)`, `impR q p`, `idP 0`.

**A3.** `impR ((p ⟶ q) ⟶ p) p`, `impL (p ⟶ q) p`, `impR p q`, `idP 0`,
`idP 0`. After →L the left premise is `⇒ p → q, p`, with two formulas on
the right, and →R on `p → q` gives `p ⇒ q, p`, an axiom by the `p` that
was kept. A calculus with one formula on the right would have to drop
that `p`: Peirce's law is not intuitionistically derivable.

**A4.** `impR (neg (neg p)) p`, `impL (neg p) ⊥`, `impR p ⊥`, `idP 0`,
`botL`.

**A5.** After `impR p q` the goal is `p ⇒ q`, and no move applies. One
world with `p` true and `q` false: `.node [0] []`.

### Part B

**B1.** `glr p`, `idP 0`. The premise is `p, □p, □p ⇒ p`: the first two
formulas are `⊠(□p)`, the third is the `□p` that GLR adds.

**B2.** `glr (p ⟶ p)`, `impR p p`, `idP 0`. The premise of GLR is
`□(p → p) ⇒ p → p`: when `Γ` is empty the antecedent is the diagonal
formula alone.

**B3.** `impR □(p ⟶ q) (□p ⟶ □q)`, `impR □p □q`, `glr q`, `impL p q`,
`idP 0`, `idP 1`. The premise of GLR is
`p, □p, p → q, □(p → q), □q ⇒ q`.

**B4.** `impR □p □□p`, `glr □p`, `glr p`, `idP 0`. The first GLR leaves
`p, □p, □□p ⇒ □p`. The `□p` that `⊠` keeps on the left beside `p` is
what does the work of transitivity: it is still there to be unboxed by
the second GLR.

**B5.** `impR □⊥ □p`, `glr p`, `botL`. The premise of GLR is
`⊥, □⊥, □p ⇒ p`.

**B6.** Section 2.

**B7.** `impR (neg □⊥) (neg □(neg □⊥))`, `impR □(neg □⊥) ⊥`,
`impL □⊥ ⊥`, `glr ⊥`, `impL □⊥ ⊥`, `glr ⊥`, `botL`, `botL`, `botL`.
Drawn:

    →R     ⇒ (□⊥ → ⊥) → □(□⊥ → ⊥) → ⊥
    →R       □⊥ → ⊥ ⇒ □(□⊥ → ⊥) → ⊥
    →L         □(□⊥ → ⊥), □⊥ → ⊥ ⇒ ⊥
    GLR          □(□⊥ → ⊥) ⇒ □⊥, ⊥
    →L             □⊥ → ⊥, □(□⊥ → ⊥), □⊥ ⇒ ⊥
    GLR              □(□⊥ → ⊥), □⊥ ⇒ □⊥, ⊥
    ⊥L                 □⊥ → ⊥, □(□⊥ → ⊥), ⊥, □⊥, □⊥ ⇒ ⊥
    ⊥L               ⊥, □(□⊥ → ⊥), □⊥ ⇒ ⊥
    ⊥L           ⊥, □(□⊥ → ⊥) ⇒ ⊥

It is the derivation of Löb's axiom with `⊥` for `p`, after two uses of
→R and one of →L.

### Part C

**C1.** After `impR □p p` the goal is `□p ⇒ p` and no move applies. One
world that sees nothing, with `p` false: `.node [] []`. There `□p` is
true because there is no world to look at.

**C2.** `.node [] [.node [] []]`: a root that sees one world, where `p`
is false. `□p` is false at the root. `□□p` is true there, because the
one world it sees sees nothing. At a single world `□p` is true, so the
implication is.

**C3.** `.node [] [.node [] [], .node [0] []]`, as in section 4. With
one world below the root, either `p` is false there and `□(p → q)` is
true at the root, or `p` is true there and then `□p` is true at the
root, so `□q` must be, and `p → q` holds below. The two worlds need not
be siblings: the chain `.node [] [.node [] [.node [0] []]]` also refutes
the sequent, since the root sees both. The search returns siblings
because it makes one child for each box it tries.

**C4.** `.node [] []`. At a world that sees nothing `□⊥` is true, so
`¬□⊥` is false.

**C5.** `.node [] []`, with `p` false. Löb's axiom concludes `□p`, that
`p` is provable. It does not conclude `p`.

**C6.** Three worlds in a chain, `.node [] [.node [] [.node [] []]]`,
and no shorter chain does. `□ⁿ⊥` is true at a world exactly when every
chain of worlds leaving it has fewer than `n` steps. (The test pins this
for chains of up to five worlds.) At the top of a chain of three worlds
two steps can be taken, so `□□□⊥` is true and `□□⊥` false.

### Part D

**D1.** 4. The identity on a variable has height 1; on `p → q` it is
→R, then →L, then the two identities: 3; on `□(p → q)` one GLR more.

**D2.** GLR with an empty antecedent has the premise `□A ⇒ A`, which is
the given derivation weakened by `□A` on the left.

    def nec {A : Form} (d : Fam ([] ⇒ [A])) : Fam ([] ⇒ [□A]) :=
      .glr A (List.mem_singleton.2 rfl) (weakeningL (□A) (Γ0 := []) (Γ1 := []) d).1

**D3.** Invert →R in the first derivation to get `A ⇒ B`; weaken the
second to `⇒ A, B`; cut on `A`.

    def mp {A B : Form} (d₁ : Fam ([] ⇒ [A ⟶ B])) (d₂ : Fam ([] ⇒ [A])) : Fam ([] ⇒ [B]) :=
      let i : Fam ([A] ⇒ [B]) := by
        simpa using (inversionImpR A B d₁ (List.mem_singleton.2 rfl)).1
      cutBySource A [] [] [] [B] (weakeningR B (Δ0 := [A]) (Δ1 := []) d₂).1 i

**D4.** Invert →R to get `i : □A ⇒ A`. GLR on `□A` with an empty
antecedent has exactly that premise, so it gives `⇒ □A, A`. Cut on `□A`
with `i`.

    def lobRule {A : Form} (d : Fam ([] ⇒ [□A ⟶ A])) : Fam ([] ⇒ [A]) :=
      let i : Fam ([□A] ⇒ [A]) := by
        simpa using (inversionImpR (□A) A d (List.mem_singleton.2 rfl)).1
      cutBySource (□A) [] [] [] [A] (.glr A (List.mem_cons_self ..) i) i

GLR from `□A ⇒ A` to `⇒ □A` is Löb's rule with a box on its conclusion.

**D5.** With `d₁ : Fam ([□p] ⇒ [□□p, □□□p])` and
`d₂ : Fam ([□□p, □p] ⇒ [□□□p])` from the search, the derivation is
`.cut (□□p) d₁.toCut d₂.toCut`. Both eliminations return a derivation of
height 4; the two given ones have heights 3 and 4.

**D6.** No rule of GLS has the empty sequent as a conclusion: each asks
for a formula in it. In GLS + (cut) the cut rule can conclude any
sequent, so the argument needs the cut removed first.

    theorem empty_not_derivable : Fam ([] ⇒ []) → False := fun d => nomatch d

    theorem consistent : FamCut ([] ⇒ []) → False := fun d =>
      empty_not_derivable (cutElimination _ d)

**D7.** Only GLR can conclude `⇒ □⊥`, and its premise is `□⊥ ⇒ ⊥`,
which no rule concludes. In Lean: `cases` on the derivation, then on the
premise of GLR, each case closed by `simp` on the membership it asks
for. The full proof is `box_bot_not_derivable` in
`GLS/TutorialTest.lean`.

**D8.** 1, 3, 7, 15, 31, 63, 127. Each boxed formula of the antecedent
gives two formulas in the premise, and one is added. Contraction would
remove the repetitions; it is admissible but not part of the rule, and
the rule as the source states it keeps every copy. This is why the
proved search slows on deeply nested boxes, and why the development has
a second search over sets whose answers are checked (the campaign's
`measurements.md`).

### Part E

**E1.** As in 6.3.

**E2.** By induction along the converse of the relation.

    theorem irrefl (M : Model) (h : M.GL) (w : M.W) : ¬ M.R w w := by
      induction w using h.cwf.induction with
      | _ w ih => exact fun hww => ih w hww hww

**E3.** The argument of 6.1, with nothing else around it.

    theorem lob_true (M : Model) (h : M.GL) (A : Form) (w : M.W) :
        M.sat w (□(□A ⟶ A) ⟶ □A) := by
      intro hbox v hwv
      induction v using h.cwf.induction with
      | _ v ih => exact hbox v hwv fun u hvu => ih u hvu (h.trans _ _ _ hwv hvu)

Neither proof depends on any axiom.

**E4.** →R. To show `w ⊩ A → B` or some other formula of `Δ`, the proof
asks whether `w ⊩ A`: if so the premise applies, and if not the
implication is true. That case distinction is `h2 A w` in the case
`impR` of `soundness`. The rule keeps `Δ` beside `A → B`, which is what
makes the calculus classical (compare A3).
