# MALL: the rule table

This page lies beside the source's figure for anyone who reads the
transcription. One row for each rule of the figure, in the figure's
order. The "as printed" column is copied from the source; the output of
`#rules` is pasted as Lean printed it.

Source: J.-Y. Girard, *Linear logic*, TCS 50 (1987), Definition 1.15,
p. 22, read from the page image of the author's scan `linear.pdf` (the
file's page 23). The paper has one version.

The families: `MALL.Fam` (with cut) and `MALL.CF` (without), in
`MALL/System.lean`; the figure letter for letter, `MALL.Lit`, in
`MALL/Source.lean`. The proof system: `MALL.S`, in `MALL/Proof.lean`.

Checked: the source draws no derivation of this fragment; ten
derivations of what it asserts are terms of the family
(`MALL/Source.lean`). The second transcription was run on 2026-11-26:
11 rules in both readings, no difference in a premise, a conclusion or
a side condition; five ambiguities that the second reader found and the
plan had not listed, settled below.

## How a rule of the figure reads in Lean

*(The judgments are flat. This section is here because every row of the
table reads the same way, and it is said once.)* The figure writes a
rule on sequences, with its principal formula first:

    ⊢ A, B, **C**
    ───────────── ⅋
    ⊢ A ⅋ B, **C**

and has a rule EXCH that permutes a sequence. In `Fam` and `CF` the same
rule is

    Fam (A :: B :: Γ)
    ───────────────────
    Fam Ξ
    if   Ξ ~ A ⅋ B :: Γ

The premise is the figure's. The conclusion is any sequent `Ξ` that is a
permutation (`~`, `List.Perm`) of the figure's conclusion. So a rule of
`Fam` is the figure's rule followed by one use of EXCH, and EXCH by
itself is the function `Fam.exch` (`MALL/System.lean`). The source names
this form: "pedantically, in the variant without exchange, adapted to
multisets of formulas" (p. 24). In `Lit` the conclusion is the figure's
own, and EXCH is a constructor; `Lit.toFam` and `Fam.toLit` carry a
derivation of either to the other (`lit_iff_fam`).

## Notation

| in the source | in Lean | note |
|---|---|---|
| a, b, c, … (propositional letters) | `Form.atom n` | numbered; the tests write `p q r` for 0, 1, 2 |
| a^⊥ (the dual of a letter) | `Form.natom n` | printed `p⊥` |
| **1**, ⊥, ⊤, **0** | `𝟏`, `⊥`, `⊤`, `𝟎` (`Form.one`, `.bot`, `.top`, `.zero`) | the bold digits stand for the source's bold |
| A ⊗ B, A ⅋ B, A & B, A ⊕ B | the same (`Form.tensor`, `.par`, `.wth`, `.plus`) | `with` is a keyword of Lean: the constructor is `wth` |
| A^⊥ (linear negation, defined) | `Aᗮ` (`Form.neg`, a function) | a postfix `⊥` would be read as the constant |
| A, B (light: formulas) | `A`, `B` | |
| **A**, **B**, **C**, **D** (bold: "the unspecified lists of formulas", p. 23) | `Γ`, `Δ` | the source uses one alphabet in two weights; Lean has no weights. In the rows below: **C** is `Γ`, **D** is `Δ`; in cut, **B** is `Γ` and **C** is `Δ`; in ⊥, ⊤ and EXCH, **A** is `Γ` |
| ⊢ A₁, …, Aₙ | `Fam [A₁, …, Aₙ]`; printed `⊢ A₁, …, Aₙ` | |
| (none) | `Ξ` | **not in the figure**: the whole conclusion, up to a permutation |
| (none) | `~` | `List.Perm`: the two lists have the same formulas, each as many times |

## The rules

| # | rule, as the source names it | as printed (all p. 22): premises / conclusion / remark | the constructor | agrees with `#rules` below? | the move, and what `step` asks and leaves |
|---|---|---|---|---|---|
| 1 | "Logical axioms" | none / ⊢ A, A^⊥ / "(It is enough to restrict it to the case of a propositional letter a.)" | `Fam.ax`, `CF.ax`, `Lit.ax` | yes, up to D1 | `ax A`; asks that the sequent be a permutation of `[A, Aᗮ]`; leaves nothing |
| 2 | "Cut rule", CUT | ⊢ A, **B** and ⊢ A^⊥, **C** / ⊢ **B**, **C** | `Fam.cut`, `Lit.cut`; none in `CF` | yes, up to D1 | `cut A Γ`; asks that `Γ` be part of the sequent, as a multiset; leaves `A :: Γ` and `Aᗮ ::` the rest |
| 3 | "Exchange rule", EXCH | ⊢ **A** / ⊢ **B** / "where **B** is obtained by permuting the formulas of **A**" | `Lit.exch`; in `Fam` and `CF` no constructor (D1): the functions `Fam.exch`, `CF.exch` | yes for `Lit`; D1 | no move: every move reads the sequent up to a permutation |
| 4 | "Additive rules", ⊤ | none / ⊢ ⊤, **A** / "(axiom, **A** arbitrary) (no rule for **0**)" | `.top` | yes, up to D1 | `top`; asks that `⊤` be in the sequent; leaves nothing |
| 5 | & | ⊢ A, **C** and ⊢ B, **C** / ⊢ A & B, **C** | `.wth` | yes, up to D1 | `wth A B`; asks that `A & B` be in the sequent; leaves `A ::` the rest and `B ::` the rest |
| 6 | 1⊕ | ⊢ A, **C** / ⊢ A ⊕ B, **C** | `.plus₁` | yes, up to D1 | `plus₁ A B`; asks that `A ⊕ B` be in the sequent; leaves `A ::` the rest |
| 7 | 2⊕ | ⊢ B, **C** / ⊢ A ⊕ B, **C** | `.plus₂` | yes, up to D1 | `plus₂ A B`; the same; leaves `B ::` the rest |
| 8 | "Multiplicative rules", **1** | none / ⊢ **1** / "(axiom)" | `.one` | yes, up to D1 | `one`; asks that the sequent be `[𝟏]`; leaves nothing |
| 9 | ⊥ | ⊢ **A** / ⊢ ⊥, **A** | `.bot` | yes, up to D1 | `bot`; asks that `⊥` be in the sequent; leaves the rest (one occurrence removed) |
| 10 | ⊗ | ⊢ A, **C** and ⊢ B, **D** / ⊢ A ⊗ B, **C**, **D** | `.tensor` | yes, up to D1 | `tensor A B Γ`; asks that `A ⊗ B` be in the sequent and `Γ` be part of the rest, as a multiset; leaves `A :: Γ` and `B ::` what is left |
| 11 | ⅋ | ⊢ A, B, **C** / ⊢ A ⅋ B, **C** | `.par` | yes, up to D1 | `par A B`; asks that `A ⅋ B` be in the sequent; leaves `A :: B ::` the rest |

"The rest" is `List.erase`: the sequent with one occurrence of the
principal formula removed. "What is left" is `MALL.sub`: the rest with
one occurrence of each formula of `Γ` removed.

The output of `#rules MALL.Fam`, pasted whole:

```
MALL.Fam — 10 rules
ax
    ───────
    Fam Ξ
    for  A : Form
    if   Ξ ~ [A, Aᗮ]

cut
    Fam (A :: Γ)      Fam (Aᗮ :: Δ)
    ─────────────────────────────────
    Fam Ξ
    for  A : Form,  Γ : List Form,  Δ : List Form
    if   Ξ ~ Γ ++ Δ

top
    ───────
    Fam Ξ
    for  Γ : List Form
    if   Ξ ~ ⊤ :: Γ

wth
    Fam (A :: Γ)      Fam (B :: Γ)
    ────────────────────────────────
    Fam Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A & B :: Γ

plus₁
    Fam (A :: Γ)
    ──────────────
    Fam Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊕ B :: Γ

plus₂
    Fam (B :: Γ)
    ──────────────
    Fam Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊕ B :: Γ

one
    ───────
    Fam Ξ
    if   Ξ ~ [𝟏]

bot
    Fam Γ
    ───────
    Fam Ξ
    for  Γ : List Form
    if   Ξ ~ ⊥ :: Γ

tensor
    Fam (A :: Γ)      Fam (B :: Δ)
    ────────────────────────────────
    Fam Ξ
    for  A : Form,  B : Form,  Γ : List Form,  Δ : List Form
    if   Ξ ~ A ⊗ B :: (Γ ++ Δ)

par
    Fam (A :: B :: Γ)
    ───────────────────
    Fam Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⅋ B :: Γ
```

The output of `#rules MALL.CF`:

```
MALL.CF — 9 rules
ax
    ──────
    CF Ξ
    for  A : Form
    if   Ξ ~ [A, Aᗮ]

top
    ──────
    CF Ξ
    for  Γ : List Form
    if   Ξ ~ ⊤ :: Γ

wth
    CF (A :: Γ)      CF (B :: Γ)
    ──────────────────────────────
    CF Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A & B :: Γ

plus₁
    CF (A :: Γ)
    ─────────────
    CF Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊕ B :: Γ

plus₂
    CF (B :: Γ)
    ─────────────
    CF Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊕ B :: Γ

one
    ──────
    CF Ξ
    if   Ξ ~ [𝟏]

bot
    CF Γ
    ──────
    CF Ξ
    for  Γ : List Form
    if   Ξ ~ ⊥ :: Γ

tensor
    CF (A :: Γ)      CF (B :: Δ)
    ──────────────────────────────
    CF Ξ
    for  A : Form,  B : Form,  Γ : List Form,  Δ : List Form
    if   Ξ ~ A ⊗ B :: (Γ ++ Δ)

par
    CF (A :: B :: Γ)
    ──────────────────
    CF Ξ
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⅋ B :: Γ
```

The output of `#rules MALL.Lit` (the figure as it stands):

```
MALL.Lit — 11 rules
ax
    ────────────
    Lit [A, B]
    for  A : Form,  B : Form
    if   B = Aᗮ

cut
    Lit (A :: Γ)      Lit (Aᗮ :: Δ)
    ─────────────────────────────────
    Lit Ξ
    for  A : Form
    if   Ξ = Γ ++ Δ

exch
    Lit Γ
    ────────
    Lit Γ'
    if   Γ ~ Γ'

top
    ──────────────
    Lit (⊤ :: Γ)
    for  Γ : List Form

wth
    Lit (A :: Γ)      Lit (B :: Γ)
    ────────────────────────────────
    Lit (A & B :: Γ)

plus₁
    Lit (A :: Γ)
    ──────────────────
    Lit (A ⊕ B :: Γ)
    for  B : Form

plus₂
    Lit (B :: Γ)
    ──────────────────
    Lit (A ⊕ B :: Γ)
    for  A : Form

one
    ─────────
    Lit [𝟏]

bot
    Lit Γ
    ──────────────
    Lit (⊥ :: Γ)

tensor
    Lit (A :: Γ)      Lit (B :: Δ)
    ────────────────────────────────
    Lit (A ⊗ B :: Ξ)
    if   Ξ = Γ ++ Δ

par
    Lit (A :: B :: Γ)
    ───────────────────
    Lit (A ⅋ B :: Γ)
```

## In the Lean and not in the figure

| what | why it is there |
|---|---|
| the variable `Ξ` and the hypothesis `Ξ ~ …` of each constructor of `Fam` and `CF` | D1: the sequent as a multiset |
| the explicit arguments `A`, `B`, `Γ`, `Δ` of the constructors | every conclusion is a variable, so Lean cannot infer a rule's data from it (`plan.md`, "Choices of encoding") |
| in `Lit`: `B` with `B = Aᗮ` in the axiom; `Ξ` with `Ξ = Γ ++ Δ` in cut and ⊗ | D2: no computed index in a conclusion |
| the family `CF` | the calculus without the cut rule, for cut elimination; the source does not name it |
| `Fam.height`, `CF.height` | a measure, as functions on derivations; no index is added |

## Side conditions from the prose

| condition | where | which rules | how it is encoded |
|---|---|---|---|
| "where **B** is obtained by permuting the formulas of **A**" | p. 22 | EXCH | `Lit.exch`: `Γ ~ Γ'`; in `Fam`, the hypothesis of every rule |
| "**A** arbitrary" | p. 22 | ⊤ | `Γ` is any list, the empty one too |
| "(no rule for **0**)" | p. 22 | | no constructor has `𝟎` as its principal formula |
| "(It is enough to restrict it to the case of a propositional letter a.)" | p. 22 | the logical axiom | not a condition: the rule is for every `A`. The claim is a goal of stage 2 (identity expansion) |

## The checks

* `#rules MALL.Fam`: 10 rules printed; the figure has 11, and the
  eleventh is EXCH (D1). `#rules MALL.Lit`: 11 rules, the figure's.
  `#rules MALL.CF`: 9 rules, those of `Fam` but cut.
* `#slime` on the two controls: `CleanControl` "0 carrying green
  slime"; `SlimedControl` "1 carrying green slime … index 1 `ms ++ ns`
  ↳ computed by `HAppend.hAppend`".
* `#slime MALL.Fam`: "1 indices, 10 constructors, 0 carrying green
  slime"; `MALL.CF`: 9 constructors, 0; `MALL.Lit`: 11 constructors, 0.
* What the source asserts, as terms of the family (`MALL/Source.lean`,
  namespace `MALL.Source`; the source draws no derivation of the
  fragment, so the choice is the operator's): `axP` (the axiom at a
  letter); `p26` (the two steps of p. 26 in the fragment, by 1⊕); `p5`
  (p. 5, "A ⊸ A & A"); `idTensor` (the remark of p. 22, at `p ⊗ q`);
  `tensorComm`, `tensorUnit`, `tensorUnit'` (1.9(ii)); `distrib` and
  `topAbsorbs` (1.13(i)); `cutEx` (the cut rule). Every rule of the
  figure is used by at least one; `p5Lit` is one of them written in the
  figure's own form, with its exchange. In the tests
  (`MALL/Test.lean`, section 9) the derivation built with the tactic
  and mapped out is, by `rfl`, the term written here, for `p5`,
  `idTensor` and `distrib`.
* S2 (`famToDer`, `MALL/Proof.lean`): PROVED. `step` refuses no
  instance of a rule.

## The second transcription

Made on 2026-11-26 by a fresh agent of the operator, given only the
page images of pp. 21-24 of the source and the name of the system; told
to open no other file (`reference/adopt.md` §7). It found 11 rules.
Compared with what `#rules MALL.Lit` prints (the figure's form) and,
through D1, with `#rules MALL.Fam`.

| # | rule | the second reading: premises / conclusion / remark | agrees with `#rules`? | settled from the source at | changed here |
|---|---|---|---|---|---|
| 1 | Logical axioms | none / ⊢A, A^⊥ / "(It is enough to restrict it …)" | yes | | nothing |
| 2 | CUT | ⊢A, **B** ; ⊢A^⊥, **C** / ⊢**B**, **C** | yes | | nothing |
| 3 | EXCH | ⊢**A** / ⊢**B** / "where **B** is obtained by permuting the formulas of **A**" | yes (`Lit.exch`) | | nothing |
| 4 | ⊤ | none / ⊢⊤, **A** / "(axiom, **A** arbitrary) (no rule for **0**)" | yes | | nothing |
| 5 | & | ⊢A, **C** ; ⊢B, **C** / ⊢A & B, **C** (same **C**) | yes | | nothing |
| 6 | 1⊕ | ⊢A, **C** / ⊢A⊕B, **C** | yes | | nothing |
| 7 | 2⊕ | ⊢B, **C** / ⊢A⊕B, **C** | yes | | nothing |
| 8 | **1** | none / ⊢**1** / "(axiom)" | yes | | nothing |
| 9 | ⊥ | ⊢**A** / ⊢⊥, **A** | yes | | nothing |
| 10 | ⊗ | ⊢A, **C** ; ⊢B, **D** / ⊢A⊗B, **C**, **D** | yes (`Γ ++ Δ`, in that order) | | nothing |
| 11 | ⅋ | ⊢A, B, **C** / ⊢A ⅋ B, **C** | yes | | nothing |

On the formulas the second reader notes that negation does not reverse
the order of the two components ((A ⊗ B)^⊥ = A^⊥ ⅋ B^⊥): `Form.neg`
keeps the order.

Ambiguities that the second reader found and the plan had not listed,
each settled:

* *Bold against light is the only mark that separates a formula from a
  list* (and that light letters are formulas is not said): settled by
  use, as the second reader did (p. 23: "the unspecified lists of
  formulas **A**, **B**, **C**, etc."). The table's "Notation" says
  which letter is which. A divergence of kind U: D3.
* *Whether a context may be void* is said only at ⊤ ("**A**
  arbitrary") and, for a whole sequent, on p. 23 ("when the list is
  void"). Here every context may be empty: D4. The rule **1** needs it
  to be of any use with ⊗ (`Source.tensorUnit'` splits with an empty
  context).
* *EXCH allows any permutation in one step, the identity too*: so does
  `Lit.exch`, and the hypothesis of each rule of `Fam`.
* *CUT is printed with A on the left and A^⊥ on the right only, and
  A^⊥⊥ = A is stated for letters alone*: `Fam.cut` is as printed;
  `Form.neg_neg` proves A^⊥⊥ = A for every formula, so a cut with the
  premises the other way round is a cut on A^⊥.
* *"Provable" is not defined on these pages*: here, `Derivable Γ` is
  `Nonempty (Fam Γ)`.

The second reader also lists three misprints of pp. 23-24 that are
outside Definition 1.15 (in the proofs of 1.16 and 1.17); none touches
a rule.

Ambiguities the plan listed and the second reader did not: U1 (how
many letters) and U2 (the interpretation "in a completely
straightforward way": the reader was not asked about the semantics).

## Divergences

| # | kind | the source's item | what the source says | what is done here | why | date |
|---|---|---|---|---|---|---|
| D1 | R | Definition 1.15, p. 22 | sequents are sequences; EXCH is a rule; each rule is drawn with its principal formula first | in `Fam` and `CF` a sequent is a list read as a multiset: each rule concludes any permutation of the figure's conclusion, and EXCH is a function, not a constructor. `Lit` has the figure as it stands, and the two derive the same sequents | the source's own "variant without exchange, adapted to multisets" (p. 24); `decisions.md`, stage 0 | 2026-11-26 |
| D2 | R | the same | the conclusions `⊢ A, A^⊥` and `⊢ **B**, **C**` and `⊢ A ⊗ B, **C**, **D**` | in `Lit`, a variable with an equation (`B = Aᗮ`, `Ξ = Γ ++ Δ`) | no computed index in a conclusion (`#slime`) | 2026-11-26 |
| D3 | U | Definition 1.15 | which letters are formulas and which lists is shown only by typeface and use | as the "Notation" table says | settled by use; the two readers agree | 2026-11-26 |
| D4 | U | Definition 1.15; p. 23 | whether a context may be empty is said only for ⊤ and for the whole sequent | every context may be empty; the empty sequent is a sequent | the rule **1** and the reading of p. 23 need it | 2026-11-26 |
| D5 | U | p. 21 | "propositional letters a, b, c, …" | one letter for each natural number | U1 of the plan | 2026-11-26 |
| D6 | R | p. 21 | the connective is called *with* | the constructors are named `wth` | `with` is a keyword of Lean: a move named so cannot be typed after the tactic | 2026-11-26 |

## Errors of transcription

None found so far, by `#rules`, the terms of the family, the second
transcription or S2.

| what | found by | repaired in (commit) | what was built again |
|---|---|---|---|
