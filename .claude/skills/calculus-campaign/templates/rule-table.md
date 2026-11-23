# <CALCULUS>: the rule table

*Template. This page lies beside the source's figure when the reviewer
signs the transcription, and again at the reviewer's test. One row for
each rule of the figure, in the figure's order. Nothing is retyped from
memory: the "as printed" column is copied from the source, and the output
of `#rules` is pasted as Lean printed it, never paraphrased.*

Source: <paper>, <figure and page>, read from <which file>. Numbers are
those of <which version>.

The family: `<name>`, in `<file>`. The proof system (filled at step 5 of
Adopt, after the signature): `<name>`, in `<file>`.

Signed by the reviewer: <not yet / date; see `gates.md`>.

## Notation

| in the source | in Lean | note |
|---|---|---|
| | | |

## The rules

| # | rule, as the source names it | as printed: premises / conclusion / side condition, and where | the constructor | agrees with `#rules` below? | the move, and what `step` asks and leaves (filled after the signature) |
|---|---|---|---|---|---|
| 1 | | | | yes / no: see D<n> | |

The output of `#rules <family>`, pasted whole:

```
<paste>
```

An example of one row, to show the form only: a conjunction rule of a
two-sided sequent calculus, written for this template and taken from no
source. The figure below it is what `#rules` printed for a family of that
rule and one other (compiled; `⊢` and `⋏` are the family's notations).

| # | rule | as printed | the constructor | agrees? | the move; `step` |
|---|---|---|---|---|---|
| 1 | `∧R` | premises `Γ ⊢ A` and `Γ ⊢ B`; conclusion `Γ ⊢ A ∧ B`; no side condition. Fig. 2, p. 5 | `Fam.andR` | yes | `andR`; asks that the conclusion is a conjunction; leaves `Γ ⊢ A` and `Γ ⊢ B` |

```
Example.Fam — 2 rules
andR
    Fam (Γ ⊢ A)      Fam (Γ ⊢ B)
    ──────────────────────────────
    Fam (Γ ⊢ A ⋏ B)

andL
    Fam (A :: B :: Γ ⊢ C)
    ───────────────────────
    Fam (Γ ⊢ C)
    for  A : Form,  B : Form
    if   A ⋏ B ∈ Γ
```

## In the Lean and not in the figure

| what | why it is there |
|---|---|

## Side conditions from the prose

| condition | where in the source | which rules | how it is encoded |
|---|---|---|---|

## The checks

* `#rules <family>`: <n> rules printed; the figure has <n>.
* `#slime` on the two controls: <the output: the clean one passes, the
  other is reported>.
* `#slime <family>`: <the output; it must report no computed index>.

## Divergences

Recorded when made. Each cites the source's item, says what the source
states, what is done here, and why. Three kinds:

* **W**: the source is wrong or says too much;
* **U**: the source is under-specified, and the choice was ours;
* **R**: a choice of representation where the source is clear (a list for
  a multiset, an equation for a computed index).

| # | kind | the source's item | what the source says | what is done here | why | date |
|---|---|---|---|---|---|---|
| D1 | | | | | | |

## Errors of transcription

Each, with when it was found: at the rule table, at the reviewer's test,
or after it. After a repair the table is signed again.

| what | found when | repaired in (commit) | signed again |
|---|---|---|---|
