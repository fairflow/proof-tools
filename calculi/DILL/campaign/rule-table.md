# DILL: the rule table

This page lies beside the source's figure. One row for each rule of the
figure, in the figure's order. The "as printed" column is copied from the
page; the output of `#rules` is pasted as Lean printed it.

Source: Chang, Chaudhuri, Pfenning, *A judgmental analysis of linear
logic*, CMU-CS-03-131R (revised 29 December 2003), cited as CCP: Figure 2,
printed p. 12, and Principle 7, p. 11; read from `ccp03.pdf`, the pages as
images. Numbers are those of that report.

The family: `DILL.Fam`, in `DILL/System.lean`. The proof system:
`DILL.S`, in `DILL/Proof.lean`.

Checked: the source's worked derivations as terms (`DILL/Source.lean`;
the count is on the status board); the second transcription, run
2026-11-26 15:15 to 15:19 GMT, no difference (below). A second table at
the end has the one-zone calculus `DILL.ILL`, from another source.

## Notation

| in the source | in Lean | note |
|---|---|---|
| `Γ ; Δ ⟹ C ; ·` | `Γ ⨾ Δ ⟹ C`, which is `Seq.mk Γ Δ C` | Lean's `;` separates tactics and cannot also separate the zones (divergence R4). The `; ·` on the right, an empty zone of possibility, is not written: the fragment has no other right-hand side |
| `γ` | `C` | in the fragment `γ` is always `C ; ·` |
| `Γ` (valid hypotheses) | `Γ : List Form`, read through membership | R2 |
| `Δ`, `Δ′` (linear hypotheses) | `Δ Δ' : List Form`, read as multisets | R1 |
| (no letter) | `Ξ` | the linear zone of a conclusion, a variable; not in the figure |
| `·` (an empty zone) | `[]` | |
| `Γ, A` in a premise | `A :: Γ` | |
| `Γ, A` in the conclusion of copy | `A ∈ Γ` | R2 |
| `Δ, A` | `A :: Δ` | |
| `Δ, Δ′` | `Δ ++ Δ'` | |
| **1**, **0** | `𝟏`, `𝟎` | |
| `!A` | `!A`, written `(!A)` where anything follows | core Lean's `!` is Boolean negation and takes what follows |
| `A ⊕ B` | `A ⊕ B`, written `(A ⊕ B)` before `::` and `∈` | core Lean's `⊕` is the sum of types |
| (no letter) | `c : Bool` | `Fam true` has the two cuts, `Fam false` (`CF`) is the figure |
| `~` | `List.Perm` | not in the figure |

## The rules

Every row agrees with `#rules` below, read through this notation: where
the figure's conclusion has a linear zone other than a bare `Δ`, the
constructor concludes `Ξ` and has the figure's zone as the side condition
`Ξ ~ …`.

| # | rule | as printed: premises / conclusion, Figure 2, p. 12 | the constructor | agrees? | the move; what `step` asks; what it leaves |
|---|---|---|---|---|---|
| 1 | init | none / `Γ ; A ⟹ A ; ·` | `init` | yes | `init`; the linear zone is exactly the conclusion; nothing |
| 2 | copy | `Γ, A ; Δ, A ⟹ γ` / `Γ, A ; Δ ⟹ γ` | `copy` | yes (R2) | `copy A`; `A` is in the unrestricted zone; `Γ ; A, Δ ⟹ C` |
| 3 | ⊗L | `Γ ; Δ, A, B ⟹ γ` / `Γ ; Δ, A ⊗ B ⟹ γ` | `tensorL` | yes | `tensorL A B`; `A ⊗ B` is in the linear zone; `A, B` and the rest |
| 4 | ⊗R | `Γ ; Δ ⟹ A ; ·` and `Γ ; Δ′ ⟹ B ; ·` / `Γ ; Δ, Δ′ ⟹ A ⊗ B ; ·` | `tensorR` | yes | `tensorR A B Δ`; the conclusion is `A ⊗ B` and `Δ` is part of the linear zone; `Γ ; Δ ⟹ A` and `Γ ; rest ⟹ B` |
| 5 | **1**L | `Γ ; Δ ⟹ γ` / `Γ ; Δ, 1 ⟹ γ` | `oneL` | yes | `oneL`; `1` is in the linear zone; the rest |
| 6 | **1**R | none / `Γ ; · ⟹ 1 ; ·` | `oneR` | yes | `oneR`; the conclusion is `1` and the linear zone is empty; nothing |
| 7 | ⊸L | `Γ ; Δ ⟹ A ; ·` and `Γ ; Δ′, B ⟹ γ` / `Γ ; Δ, Δ′, A ⊸ B ⟹ γ` | `lolliL` | yes | `lolliL A B Δ`; `A ⊸ B` is in the linear zone and `Δ` is part of the rest; `Γ ; Δ ⟹ A` and `Γ ; B, rest ⟹ C` |
| 8 | ⊸R | `Γ ; Δ, A ⟹ B ; ·` / `Γ ; Δ ⟹ A ⊸ B ; ·` | `lolliR` | yes | `lolliR A B`; the conclusion is `A ⊸ B`; `Γ ; A, Δ ⟹ B` |
| 9 | &L₁ | `Γ ; Δ, A ⟹ γ` / `Γ ; Δ, A & B ⟹ γ` | `withL₁` | yes | `withL₁ A B`; `A & B` is in the linear zone; `A` and the rest |
| 10 | &L₂ | `Γ ; Δ, B ⟹ γ` / `Γ ; Δ, A & B ⟹ γ` | `withL₂` | yes | `withL₂ A B`; the same; `B` and the rest |
| 11 | &R | `Γ ; Δ ⟹ A ; ·` and `Γ ; Δ ⟹ B ; ·` / `Γ ; Δ ⟹ A & B ; ·` | `withR` | yes | `withR A B`; the conclusion is `A & B`; the two premises, same zones |
| 12 | ⊤R | none / `Γ ; Δ ⟹ ⊤ ; ·` | `topR` | yes | `topR`; the conclusion is `⊤`; nothing |
| 13 | **0**L | none / `Γ ; Δ, 0 ⟹ γ` | `zeroL` | yes | `zeroL`; `0` is in the linear zone; nothing |
| 14 | ⊕L | `Γ ; Δ, A ⟹ γ` and `Γ ; Δ, B ⟹ γ` / `Γ ; Δ, A ⊕ B ⟹ γ` | `plusL` | yes | `plusL A B`; `A ⊕ B` is in the linear zone; `A` and the rest, `B` and the rest |
| 15 | ⊕R₁ | `Γ ; Δ ⟹ A ; ·` / printed `Γ ; Δ ⟹ A & B ; ·` | `plusR₁`, with `A ⊕ B` | no: W1 | `plusR₁ A B`; the conclusion is `A ⊕ B`; `Γ ; Δ ⟹ A` |
| 16 | ⊕R₂ | `Γ ; Δ ⟹ B ; ·` / printed `Γ ; Δ ⟹ A & B ; ·` | `plusR₂`, with `A ⊕ B` | no: W1 | `plusR₂ A B`; the conclusion is `A ⊕ B`; `Γ ; Δ ⟹ B` |
| 17 | !L | `Γ, A ; Δ ⟹ γ` / `Γ ; Δ, !A ⟹ γ` | `bangL` | yes | `bangL A`; `!A` is in the linear zone; `A, Γ ; rest ⟹ C` |
| 18 | !R | `Γ ; · ⟹ A ; ·` / `Γ ; · ⟹ !A ; ·` | `bangR` | yes | `bangR A`; the conclusion is `!A` and the linear zone is empty; `Γ ; · ⟹ A` |

Left out of the figure (the first entry of `decisions.md`): `promote`,
`?L`, `?R`.

## In the Lean and not in the figure

| constructor | what it is | where in the source |
|---|---|---|
| `cut` (only in `Fam true`) | from `Γ ; Δ ⟹ A` and `Γ ; Δ′, A ⟹ γ` to `Γ ; Δ, Δ′ ⟹ γ` | CCP Principle 7, item 2, p. 11: a principle that Theorem 3 shows admissible, here a rule of the calculus with cut (Pfenning's notes, p. 56, have it as the rule "cut") |
| `cutU` (only in `Fam true`) | from `Γ ; · ⟹ A` and `Γ, A ; Δ′ ⟹ γ` to `Γ ; Δ′ ⟹ γ` | CCP Principle 7, item 1 (Pfenning: "cut!") |

Moves: `cut A Δ` (asks that `Δ` is part of the linear zone; leaves
`Γ ; Δ ⟹ A` and `Γ ; A, rest ⟹ C`) and `cutU A` (always applies; leaves
`Γ ; · ⟹ A` and `A, Γ ; Δ ⟹ C`).

Functions, not rules: `Fam.exch` (exchange in the linear zone),
`Fam.mono` (the unrestricted zone replaced by any list with its members:
weakening, contraction and exchange of `Γ`, CCP Theorem 2).

## The divergence log

| | kind | what | recorded |
|---|---|---|---|
| W1 | the source is wrong | Figure 2 prints the conclusions of ⊕R₁ and ⊕R₂ with `A & B`. The rules are ⊕'s: their names; their place under ⊕L; as printed ⊕ would have no right rule and `A ⟹ A & B` would be derivable; Pfenning's notes (p. 47) print `A ⊕ B`. Transcribed with `A ⊕ B` | 14:59, the plan, Q1; found again by the cold reader, unprompted |
| U1 | under-specified | whether `Γ` is a list, a multiset or a set: p. 11 says "valid context", and contraction is stated with `Γ, A, A`. Decided: a list read through membership | 14:59 |
| U2 | under-specified | init for every formula or for atoms: the figure has the general `A` ("the following most general form", p. 11). Transcribed for every formula | 14:59 |
| U3 | under-specified | the supply of atomic propositions. Decided: one for each natural number | 14:59 |
| U4 | under-specified | whether a zone may be empty where the figure does not write `·`. Decided: yes, every `Γ`, `Δ`, `Δ′` may be empty | 15:20, from the cold reader's list (A3) |
| R1 | representation | the linear zone is a list; a rule that takes from it concludes a variable `Ξ` with `Ξ ~ …`. The source's exchange ("allow free exchange among the linear hypotheses", p. 2) is the function `Fam.exch` | 14:59 |
| R2 | representation | the unrestricted zone is a list read through membership: `A ∈ Γ` for the figure's `Γ, A` in the conclusion of copy. Weakening and contraction of `Γ` (Theorem 2) are the function `Fam.mono` | 14:59 |
| R3 | representation | one family with `c : Bool` for the calculus with the cuts and without | 14:59 |
| R4 | representation | `⨾` for the `;` between the zones (a first build with `;` failed in a file of tactics, 15:14); `(!A)` and `(A ⊕ B)` in parentheses where core Lean's signs would take over | 15:14 |
| R5 | representation | a move of a right rule names the conclusion's formula (`tensorR A B Δ`), though `step` could read it from the sequent: the soundness of the moves is then a definition without a case for each other shape of conclusion | 15:22 |

None changes what is derivable, given W1.

## The second transcription

Made 2026-11-26 15:15 to 15:19 GMT by a cold reader (an agent started
with four page images only: CCP pp. 11 and 12, KOT pp. 3 and 4; it was
told to open nothing else, and reports that it opened those and crops of
them). Its table, compared row by row with what `#rules` prints below:

* **System A** (this calculus): 18 rules of the figure and the two cuts,
  20 in both readings. Each premise, each conclusion and each side
  condition agrees: init with exactly `A` in the linear zone; copy with
  `A` kept in `Γ`; 1R and !R with an empty linear zone, !R's premise
  too; !L putting `A`, not `!A`, into `Γ`; the first premise of cut 7.1
  with an empty linear zone; `Γ` shared by the premises of every rule.
  **No difference.**
* The reader found the misprint W1 unprompted, with the same three
  reasons, and two more on the same pages that touch no rule: "the" for
  "then" in Theorem 2.2, and `F₁ :: Γ, Δ′ ; ⟹ γ` in the proof of
  Theorem 3 for `Γ ; Δ′ ⟹ γ`.
* Its list of what the pages leave open: lists, multisets or sets (U1);
  exchange not mentioned on pp. 11-12 (it is on p. 2, which the reader
  was not given: R1); empty zones (U4, entered from this list); init at
  every formula (U2); the cuts are principles, not rules of the figure
  (the table above says so); the fragment is not singled out by the
  source (the plan's Q2 says why it is closed).
* **System B** (one-zone ILL, the second table below): 20 rules in both
  readings, no difference.

Errors of transcription found: none.

## The output of `#rules DILL.Fam`, pasted whole

```
DILL.Fam — 20 rules
init
    ───────────────────
    Fam c (Γ ⨾ Ξ ⟹ A)
    for  A : Form
    if   Ξ ~ [A]

copy
    Fam c (Γ ⨾ A :: Ξ ⟹ C)
    ────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form
    if   A ∈ Γ

tensorL
    Fam c (Γ ⨾ A :: B :: Δ ⟹ C)
    ─────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  B : Form,  Δ : List Form
    if   Ξ ~ A ⊗ B :: Δ

tensorR
    Fam c (Γ ⨾ Δ ⟹ A)      Fam c (Γ ⨾ Δ' ⟹ B)
    ───────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ A ⊗ B)
    for  Δ : List Form,  Δ' : List Form
    if   Ξ ~ Δ ++ Δ'

oneL
    Fam c (Γ ⨾ Δ ⟹ C)
    ───────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  Δ : List Form
    if   Ξ ~ 𝟏 :: Δ

oneR
    ───────────────────
    Fam c (Γ ⨾ Ξ ⟹ 𝟏)
    if   Ξ ~ []

lolliL
    Fam c (Γ ⨾ Δ ⟹ A)      Fam c (Γ ⨾ B :: Δ' ⟹ C)
    ────────────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  B : Form,  Δ : List Form,  Δ' : List Form
    if   Ξ ~ A ⊸ B :: (Δ ++ Δ')

lolliR
    Fam c (Γ ⨾ A :: Ξ ⟹ B)
    ────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ A ⊸ B)

withL₁
    Fam c (Γ ⨾ A :: Δ ⟹ C)
    ────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  B : Form,  Δ : List Form
    if   Ξ ~ A & B :: Δ

withL₂
    Fam c (Γ ⨾ B :: Δ ⟹ C)
    ────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  B : Form,  Δ : List Form
    if   Ξ ~ A & B :: Δ

withR
    Fam c (Γ ⨾ Ξ ⟹ A)      Fam c (Γ ⨾ Ξ ⟹ B)
    ──────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ A & B)

topR
    ───────────────────
    Fam c (Γ ⨾ Ξ ⟹ ⊤)

zeroL
    ───────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  Δ : List Form
    if   Ξ ~ 𝟎 :: Δ

plusL
    Fam c (Γ ⨾ A :: Δ ⟹ C)      Fam c (Γ ⨾ B :: Δ ⟹ C)
    ────────────────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  B : Form,  Δ : List Form
    if   Ξ ~ A ⊕ B :: Δ

plusR₁
    Fam c (Γ ⨾ Ξ ⟹ A)
    ───────────────────────
    Fam c (Γ ⨾ Ξ ⟹ A ⊕ B)

plusR₂
    Fam c (Γ ⨾ Ξ ⟹ B)
    ───────────────────────
    Fam c (Γ ⨾ Ξ ⟹ A ⊕ B)

bangL
    Fam c (A :: Γ ⨾ Δ ⟹ C)
    ────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  Δ : List Form
    if   Ξ ~ !A :: Δ

bangR
    Fam c (Γ ⨾ [] ⟹ A)
    ────────────────────
    Fam c (Γ ⨾ Ξ ⟹ !A)
    if   Ξ ~ []

cut
    Fam c (Γ ⨾ Δ ⟹ A)      Fam c (Γ ⨾ A :: Δ' ⟹ C)
    ────────────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form,  Δ : List Form,  Δ' : List Form
    if   c = true
         Ξ ~ Δ ++ Δ'

cutU
    Fam c (Γ ⨾ [] ⟹ A)      Fam c (A :: Γ ⨾ Ξ ⟹ C)
    ────────────────────────────────────────────────
    Fam c (Γ ⨾ Ξ ⟹ C)
    for  A : Form
    if   c = true
```

`#slime`: the control family with `ms ++ ns` in a conclusion is flagged,
the clean control is not, and `DILL.Fam — 1 indices, 20 constructors, 0
carrying green slime`.

## The one-zone calculus `DILL.ILL`: a second table

Source: M. Kanovich, M. Okada, K. Terui, *Intuitionistic phase semantics
is almost classical*, author's final version (2006), cited as KOT:
Figure 1, p. 4, "Inference Rules of Intuitionistic Linear Logic (ILL)",
and Definition 2.1, p. 3; read from `kot06-iphase.pdf`, the pages as
images. Taken without the constant `⊥` (so without `⊥l` and `⊥r`), and
with exactly one formula on the right where the figure has at most one
(`Δ` with `|Δ| ≤ 1`): with `⊥` gone, the only sequents this removes are
those with an empty right-hand side, which no remaining rule leads out
of. The family: `DILL.ILL`, in `DILL/ILL.lean`; `ILL true` has Cut,
`ILL false` has not. A sequent `Γ ⊢ C` is `ILL c Γ C`, the left side a
list read as a multiset ("finite multisets of formulas", Definition
2.1), in the same form as the linear zone above.

| # | rule | as printed: premises / conclusion | the constructor | agrees? |
|---|---|---|---|---|
| 1 | Identity | none / `A ⊢ A` | `id` | yes |
| 2 | Cut | `Γ₁ ⊢ A` and `A, Γ₂ ⊢ Δ` / `Γ₁, Γ₂ ⊢ Δ` | `cut` (only in `ILL true`) | yes |
| 3 | ⊗l | `A, B, Γ ⊢ Δ` / `A ⊗ B, Γ ⊢ Δ` | `tensorL` | yes |
| 4 | ⊗r | `Γ₁ ⊢ A` and `Γ₂ ⊢ B` / `Γ₁, Γ₂ ⊢ A ⊗ B` | `tensorR` | yes |
| 5 | **1**l | `Γ ⊢ Δ` / `1, Γ ⊢ Δ` | `oneL` | yes |
| 6 | **1**r | none / `⊢ 1` | `oneR` | yes |
| 7 | ⊸l | `Γ₁ ⊢ A` and `B, Γ₂ ⊢ Δ` / `A ⊸ B, Γ₁, Γ₂ ⊢ Δ` | `lolliL` | yes |
| 8 | ⊸r | `A, Γ ⊢ B` / `Γ ⊢ A ⊸ B` | `lolliR` | yes |
| 9 | ⊕l | `A, Γ ⊢ Δ` and `B, Γ ⊢ Δ` / `A ⊕ B, Γ ⊢ Δ` | `plusL` | yes |
| 10 | ⊕r₁ | `Γ ⊢ A` / `Γ ⊢ A ⊕ B` | `plusR₁` | yes |
| 11 | ⊕r₂ | `Γ ⊢ B` / `Γ ⊢ A ⊕ B` | `plusR₂` | yes |
| 12 | **0**l | none / `0, Γ ⊢ Δ` | `zeroL` | yes |
| 13 | &l₁ | `A, Γ ⊢ Δ` / `A & B, Γ ⊢ Δ` | `withL₁` | yes |
| 14 | &l₂ | `B, Γ ⊢ Δ` / `A & B, Γ ⊢ Δ` | `withL₂` | yes |
| 15 | &r | `Γ ⊢ A` and `Γ ⊢ B` / `Γ ⊢ A & B` | `withR` | yes |
| 16 | ⊤r | none / `Γ ⊢ ⊤` | `topR` | yes |
| 17 | !D | `A, Γ ⊢ Δ` / `!A, Γ ⊢ Δ` | `bangD` | yes |
| 18 | !C | `!A, !A, Γ ⊢ Δ` / `!A, Γ ⊢ Δ` | `bangC` | yes |
| 19 | !W | `Γ ⊢ Δ` / `!A, Γ ⊢ Δ` | `bangW` | yes |
| 20 | !r | `!Γ ⊢ A` / `!Γ ⊢ !A`; "Here `!Γ` stands for a multisets of formulas of the form `!A₁, …, !Aₙ`" | `bangR`, with `Γ.map Form.bang` for `!Γ` | yes |

Divergences: R (the left side a list under a permutation hypothesis; one
family with `c`; `!Γ` as `Γ.map Form.bang`, which may be empty); U (the
source does not define the system without `⊥`: it says only that `⊥`
"can be replaced with an arbitrary but fixed propositional variable",
p. 3). CCP's own `ILL` (p. 19: the sequents of its Figure 3 with one
formula on the right) has the same four rules for `!`, named !L, weak!,
contr!, !R; its Theorem 7 is stated of that calculus.

The output of `#rules DILL.ILL`, pasted whole:

```
DILL.ILL — 20 rules
id
    ───────────
    ILL c Ξ A
    for  A : Form
    if   Ξ ~ [A]

cut
    ILL c Γ₁ A      ILL c (A :: Γ₂) C
    ───────────────────────────────────
    ILL c Ξ C
    for  A : Form,  Γ₁ : List Form,  Γ₂ : List Form
    if   c = true
         Ξ ~ Γ₁ ++ Γ₂

tensorL
    ILL c (A :: B :: Γ) C
    ───────────────────────
    ILL c Ξ C
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊗ B :: Γ

tensorR
    ILL c Γ₁ A      ILL c Γ₂ B
    ────────────────────────────
    ILL c Ξ (A ⊗ B)
    for  Γ₁ : List Form,  Γ₂ : List Form
    if   Ξ ~ Γ₁ ++ Γ₂

oneL
    ILL c Γ C
    ───────────
    ILL c Ξ C
    for  Γ : List Form
    if   Ξ ~ 𝟏 :: Γ

oneR
    ───────────
    ILL c Ξ 𝟏
    if   Ξ ~ []

lolliL
    ILL c Γ₁ A      ILL c (B :: Γ₂) C
    ───────────────────────────────────
    ILL c Ξ C
    for  A : Form,  B : Form,  Γ₁ : List Form,  Γ₂ : List Form
    if   Ξ ~ A ⊸ B :: (Γ₁ ++ Γ₂)

lolliR
    ILL c (A :: Ξ) B
    ──────────────────
    ILL c Ξ (A ⊸ B)

plusL
    ILL c (A :: Γ) C      ILL c (B :: Γ) C
    ────────────────────────────────────────
    ILL c Ξ C
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A ⊕ B :: Γ

plusR₁
    ILL c Ξ A
    ─────────────────
    ILL c Ξ (A ⊕ B)

plusR₂
    ILL c Ξ B
    ─────────────────
    ILL c Ξ (A ⊕ B)

zeroL
    ───────────
    ILL c Ξ C
    for  Γ : List Form
    if   Ξ ~ 𝟎 :: Γ

withL₁
    ILL c (A :: Γ) C
    ──────────────────
    ILL c Ξ C
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A & B :: Γ

withL₂
    ILL c (B :: Γ) C
    ──────────────────
    ILL c Ξ C
    for  A : Form,  B : Form,  Γ : List Form
    if   Ξ ~ A & B :: Γ

withR
    ILL c Ξ A      ILL c Ξ B
    ──────────────────────────
    ILL c Ξ (A & B)

topR
    ───────────
    ILL c Ξ ⊤

bangD
    ILL c (A :: Γ) C
    ──────────────────
    ILL c Ξ C
    for  A : Form,  Γ : List Form
    if   Ξ ~ !A :: Γ

bangC
    ILL c (!A :: !A :: Γ) C
    ─────────────────────────
    ILL c Ξ C
    for  A : Form,  Γ : List Form
    if   Ξ ~ !A :: Γ

bangW
    ILL c Γ C
    ───────────
    ILL c Ξ C
    for  A : Form,  Γ : List Form
    if   Ξ ~ !A :: Γ

bangR
    ILL c (map Form.bang Γ) A
    ───────────────────────────
    ILL c Ξ !A
    for  Γ : List Form
    if   Ξ ~ map Form.bang Γ
```

`#slime DILL.ILL`: 2 indices, 20 constructors, 0 carrying green slime.
