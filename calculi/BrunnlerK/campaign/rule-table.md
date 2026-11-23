# Brünnler's system K: the rule table

This page lies beside the source's Figure 2.3 when the reviewer signs the
transcription, and again at the reviewer's test. The "as printed" column
is copied from the source; the output of `#rules` is pasted as Lean
printed it.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1. System K:
Figure 2.3 (label `fig:kx`, p. 10). Cut: Figure 2.4 (label
`fig:admissible`, p. 10). System K°: the display and the paragraph after
Definition 2.13, p. 14 (no figure, no label). Read from the TeX source of
v1 (`main.tex`), with the prose of pp. 6–10 and 14–15. Numbers and pages
are those of v1.

The families: `BrunnlerK.Fam` in `BrunnlerK/System.lean` (system K at
`Fam false`, K + cut at `Fam true`), and `BrunnlerK.FamO` in
`BrunnlerK/SystemO.lean` (system K°). The proof system: not written; it
is step 5 of Adopt, after the signature.

Signed by the reviewer: not yet.

Written 2026-11-23 14:16 GMT.

## How a rule of the figure reads in Lean

The source states each rule for a context `Γ{ }`, a sequent with a hole.
A rule

        Γ{X′}
      ─────────
        Γ{X}

is in Lean a constructor with conclusion `Fam c Γ`, where `Γ` is a
variable, and with:

* a path `a`: the place of the hole, as the positions of the boxes
  entered from the root (`[]` is the root, `[1, 0]` is box 0 of box 1);
* the side condition `Γ.node? a = some Θ`: the sequent at that place is
  `Θ`. `Θ` is **all** of the sequent at that node: the `X` of the figure
  together with whatever else the context has there;
* a side condition that says `X` is there: `A ⋏ B ∈ Θ.forms`, at any
  position among the formulas of `Θ`;
* the premise `Fam c (Γ.setNode a Θ′)`: `Γ` with the sequent at `a`
  replaced by `Θ′`, which is `Θ` with `X` changed to `X′`.

The letters `Γ`, `Δ`, `A`, `B`, `p` in the constructors are the
figure's. `Θ`, `a` and `i` are not in the figure.

## Notation

| in the source | in Lean | note |
|---|---|---|
| a proposition `p` | `Form.atom n` | a proposition is a natural number (D14) |
| `p̄` | `Form.natom n` | `∼(Form.atom n)` reduces to it |
| `A ∨ B`, `A ∧ B` | `A ⋎ B`, `A ⋏ B` | `∨` and `∧` are Lean's own, for propositions. Left-associative, as the source says (p. 6). That `⋏` binds tighter than `⋎` is ours (D9) |
| `◇A`, `□A` | `◇A`, `□A` | |
| `Ā`, the negation of a formula | `∼A`, that is `Form.dual A` | a function, by the De Morgan laws; the modal clauses are ours (D5) |
| `A ⊃ B` | `A ⊃ B`, that is `Form.imp A B` | defined as `∼A ⋎ B`, as the source defines it |
| `⊥`, `⊤` | not defined | D7 |
| the sequent `A₁, …, Aₘ, [Δ₁], …, [Δₙ]` | `NSeq`: `cons Δ₁ (cons Δ₂ (… (cons Δₙ (leaf [A₁, …, Aₘ]))))` | lists for the two multisets (D1) |
| the empty sequent `∅` | `NSeq.leaf []` | |
| `Γ`, `Δ`, `Λ` (sequents) | `Γ`, `Δ`, `Λ` | |
| `Π`, `Σ` (sequents) | `Υ`, `Ξ` | Lean reserves `Π` and `Σ`. Neither occurs in Figure 2.3 or 2.4, nor in the two families; the proof of Lemma 2.4 uses `Σ`. Further sequents: `Θ`, `Φ` |
| "`A` is in `Γ`" (Definition 2.12) | `A ∈ Γ.forms` | |
| the immediate subtrees of `Γ` (Definition 2.12) | `Γ.boxes` | |
| a unary context `Γ{ }` | a sequent `Γ` and a path `a : Path` (`List Nat`) | D2 |
| `depth(Γ{ })` | `a.length` | |
| the node at the hole | `Θ`, with `Γ.node? a = some Θ` | |
| `Γ{…}` with the node changed | `Γ.setNode a Θ′` | |
| `Γ, A` | `Γ.add A` | the formula goes in front (D3) |
| `Γ` less one `A` | `Γ.erase A` | the first `A` (D3) |
| `Γ, [Δ]` | `Γ.addBox Δ` | the new box goes last (D3) |
| the box at position `i`; replacing it | `Θ.box? i`; `Θ.setBox i Δ′` | |
| the set sequents of `Γ` and `Γ′` are equal (Definition 2.13) | `Γ.sameSet Γ′ = true` | D11 |
| `K ⊢ Γ` | `Nonempty (K Γ)`, with `K := Fam false` | the family is into `Type` |
| `K + cut ⊢ Γ` | `Nonempty (Kcut Γ)`, with `Kcut := Fam true` | D6 |
| `K° ⊢ Γ` | `Nonempty (FamO Γ)` | |

## The rules of system K, and cut

| # | rule, as the source names it | as printed: premises / conclusion / side condition, and where | the constructor | agrees with `#rules` below? | the move, and what `step` asks and leaves (filled after the signature) |
|---|---|---|---|---|---|
| 1 | the axiom | no premise; `Γ{p, p̄}`; no side condition. Figure 2.3, p. 10. "A proof … is a derivation … where all premises are instances of the axiom `Γ{p, p̄}`", p. 9 | `Fam.ax` | yes, read with D2, D4: `p` and `p̄` are asked for by membership in the node | |
| 2 | `∧` | premises `Γ{A}` and `Γ{B}`; conclusion `Γ{A ∧ B}`; no side condition. Figure 2.3 | `Fam.and` | yes, read with D2, D3: one `A ∧ B` is taken out of the node and `A` (or `B`) put in front | |
| 3 | `∨` | premise `Γ{A, B}`; conclusion `Γ{A ∨ B}`; none. Figure 2.3 | `Fam.or` | yes, read with D2, D3: the node then begins `A, B` | |
| 4 | `□` | premise `Γ{[A]}`; conclusion `Γ{□A}`; none. Figure 2.3 | `Fam.box` | yes, read with D2, D3: one `□A` is taken out and the box `[A]` put after the node's boxes | |
| 5 | `◇k_c` (printed with a dot over `k`: the rule for the axiom k, with contraction built in) | premise `Γ{◇A, [Δ, A]}`; conclusion `Γ{◇A, [Δ]}`; none. Figure 2.3 | `Fam.dia` | yes, read with D2, D3: `◇A` is in the node and stays; the box at position `i` is `[Δ]`, and `A` is put in front of `Δ` | |
| | `◇d_c`, `◇t_c`, `◇b_c`, `◇4_c`, `◇5_c` | Figure 2.3 | none | left out at the target's gate: the system is K alone | |
| 6 | `cut` | premises `Γ{A}` and `Γ{Ā}`; conclusion `Γ{∅}`; none. Figure 2.4, p. 10 | `Fam.cut` | yes, read with D2, D3, D6: allowed only where `c = true`; `A` (or `Ā`) is put in front of the node | |
| | `nec`, `wk`, `ctr` | Figure 2.4 | none | not rules of K: the source shows them admissible (Lemma 2.4, `l:stradm`). They are goal 3 | |

The output of `#rules BrunnlerK.Fam`, pasted whole:

```
BrunnlerK.Fam — 6 rules
ax
    ─────────
    Fam c Γ
    for  a : Path,  p : Nat
    if   Γ.node? a = some Θ
         Form.atom p ∈ Θ.forms
         Form.natom p ∈ Θ.forms

and
    Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add A))      Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add B))
    ──────────────────────────────────────────────────────────────────────────────────────────────────
    Fam c Γ
    for  a : Path,  A : Form,  B : Form
    if   Γ.node? a = some Θ
         A ⋏ B ∈ Θ.forms

or
    Fam c (Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A))
    ───────────────────────────────────────────────────────
    Fam c Γ
    for  a : Path,  A : Form,  B : Form
    if   Γ.node? a = some Θ
         A ⋎ B ∈ Θ.forms

box
    Fam c (Γ.setNode a ((Θ.erase □A).addBox (NSeq.leaf [A])))
    ───────────────────────────────────────────────────────────
    Fam c Γ
    for  a : Path,  A : Form
    if   Γ.node? a = some Θ
         □A ∈ Θ.forms

dia
    Fam c (Γ.setNode a (Θ.setBox i (Δ.add A)))
    ────────────────────────────────────────────
    Fam c Γ
    for  a : Path,  i : Nat,  A : Form
    if   Γ.node? a = some Θ
         ◇A ∈ Θ.forms
         Θ.box? i = some Δ

cut
    Fam c (Γ.setNode a (Θ.add A))      Fam c (Γ.setNode a (Θ.add ∼A))
    ───────────────────────────────────────────────────────────────────
    Fam c Γ
    for  a : Path,  A : Form
    if   c = true
         Γ.node? a = some Θ
```

## The rules of system K°

"For each rule ρ we define a rule ρ° which keeps the main formula from
the conclusion. For most rules ρ = ρ° except for the following rules"
(p. 14). At `X = ∅` the system K° is `{∧°, ∨°, □°, ◇k_c°}`.

| # | rule | as printed, and where | the constructor | agrees with `#rules` below? |
|---|---|---|---|---|
| 7 | the axiom | as row 1. K° is a set of rules and a proof's leaves are instances of the axiom, in K° as in K | `FamO.ax` | yes, as row 1. No proviso (D12) |
| 8 | `∧°` | premises `Γ{A ∧ B, A}` and `Γ{A ∧ B, B}`; conclusion `Γ{A ∧ B}`. Display, p. 14 | `FamO.and` | yes, read with D2, D3: nothing is taken out; `A` (or `B`) is put in front of the node. The proviso: `hs₁`, `hs₂` |
| 9 | `∨°` | premise `Γ{A ∨ B, A, B}`; conclusion `Γ{A ∨ B}`. Display, p. 14 | `FamO.or` | yes. The proviso: `hs` |
| 10 | `□°` | premise `Γ{□A, [A]}`; conclusion `Γ{□A}`; "where in the conclusion the node of the active formula does not have a child node which contains `A`". Display, p. 14 | `FamO.box` | yes, read with D10: the side condition is the line `∀ (Δ : NSeq), Δ ∈ Θ.boxes → ¬A ∈ Δ.forms`. The proviso: `hs` |
| | `◇d_c°` | display, p. 14 | none | left out with `◇d_c` |
| 11 | `◇k_c°` | not displayed: "for most rules ρ = ρ°", so it is `◇k_c` of Figure 2.3, which keeps `◇A` already | `FamO.dia` | yes, as row 5. The proviso: `hs` |

The output of `#rules BrunnlerK.FamO`, pasted whole:

```
BrunnlerK.FamO — 5 rules
ax
    ────────
    FamO Γ
    for  a : Path,  p : Nat
    if   Γ.node? a = some Θ
         Form.atom p ∈ Θ.forms
         Form.natom p ∈ Θ.forms

and
    FamO (Γ.setNode a (Θ.add A))      FamO (Γ.setNode a (Θ.add B))
    ────────────────────────────────────────────────────────────────
    FamO Γ
    for  a : Path,  A : Form,  B : Form
    if   Γ.node? a = some Θ
         A ⋏ B ∈ Θ.forms
         (Γ.setNode a (Θ.add A)).sameSet Γ = false
         (Γ.setNode a (Θ.add B)).sameSet Γ = false

or
    FamO (Γ.setNode a ((Θ.add B).add A))
    ──────────────────────────────────────
    FamO Γ
    for  a : Path,  A : Form,  B : Form
    if   Γ.node? a = some Θ
         A ⋎ B ∈ Θ.forms
         (Γ.setNode a ((Θ.add B).add A)).sameSet Γ = false

box
    FamO (Γ.setNode a (Θ.addBox (NSeq.leaf [A])))
    ───────────────────────────────────────────────
    FamO Γ
    for  a : Path,  A : Form
    if   Γ.node? a = some Θ
         □A ∈ Θ.forms
         ∀ (Δ : NSeq), Δ ∈ Θ.boxes → ¬A ∈ Δ.forms
         (Γ.setNode a (Θ.addBox (NSeq.leaf [A]))).sameSet Γ = false

dia
    FamO (Γ.setNode a (Θ.setBox i (Δ.add A)))
    ───────────────────────────────────────────
    FamO Γ
    for  a : Path,  i : Nat,  A : Form
    if   Γ.node? a = some Θ
         ◇A ∈ Θ.forms
         Θ.box? i = some Δ
         (Γ.setNode a (Θ.setBox i (Δ.add A))).sameSet Γ = false
```

## The functions the rules use

`#rules` prints a definition by its name. These are the definitions, from
`BrunnlerK/Sequent.lean`; `Path` is `List Nat`.

```lean
def forms : NSeq → List Form
  | leaf fs => fs
  | cons _ r => r.forms

def boxes : NSeq → List NSeq
  | leaf _ => []
  | cons Δ r => Δ :: r.boxes

def add : NSeq → Form → NSeq
  | leaf fs, A => leaf (A :: fs)
  | cons Δ r, A => cons Δ (r.add A)

def erase : NSeq → Form → NSeq
  | leaf fs, A => leaf (fs.erase A)
  | cons Δ r, A => cons Δ (r.erase A)

def addBox : NSeq → NSeq → NSeq
  | leaf fs, Λ => cons Λ (leaf fs)
  | cons Δ r, Λ => cons Δ (r.addBox Λ)

def box? : NSeq → Nat → Option NSeq
  | leaf _, _ => none
  | cons Δ _, 0 => some Δ
  | cons _ r, i + 1 => r.box? i

def setBox : NSeq → Nat → NSeq → NSeq
  | leaf fs, _, _ => leaf fs
  | cons _ r, 0, Λ => cons Λ r
  | cons Δ r, i + 1, Λ => cons Δ (r.setBox i Λ)

def node? : NSeq → Path → Option NSeq
  | Γ, [] => some Γ
  | Γ, i :: a =>
    match Γ.box? i with
    | some Δ => Δ.node? a
    | none => none

def setNode : NSeq → Path → NSeq → NSeq
  | _, [], Θ => Θ
  | Γ, i :: a, Θ =>
    match Γ.box? i with
    | some Δ => Γ.setBox i (Δ.setNode a Θ)
    | none => Γ
```

And for the proviso of K°:

```lean
def sameForms (fs gs : List Form) : Bool :=
  fs.all (fun A => gs.contains A) && gs.all (fun A => fs.contains A)

def sameSet : NSeq → NSeq → Bool
  | leaf fs, Γ' => sameForms fs Γ'.forms && Γ'.boxes.isEmpty
  | cons Δ r, Γ' =>
    sameForms r.forms Γ'.forms
      && (Γ'.boxes.any (fun Δ' => sameSet Δ Δ') && boxesIn r Γ')
      && Γ'.boxes.all (fun Δ' => sameSet Δ Δ' || hasBox r Δ')

def boxesIn : NSeq → NSeq → Bool
  | leaf _, _ => true
  | cons Δ r, Γ' => Γ'.boxes.any (fun Δ' => sameSet Δ Δ') && boxesIn r Γ'

def hasBox : NSeq → NSeq → Bool
  | leaf _, _ => false
  | cons Δ r, Δ' => sameSet Δ Δ' || hasBox r Δ'
```

## In the Lean and not in the figure

| what | why it is there |
|---|---|
| the constructor `ax`, in both families | the source's axiom is not among its rules: a proof is a derivation whose leaves are instances of it. In a family a leaf is a constructor with no premise (D4) |
| the path `a`, the node `Θ` and the field `hΘ : Γ.node? a = some Θ`, in every constructor | they stand for the context `Γ{ }` (D2) |
| the position `i` and the field `hΔ : Θ.box? i = some Δ`, in `dia` | they say which box of the node is the figure's `[Δ]` (D2) |
| the parameter `c : Bool` of `Fam`, and the field `hc : c = true` of `cut` | one family for K and for K + cut (D6) |
| the membership fields (`hA`, `hp`, `hn`) | they say that the figure's main formula is in the node (D2) |

## Side conditions from the prose

| condition | where in the source | which rules | how it is encoded |
|---|---|---|---|
| none | pp. 6–10 | the rules of K, and cut | |
| "`depth(Γ{ }{∅}) > 0`" | Figure 2.3 | `◇5_c` | left out with the rule |
| "where in the conclusion the node of the active formula does not have a child node which contains `A`" | p. 14, beside the rule | `□°` | the field `hch : ∀ Δ ∈ Θ.boxes, A ∉ Δ.forms` (D10) |
| "each rule ρ° carries the proviso that for all of its premises the set sequent is different from the set sequent of the conclusion" | p. 14, the paragraph after the display | `∧°`, `∨°`, `□°`, `◇k_c°` | a field for each premise, `(premise).sameSet Γ = false` (D11) |

## The checks

* `#rules BrunnlerK.Fam`: 6 rules printed. Figure 2.3 has, for system K,
  the axiom and 4 rules; the sixth is `cut` of Figure 2.4.
* `#rules BrunnlerK.FamO`: 5 rules printed. The source has, at `X = ∅`,
  the axiom and 4 rules.
* The modules build (`lake build` in `calculi/BrunnlerK/`). The four
  theory files, `Form.lean`, `Sequent.lean`, `System.lean` and
  `SystemO.lean`, end with `#axioms_within_file [propext, Quot.sound]`,
  which holds.
* In `BrunnlerK/Test/Sequent.lean`: the example of p. 8 (the context
  `A, [[B], { }]` filled with `C, [D]`); each function above on a small
  sequent, by `#guard` and again by `decide +kernel`, so each reduces in
  the kernel; six cases of `sameSet`.
* In `BrunnlerK/Test/System.lean`: the source's Example 2.3 (p. 9)
  written with the constructors of `Fam false`, from its sequent and
  from its formula; one cut in `Fam true`; one proof in `FamO`, and the
  two provisos of K° each seen to fail once.

`#slime` on the two controls and on `Fam`: the clean control passes, the
other is reported, and `Fam` has no computed index.

```
BrunnlerK.CleanControl — 1 indices, 2 constructors, 0 carrying green slime

  clean: nil, cons
BrunnlerK/System.lean:86:0: warning: BrunnlerK.SlimedControl — 1 indices, 2 constructors, 1 carrying green slime

  app
    index 1  ms ++ ns
              ↳ computed by  HAppend.hAppend

  clean: nil
BrunnlerK.Fam — 1 indices, 6 constructors, 0 carrying green slime

  clean: ax, and, or, box, dia, cut
```

`#slime BrunnlerK.FamO`:

```
BrunnlerK.FamO — 1 indices, 5 constructors, 0 carrying green slime

  clean: ax, and, or, box, dia
```

Example 2.3 as the constructors build it, each sequent printed by
`NSeq.show` (formulas first, then boxes); beside it the source's line:

| the rule, upwards | here | in the source (p. 9) |
|---|---|---|
| | `◇(ā ∧ b̄) ∨ (□a ∨ ◇b)` | `◇(ā ∧ b̄) ∨ (□a ∨ ◇b)` |
| `∨` | `◇(ā ∧ b̄), □a ∨ ◇b` | (the source does `∨` twice in one step) |
| `∨` | `□a, ◇b, ◇(ā ∧ b̄)` | `◇(ā ∧ b̄), □a, ◇b` |
| `□` | `◇b, ◇(ā ∧ b̄), [a]` | `◇(ā ∧ b̄), [a], ◇b` |
| `◇k_c` | `◇b, ◇(ā ∧ b̄), [ā ∧ b̄, a]` | `◇(ā ∧ b̄), [a, ā ∧ b̄], ◇b` |
| `∧`, left | `◇b, ◇(ā ∧ b̄), [ā, a]` | `◇(ā ∧ b̄), [a, ā], ◇b` |
| `∧`, right | `◇b, ◇(ā ∧ b̄), [b̄, a]` | `◇(ā ∧ b̄), [a, b̄], ◇b` |
| `◇k_c` | `◇b, ◇(ā ∧ b̄), [b, b̄, a]` | `◇(ā ∧ b̄), [a, b̄, b], ◇b` |

The same multisets on every line; the order differs, by D3.

## Divergences

Recorded when made (all on 2026-11-23, at the transcription). **W**: the
source is wrong or says too much. **U**: the source is under-specified,
and the choice was ours. **R**: a choice of representation where the
source is clear.

| # | kind | the source's item | what the source says | what is done here | why |
|---|---|---|---|---|---|
| D1 | R | "Nested sequents", p. 6 | a sequent is a finite multiset of formulas and boxed sequents | `NSeq`: a list of formulas and, one at a time, the boxes. No exchange rule: every rule finds its formula, and `◇k_c` its box, at any position. That a permutation inside a node keeps provability is goal 4, OPEN | the plan's table of encodings, passed. A multiset as a quotient cannot be nested in a type of its own (the kernel refuses it) |
| D2 | R | "Sequent contexts, unary", pp. 7–8; every rule of Figures 2.3, 2.4 | a rule is stated for every context `Γ{ }`, and its conclusion is `Γ{…}` | the conclusion of every constructor is a variable `Γ`; the hole is a path `a`; the node there is `Θ`; the main formula is asked for by membership in `Θ.forms`; a premise is `Γ.setNode a …` | written as the figure has it, a conclusion would be a function applied to something, a computed index. The plan's table, passed; which functions, and membership, are chosen here |
| D3 | R | Figures 2.3, 2.4; p. 14 | the comma is multiset union: what a rule adds has no place | a formula added is put in front of the node's formulas (`add`); a formula removed is the first of its kind (`erase`); a new box is put after the node's boxes (`addBox`), so that the positions of the others, which paths use, do not change | with "erase, then put in front", a permutation of the node gives a permutation of the premise by a lemma of core Lean (`List.Perm.erase`), which is what goal 4 needs. The alternative, putting the new formula where the old one stood, reads closer to the source's example and costs a lemma of our own |
| D4 | U | pp. 8–9: "System K is the set of rules {∧, ∨, □, ◇k_c}"; a proof's premises "are instances of the axiom" | the axiom is not a rule | a constructor `ax` with no premise, in both families | a family has no other way to have leaves. Place 3 of the plan's Q1 |
| D5 | U | "Formulas", p. 6 | "its negation `Ā` is defined as usual using the De Morgan laws"; no clause is written | `Form.dual`: `p ↦ p̄`, `p̄ ↦ p`, `∨` and `∧` exchanged, and the dual of `□A` is `◇Ā`, of `◇A` is `□Ā` | as the cut rule and Definition 2.28 use it. Place 1 of Q1 |
| D6 | R | Figure 2.4; Theorem 2.35 | K and K + cut are two systems | one family with a Boolean parameter; `cut` asks `c = true` | the plan's table, passed |
| D7 | U | p. 6 | `⊥` and `⊤` are `p ∧ p̄` and `p ∨ p̄` "for some proposition `p`" | not defined | the choice of `p` is not made in the source; nothing in the rules uses them. The corresponding formula of the empty sequent is the one place that needs `⊥`: it is settled with the statement of `Valid`, at the gate of Prove. Place 8 of Q1 |
| D8 | U | p. 6; `◇k_c` with `Δ = ∅` | an empty box is not said to be something or nothing | `cons (leaf []) Γ` is `[∅], Γ`, and is not `Γ` | the rule `◇k_c` distinguishes them. Place 5 of Q1 |
| D9 | U | p. 6 | every mixed formula is bracketed | `⋏` binds tighter than `⋎`; the printer writes `∧`, `∨` and brackets accordingly | notation only |
| D10 | U | p. 14, the side condition of `□°` | "does not have a child node which contains `A`" | no box of the node has `A` among its own formulas (`A` is *in* the child, Definition 2.12; not *inside* it, at any depth) | a node of the corresponding tree is marked with a multiset of formulas, so a node contains formulas, not subtrees |
| D11 | R | Definition 2.13; the proviso of p. 14 | the set sequent is a set of formulas and boxed set sequents; the proviso compares two of them | a Boolean function `sameSet` on two sequents: the same set of formulas, and each box of either has the set sequent of some box of the other. No set sequent is built | sets of sequents would need an order or a quotient. The proviso is about the whole sequent, and cannot be replaced by a condition at the node: a test shows a node's own set changing while the sequent's set sequent stays |
| D12 | U | p. 14 | "each rule ρ° carries the proviso" | the axiom of K° has no proviso; `◇k_c°` is `◇k_c` with the proviso | the axiom is not a rule; "for most rules ρ = ρ°" |
| D13 | U | "Inference rules, derivations and proofs", p. 8 | "The depth of a derivation D is denoted by `\|D\|`", not defined | not in Lean yet: a function on derivations, proposed with a leaf at depth 0, shown at the gate of Prove | no rule depends on it. Place 6 of Q1 |
| D14 | R | p. 6 | propositions `p`, an unnamed set | natural numbers | equality must be decidable and reduce in the kernel |

**The eight places of the plan's Q1**, each with where it went: 1, the
dual: D5. 2, `Γ{A, Ā}` for every `A`: not a rule; goal 5 in
`statements.md`. 3, the axiom: D4. 4, multisets: D1, D3. 5, the empty
box: D8. 6, the depth of a derivation: D13. 7, the order of `prove`: not
in this stage; it is settled with the search, in Run. 8, `⊥` and `⊤`: D7.

## What the reviewer is asked to sign

The transcription, row by row, and these choices, which the plan left
open:

1. **How a rule names its place** (D2): a path, the whole node `Θ`, the
   main formula by membership, and the functions `node?`, `setNode`,
   `add`, `erase`, `addBox`, `box?`, `setBox` above.
2. **Where a rule puts what it adds** (D3): a formula in front, a box
   last; the formula removed is the first of its kind.
3. **The axiom by membership**: `p` and `p̄` anywhere in the node (row 1).
4. **K°** (rows 7 to 11): the side condition of `□°` as D10 reads it; the
   proviso as `sameSet`, a side condition, with no computed index (D11);
   no proviso on the axiom (D12).
5. **The divergences** D1 to D14.

## Errors of transcription

Each, with when it was found: at the rule table, at the reviewer's test,
or after it. After a repair the table is signed again.

| what | found when | repaired in (commit) | signed again |
|---|---|---|---|
| none found | | | |
