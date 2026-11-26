# DILL campaign: literature survey report

Started 2026-11-26 14:49 GMT. Status: IN PROGRESS (Q-A first source written; the rest follows).

Convention: every claim is marked **[read]** (read in the named file, at the page given;
pages are pages of the PDF file fetched, which for KOT06 coincide with the printed page
numbers) or **[memory]** (from memory, not checked). Formulas marked "rendered" were read
from a page image (`pdftoppm`), not from `pdftotext` output.

Source folder (scratch, outside the repository):
`/private/tmp/claude-501/-Users-matthew-Lean-Sources-proof-tools--claude-worktrees-epic-mayer-95e017/cf6b1d2e-c4cd-4e9f-bc77-342e4ded5a3a/scratchpad/src/`

---

## Q-A. Phase semantics for intuitionistic linear logic with `!`

### A.1 Primary source read: Kanovich, Okada, Terui 2006

M. I. Kanovich, M. Okada, K. Terui, "Intuitionistic Phase Semantics is Almost Classical",
author's final version for Math. Struct. in Comp. Science (received 23 September 2005),
file `kot06-iphase.pdf`, 19 pages. Section 2 "Preliminaries" recalls the semantics "in the
style of (Troelstra 1992)", with "the interpretation of exponentials (!, ?) ... due to
(Girard 1995)" (p. 3) **[read, rendered]**.

**Syntax (Definition 2.1, p. 3) [read, rendered].** Formulas of ILL: propositional
variables, the constants `1, ⊥, ⊤, 0`, and `A ⊗ B`, `A ⊸ B`, `A & B`, `A ⊕ B`, `!A`.
"Finite multisets of formulas are denoted by Greek capitals Γ, Δ, ... A sequent of ILL is
of the form Γ ⊢ Δ with |Δ| ≤ 1." So the source's ILL has the constant `⊥` and allows an
empty succedent; the campaign's fragment (no `⊥`, exactly one conclusion) is the
sub-system without `⊥l`, `⊥r`. The source remarks (p. 3) that `⊥` "is not strictly
necessary ... since it can be replaced with an arbitrary but fixed propositional variable".

**One-zone sequent calculus (Figure 1, p. 4) [read, rendered].** "Inference Rules of
Intuitionistic Linear Logic (ILL)": Identity `A ⊢ A` (on arbitrary formulas), Cut,
`⊗l ⊗r 1l 1r ⊸l ⊸r ⊥l ⊥r ⊕l ⊕r₁ ⊕r₂ 0l &l₁ &l₂ &r ⊤r`, and the exponential rules

```
 A, Γ ⊢ Δ          !A, !A, Γ ⊢ Δ         Γ ⊢ Δ           !Γ ⊢ A
----------- !D     -------------- !C    ----------- !W   --------- !r
!A, Γ ⊢ Δ           !A, Γ ⊢ Δ           !A, Γ ⊢ Δ        !Γ ⊢ !A
```

"Here !Γ stands for a multisets of formulas of the form !A₁, ..., !Aₙ." (This figure also
answers the Q-E request for a public one-zone ILL calculus with explicit `!` rules.)

**Intuitionistic phase space (Definition 2.2, p. 3) [read, rendered].** For a commutative
monoid `(M, ·, ε)` and `X, Y ⊆ M`, `X · Y := {x·y | x ∈ X, y ∈ Y}`.

> An *intuitionistic phase space* `(M, ·, ε, Cl)` consists of a commutative monoid
> `(M, ·, ε)` and a *closure operator* `Cl`, that is a mapping from the subsets of `M` to
> themselves such that for all `X, Y ⊆ M`:
>
> (Cl1) `X ⊆ Cl(X)`,
> (Cl2) `Cl(Cl(X)) ⊆ Cl(X)`,
> (Cl3) `X ⊆ Y ⟹ Cl(X) ⊆ Cl(Y)`,
> (Cl4) `Cl(X) · Cl(Y) ⊆ Cl(X · Y)`.
>
> A set `X ⊆ M` is said to be *closed* if `X = Cl(X)`. The set of all closed sets in `𝓜`
> is denoted by `𝒞(𝓜)`.

Remark 2.3 (p. 4): "under our considerations `Cl(∅)` is generally non-empty" **[read]**.

**Interpretation of the connectives (Definition 2.4, p. 4) [read, rendered].**

```
X ⊗ Y := Cl(X · Y)            1 := Cl({ε})
X & Y := X ∩ Y                ⊤ := M
X ⊕ Y := Cl(X ∪ Y)            0 := Cl(∅)
X ⊸ Y := {z ∈ M | ∀x ∈ X (x·z ∈ Y)}
   !X := Cl(X ∩ I),   where I := {x ∈ 1 | x·x = x}.
```

So the clause for `!` uses the **strict idempotents lying in `1 = Cl({ε})`**: no chosen
submonoid `K`/`J`, no weak idempotents. "These operations are defined exactly in the same
way as in classical phase semantics. Notice that we do not introduce an operation (a set)
associated to ⊥; it will be treated through a valuation operator." (p. 4)

**Model and validity (Definition 2.6, p. 5) [read, rendered].**

> An *intuitionistic phase model* `(M, ·, ε, Cl, v)` is an intuitionistic phase space
> `(M, ·, ε, Cl)` with a valuation `v` that maps each propositional variable to a closed
> subset of `M`, and, in addition, assigns a closed subset of `M` to constant ⊥.
> The valuation `v` is naturally extended to all formulas of ILL using the operations in
> Definition 2.4. A formula `A` is *satisfied* in model `(M, ·, ε, Cl, v)` if and only if
> `ε ∈ v(A)`.

Validity is stated **for formulas only**; this paper gives no clause for a sequent. (The
usual reading, `Γ ⊢ C` valid iff `v(A₁) · … · v(Aₙ) ⊆ v(C)`, equivalently
`ε ∈ v(A₁ ⊗ … ⊗ Aₙ ⊸ C)`, is **[memory]** as far as this file goes; see A.2 below for
sources that state it.)

**Co-basis (Definition 2.7 and Theorem 2.8, p. 5) [read, rendered].** A family
`{G_α}` of closed sets is a *co-basis* if `Cl(X) = ⋂ {G_α | X ⊆ G_α}` for all `X`.

> Theorem 2.8. Let `(M, ·, ε)` be a commutative monoid and `{G_α}_{α∈𝒜}` be a family of
> subsets of `M`. Suppose that for every `G_α` and `y ∈ M`, `{y} ⊸ G_α` is also a member
> of the family. Then operator `Cl` defined by `Cl(X) := ⋂_{α ∈ 𝒜, X ⊆ G_α} G_α`
> satisfies (Cl1)–(Cl4) to be a closure operator on `M`.

The proof (pp. 5–6) goes through (Cl4') `X · Cl(Y) ⊆ Cl(X · Y)`. This theorem is the
practical way to build the syntactic model: one only has to exhibit a family of sets
closed under `{y} ⊸ –`.

**Soundness and completeness (Theorem 2.9, p. 6) [read, rendered].**

> Theorem 2.9 (cf. (Abrusci 1990; Troelstra 1992)). For any formula `A`, `A` is provable
> in ILL if and only if `A` is satisfied in every intuitionistic phase model.
> Moreover, this statement can be strengthened as follows; `A` is provable in ILL if and
> only if `A` is satisfied in every intuitionistic phase model that has a countable
> co-basis.

Soundness is not proved in this paper (it is the "only if" half of 2.9, attributed to
Abrusci 1990 and Troelstra 1992); only completeness is outlined.

**The syntactic model and how it handles `!` (Proof outline of 2.9, p. 6) [read, rendered].**

> We define the *canonical model* `(M₀, ·, ε, Cl₀, v₀)` for ILL as follows;
> — `M₀` consists of finite multisets Γ of ILL formulas. Here we ignore the multiplicity
>   of formulas of the form `!B`; for instance we identify `!B, !B, !C, Σ` with
>   `!B, !C, !C, Σ`.
> — `Γ · Δ = Γ, Δ`.
> — `ε = ∅` (the empty multiset).
> — `⟦Γ ⊢ Ξ⟧ = {Δ | Δ, Γ ⊢ Ξ is provable in ILL}`.
>
> Let `𝒢` be `{⟦Γ ⊢ Ξ⟧ | Γ ⊢ Ξ is a sequent of ILL}`. By definition `𝒢` is countable.
> Furthermore, for every `⟦Γ ⊢ Ξ⟧ ∈ 𝒢` and `Δ ∈ M₀`, `{Δ} ⊸ ⟦Γ ⊢ Ξ⟧ = ⟦Δ, Γ ⊢ Ξ⟧ ∈ 𝒢`.
> Therefore, by Theorem 2.8, it induces a closure operator `Cl₀` defined by
> `Cl₀(X) := ⋂_{X ⊆ ⟦Γ ⊢ Ξ⟧} ⟦Γ ⊢ Ξ⟧`.
> Finally, define `v₀(q) := ⟦ ⊢ q⟧; v₀(⊥) := ⟦ ⊢ ⊥⟧` to complete the definition of the
> canonical model for ILL.
> It is readily seen that `I = {x ∈ 1 | x·x = x}` exactly consists of the elements of the
> form `!Γ`. The following lemma establishes the proof of Theorem 2.9:
>
> Lemma 2.10. For any ILL formula `B`, we have `B ∈ v₀(B) ⊆ ⟦ ⊢ B⟧`. In particular,
> `ε ∈ v₀(B)` implies that `B` is provable in ILL.
> *Proof.* By induction on the complexity of `B` (see (Okada 1996)).

So, in this source: **the monoid is quotiented** (multisets modulo the multiplicity of
`!`-formulas, so that `!B · !B = !B` holds on the nose), and the definition of `I` is
*not* weakened. Two things the campaign must check before transcribing this, neither of
which the paper spells out:

1. Well-definedness: `⟦Γ ⊢ Ξ⟧` must respect the identification, i.e. provability of
   `Δ, Γ ⊢ Ξ` must be invariant under changing the multiplicity (≥ 1) of a `!`-formula.
   This is contraction `!C` in one direction and `!W` in the other (weakening re-adds
   copies); not stated in the paper, an observation of this survey.
2. "`I` consists exactly of the elements of the form `!Γ`": `Δ ∈ 1 = Cl₀({∅})` and
   `Δ·Δ = Δ` in the quotient forces every formula of `Δ` to be a `!`-formula (a
   non-`!` formula has its multiplicity doubled); the converse needs `!Γ ∈ Cl₀({∅})`,
   i.e. weakening. The paper says only "readily seen".

In the two-zone calculus `Γ ; Δ ⟹ C` the quotient comes for free: take the monoid of
pairs (finite *set* Γ of unrestricted hypotheses, finite multiset Δ of linear ones) with
componentwise union/sum; the idempotents in `1` are then the pairs `(Γ, ∅)`. This remark
is this survey's, not the source's (**no source read for it yet**; see A.3 on Okada 2002
for whether the published proofs do this).

**Cut-free completeness (Remark 2.11, p. 6) [read, rendered].**

> If one replaces the definition of `⟦Γ ⊢ Ξ⟧` with
> `⟦Γ ⊢ Ξ⟧ = {Δ | Δ, Γ ⊢ Ξ is cut-free provable in ILL}`,
> one obtains the cut-elimination theorem at the same time (Okada 1996).

So the completeness theorem as stated (2.9) is for provability with cut; the cut-free
version is asserted in a remark with a pointer to Okada 1996, not proved here. Note that
with the cut-free definition the invariance in point 1 above still holds (it needs only
`!C` and `!W`), but Lemma 2.10 changes shape: the inclusion `v₀(B) ⊆ ⟦ ⊢ B⟧` is what
gives cut-free provability, and `B ∈ v₀(B)` is proved without cut (Okada's method;
details **not in this file**).

**Classical phase space, for comparison (Definition 2.12, p. 6) [read, rendered].**
"A *classical phase space* `(M, ·, ε, ⊥)` consists of a commutative monoid `(M, ·, ε)` and
a distinguished subset ⊥ of `M`", `X^⊥ := X ⊸ ⊥`, closed iff `X = X^⊥⊥`,
`?X := (X^⊥ ∩ I)^⊥`. Every classical phase space is an intuitionistic one with
`Cl(X) := X^⊥⊥` (p. 7); Example 2.13 (p. 7) shows `(ℕ, +, 0, Cl_≤)` with
`Cl_≤(X) := {n | ∃m ∈ X (n ≤ m)}` is intuitionistic and not classical.

(More sources for Q-A follow below as they are read.)

---

## Q-C. Undecidability and complexity (Lincoln, Mitchell, Scedrov, Shankar)

Source read: P. Lincoln, J. Mitchell, A. Scedrov, N. Shankar, "Decision problems for
propositional linear logic", Annals of Pure and Applied Logic 56 (1992) 239–311, scanned
copy `lmss92-apal.pdf` (73 file pages; file page n = journal page 238 + n). A second copy,
the SRI version dated September 13, 1994 (`lmss-sri94.pdf`, 89 pages), has the same
theorem numbers and wording for the statements below **[read, both files; statements
checked in the `pdftotext` output of both, formulas on journal pp. 264, 270 rendered]**.

**Undecidability, classical (Theorem 3.7, journal p. 275 = file p. 37) [read].**

> Theorem 3.7. The provability problem for propositional linear logic is recursively
> unsolvable.

**Undecidability, intuitionistic (Corollary 3.8, journal p. 275 = file p. 37) [read].**

> Corollary 3.8. The provability problem for propositional intuitionistic linear logic
> is recursively unsolvable.

The text before it: "the intuitionistic fragment is restricted so that there is only one
positive formula in any sequent. In fact, the entire construction above was carried out in
intuitionistic linear logic ... Thus any directed proof of θ(s) in a theory derived from
M is in the intuitionistic fragment of linear logic, and along with a conservativity
result not proven here, we have the following corollary." And after it: "In the proof of
this corollary we make use of the conservativity property of full linear logic over the
intuitionistic fragment for any sequents occuring in a directed proof of a translation of
an ACM machine configuration. This conservativity is a weaker property than full
conservativity since sequents in such a directed proof have a special form. In
particular, they have no constants, and the right-hand side is always a single formula."
So **Corollary 3.8 rests on a conservativity result that the paper states it does not
prove.**

**Which connectives.** The paper does not list the connectives of the intuitionistic
fragment used. What it gives (journal p. 270 = file p. 32, rendered) is the theory of an
and-branching two-counter machine without zero-test (ACM):

```
Q_i Increment A Q_j   ↦   ⊢ q_i^⊥, (q_j ⊗ a)
Q_i Decrement A Q_j   ↦   ⊢ q_i^⊥, a^⊥, q_j
Q_i Fork Q_j, Q_k     ↦   ⊢ q_i^⊥, (q_j ⊕ q_k)
```

(and the same for counter B), with the remark "Using linear implication, the
(Q_i Increment B Q_j) transition may be viewed as ⊢ q_i ⊸ (q_j ⊗ b)". A configuration
⟨Q_i, x, y⟩ is translated to `⊢ q_i^⊥, a^⊥^x, b^⊥^y, q_F`. Each axiom
`⊢ C, p_a^⊥, …, p_z^⊥` is coded (journal p. 264 = file p. 26, rendered) as the formula
`[t] ≜ (C^⊥ ⊗ p_a ⊗ … ⊗ p_z)` put under `?`, and Lemmas 3.2/3.3 (journal pp. 264–265)
say `⊢ Γ` is provable in theory T iff `⊢ ?[T], Γ` is provable without non-logical axioms.
Section 3.5 (journal p. 269): "our translation uses only MALL formulas and theories".
Read two-sidedly, the sequents are
`!(q_i ⊸ q_j ⊗ a), !(q_i ⊗ a ⊸ q_j), !(q_i ⊸ q_j ⊕ q_k), …, q_i, a^x, b^y ⊢ q_F`:
**connectives `!`, `⊸`, `⊗`, `⊕` and atoms only, no constants, `!` only on the left at
top level.** That list of connectives is this survey's reading of the stated axioms, not
a sentence of the paper. Every such sequent lies in the campaign's fragment
(`⊸ ⊗ ⊕ !`), so the campaign's DILL is undecidable given Cor. 3.8 and the
one-zone/two-zone correspondence.

**Decidability without exponentials.**

> Theorem 2.2 (journal p. 244 = file p. 6). The provability in MALL of a given sequent
> can be decided by a polynomial-space bounded Turing machine. **[read]**

> Theorem 2.12 (journal p. 259 = file p. 21). MALL provability is PSPACE-complete. **[read]**

For the intuitionistic case there is **no numbered theorem**, only the sentence directly
after Theorem 2.12 (journal p. 259) **[read]**:

> With two-sided sequents, the intuitionistic fragment of MALL constrains the right-hand
> side of the sequent to contain at most one formula. A two-sided reformulation of the
> above proof could be carried out entirely within the intuitionistic fragment of MALL,
> showing that intuitionistic MALL is also PSPACE-complete.

MALL here is the classical one-sided system with `⊗, ⅋, &, ⊕, 0, 1, ⊤, ⊥` and literals
(journal p. 243–244). The introduction (journal p. 242 = file p. 4) also records "We do
not know if multiplicative linear logic with ! is decidable" **[read]**.

---

## Q-A continued: further sources

(Placed here in order of writing; A.2–A.5 belong with A.1 above.)

### A.2 Second source read: Okada & Terui 1998 (weak idempotents, chosen submonoid, no quotient; cut-free completeness as a theorem; exactly the campaign's connectives)

M. Okada, K. Terui, "Completeness Proofs for Linear Logic Based on the Proof Search Method
(Preliminary Report)", RIMS Kôkyûroku 1023 (1998) 57–75, file `kokyuroku1023-4.pdf`
(19 pages, a scan; printed page = file page + 56). All formulas below read from rendered
pages. This is not the JSL 1999 paper (which I could not get), but it is by the same
authors, one year earlier, and states the semantics in full.

**The calculus (Appendix A, printed pp. 73–74 = file pp. 17–18) [read, rendered].**
"Multiplicatives: `1, A ⊗ B, A ⊸ B`; Additives: `⊤, 0, A & B, A ⊕ B`; Modality
(Exponential): `!A`. ... A sequent of ILL is of the form `Γ ⊢ C`" with Γ a finite
multiset. No `⊥`, exactly one formula on the right: **this is the campaign's formula
language and sequent shape, in one zone.** Rules: Identity `A ⊢ A`, Cut, `⊗l ⊗r 1l 1r ⊸l
⊸r ⊕l ⊕r₁ ⊕r₂ 0l &l₁ &l₂ &r ⊤r`, and `!D`, `!C`, `!W`, `!r` exactly as in A.1 (with `C`
for the succedent).

**Intuitionistic phase space (Definition 1, printed p. 59 = file p. 3) [read, rendered].**

> Definition 1. An intuitionistic phase space `(M, Cl)` consists of a commutative monoid
> `M` and a function `Cl : 𝒫(M) ⟶ 𝒫(M)`, called a *closure operator*, satisfying the
> following;
> (C1) `X ⊆ Cl(X)`;
> (C2) `X ⊆ Y` implies `Cl(X) ⊆ Cl(Y)`;
> (C3) `Cl(X) = Cl(Cl(X))`;
> (C4) `Cl(X)Cl(Y) ⊆ Cl(XY)`;
> where `XY` is defined by `{xy | x ∈ X, y ∈ Y}`. A set `X ⊆ M` that satisfies
> `X = Cl(X)` is called a *fact*.

Then (printed pp. 59–60): `1 = Cl({1})` ("1 stands for the unit element of M"), `⊤ = M`,
`0 = Cl(∅)`, and for facts `X, Y`:
`X ⊸ Y = {y | ∀x ∈ X  xy ∈ Y}`, `X ⊗ Y = Cl(XY)`, `X & Y = X ∩ Y`, `X ⊕ Y = Cl(X ∪ Y)`.

**The clause for `!` (printed p. 60 = file p. 4) [read, rendered].**

> If `M` is an intuitionistic phase space, then `J(M) = {x ∈ 1 | x ∈ Cl({xx})}` is a
> submonoid of `M`. An *enriched intuitionistic phase space* is an intuitionistic phase
> space `M` endowed with a submonoid `K` of `J(M)` (not necessary to be a fact).
> For any fact `X` of intuitionistic phase space, define
> • `!X = Cl(X ∩ K)`.

So here: **weak idempotents `x ∈ Cl({x·x})` inside `1`, and a chosen submonoid
`K ⊆ J(M)` as part of the structure.**

**Model and validity of a sequent (printed p. 60) [read, rendered].**

> An intuitionistic phase model `M = (M, Cl, K, v)` is given by an intuitionistic phase
> space `M = (M, Cl, K)` and an *interpretation* `v` which maps each atomic formula α to a
> fact `v(α)` of `M`, which is also denoted by `α*`. Then each formula `A` is interpreted
> by a fact `A*` along the above definitions, and `Γ ≡ A₁, …, Aₙ` is interpreted by
> `Γ* = A₁* ⊗ ⋯ ⊗ Aₙ*`. We say that `A` is *satisfied* in `M` if `1 ∈ A*`, and that
> `Γ ⊢ C` is *satisfied* in `M` if `Γ* ⊆ C*`.

(Not stated in the paper: what `Γ*` is for empty Γ; the reading `Γ* = 1 = Cl({1})` makes
"`⊢ C` satisfied" agree with "`C` satisfied".)

**Soundness, completeness, cut elimination (Theorem 2, printed p. 71 = file p. 15)
[read, rendered].**

> Theorem 2 (Completeness and Cut-Elimination). Let `S₀` be a sequent of ILL. Then the
> following are equivalent;
> 1. `S₀` is satisfied in every intuitionistic phase model;
> 2. `S₀` is cut-free provable in ILL;
> 3. `S₀` is provable in ILL.
> Proof. 2 implies 3 trivially. 3 implies 1 by the usual soundness argument. Here we prove
> that 1 implies 2.

Soundness is thus asserted ("the usual soundness argument"), not written out. The
completeness is **cut-free completeness**.

**The syntactic model here (§4.2, printed p. 69 = file p. 13) [read, rendered].** It is
*not* the provability model of A.1 but a countermodel read off one failed proof search.
An OR-tree of `S₀` (§4.1, printed p. 68) is a tree of sequents in which every node has
one child per applicable rule instance, the child being one chosen premise; it is *open*
if no node is an axiom; Proposition 5 (p. 69): "`S₀` is provable in L if and only if
there is no open OR-tree of `S₀`." Given an open OR-tree 𝓡 in cut-free ILL, with `|𝓡|`
its set of labels and `𝓡ₗ* = {Δ | Δ, Π ⊢ C ∈ |𝓡| for some Π and C}`:

> • `M = 𝓡ₗ* ∪ {√}`, where √ is a distinguished formula not occurring in 𝓡. ...
> • For each `Γ ∈ M` and `Δ ∈ M`, `Γ · Δ = Γ, Δ` if `Γ, Δ ∈ 𝓡ₗ*`, and `√` otherwise. ...
> • Let `⟦Γ ⊢ C⟧` be `{Σ ∈ M | Σ, Γ ⊢ C ∉ |𝓡|}`. We write `⟦C⟧` to denote `⟦ ⊢ C⟧`.
> • For `X ⊆ M`, `Cl(X) = ⋂ {⟦Γ ⊢ C⟧ | X ⊆ ⟦Γ ⊢ C⟧, Γ ⊢ C is a sequent of ILL}`. ...
> • `K = {!Δ | !Δ ∈ M} ∪ {∅, √}`.
> • `v(α) = ⟦α⟧` for each atomic formula α.

**No quotient is taken**: elements are plain multisets, and `!A, !A ≠ !A` in `M`. The
exponential is handled by `K` and by closure properties of facts, Lemma 7 (printed p. 70
= file p. 14), of which the `!` clauses are:

> (vi) if `A, Γ ∈ X` and `!A, Γ ∈ M`, then `!A, Γ ∈ X`;
> (vii) if `!A, !A, Γ ∈ X`, then `!A, Γ ∈ X`;
> (viii) if `Γ ∈ X` and `!A, Γ ∈ M`, then `!A, Γ ∈ X`.

(dereliction, contraction, weakening read as closure conditions). The key Proposition 6
(p. 70): "(a) if `A` is in `𝓡ₗ*`, then `A ∈ A*`; (b) if `Γ ⊢ A ∈ |𝓡|`, then `Γ ∉ A*`",
(b) in the form "(b') for any `A`, `A* ⊆ ⟦A⟧`". Its `!` case (Case 6, printed p. 71):

> As for (a), `B ∈ B*` by IH (since `B ∈ 𝓡ₗ*`), hence `!B ∈ B*` by Lemma 7(vi). On the
> other hand, `!B ∈ K` by definition. Therefore `!B ∈ Cl(B* ∩ K) = !B*`.
> As for (b'), we show that `B* ∩ K ⊆ ⟦!B⟧`. Assume that `Γ ∈ B* ∩ K`. If `Γ ≡ √`, then
> by Lemma 7(i). Otherwise Γ is of the form `!Δ` ... If `!Δ ⊢ !B ∈ |𝓡|`, then `!Δ ⊢ B`
> would be also in `|𝓡|`. But it is impossible because `!Δ ∈ ⟦B⟧` by IH.

That `K ⊆ J(M)` (each `!Δ` lies in `Cl({∅})` and in `Cl({!Δ, !Δ})`) is not argued in the
paper; it is what Lemma 7 (viii) and (vii) give. The paper's abstract (printed p. 57)
says the method yields "the completeness theorem for intuitionistic (classical, resp.)
linear logic with respect to intuitionistic (classical, resp.) phase semantics" and
(p. 59) "the cut-elimination theorem as a corollary, since we do not use the cut rule
during the construction".

### A.3 Third source read: Lafont 1997 (classical, but it is where `K`, `J(M)`, `I(M)` and the quotient are explained)

Y. Lafont, "The finite model property for various fragments of linear logic" (JSL 62(4),
1997, 1202–1208), author's copy `lafont97-model.ps` (PostScript, 6 pages). **Caveat on
how it was read:** converting the PostScript was not permitted in this session, so the
text was recovered by extracting the string constants of the file as data; prose is
reliable, symbols were decoded from font codes by hand (`{x²}⊥⊥`, `⊸` etc.) and are
**not rendered**. Treat formulas from this file as "read, symbols decoded".

Section 3 "Semantics of exponentials" (p. 4 of the file) **[read, symbols decoded]**:

> If `M` is a phase space, it is easy to see that `J(M) = {x ∈ 1•; x ∈ {x²}^⊥⊥}` is a
> submonoid of `M`. An *enriched phase space* is a phase space `M` endowed with a
> submonoid `K` of `J(M)`. This `K` is not required to be a fact. For instance, `K` may
> be `{1}`, or `J(M)` itself, or `I(M) = {x ∈ 1•; x = x²}`. In the latter case, one
> recovers Girard's phase semantics [Gir95].
> For any fact `X` in an enriched phase space, define `?X = (X^⊥ ∩ K)^⊥`,
> `!X = (?X^⊥)^⊥ = (X ∩ K)^⊥⊥`.

Syntactic model (p. 4): "`LL•` is the free commutative monoid generated by all formulas
in LL; `⊥•` is the set of all provable sequents in cut-free LL; `α• = {α}^⊥` for any
positive atom α; `K` is the submonoid of `LL•` generated by all formulas of the form
`?A`. By contraction and weakening, `K` is indeed a submonoid of `J(M)`." Lemma 3 (p. 4):
"For any formula `A` of LL, one has `A• ⊆ {A}^⊥` in `LL•`. In particular, any formula
which is satisfied by `LL•` is provable in cut-free LL." (Lemma 1, p. 2, the MALL case,
is attributed "(Okada)"; "the nice point about this proof is that it does not use the cut
rule (see also [Oka94])".)

The passage that settles the campaign's question (pp. 4–5) **[read]**:

> A *logical congruence* on a phase model `M` is a congruence `∼` on `M` such that `⊥•` is
> closed for `∼`. ... [p. 5] the smallest congruence `∼` such that `?A ∼ ?A, ?A` for any
> `A` is a logical congruence on `LL•`, and `K` is already closed for `∼`. In that case,
> `π(K) = I(LL•/∼)`, and since `LL•/∼` satisfies the same formulas as `LL•`, one gets the
> completeness of Girard's phase semantics for LL [Gir95]. Note that Girard's phase
> semantics is not closed under quotient by a logical congruence, because it is not true
> in general that `π(I(M)) = I(M/∼)`.

So the two treatments are related exactly as the campaign suspected: **either** weaken
the idempotent set to `J(M)` and add a chosen `K` (free monoid, no quotient: Lafont 1997,
Okada–Terui 1998, Larchey-Wendling's Coq development), **or** keep strict idempotents
`I` and quotient the syntactic monoid by `!A ∼ !A,!A` (Girard 1995, KOT 2006). The class
of `K`-models contains the `I`-models (`K := I(M)`), so soundness for `K`-models is the
stronger soundness statement and completeness for `I`-models the stronger completeness
statement; both hold.

### A.4 Fourth source read: Larchey-Wendling 2018 (relational variant, mechanised)

D. Larchey-Wendling, "Mechanizing Cut-Elimination in Coq via Relational Phase Semantics",
slides, ENS-Lyon, 18 Dec 2018, file `larchey18-slides.pdf` (12 pages); slide 8 rendered.
**[read]** Closure `cl` on predicates over a type `M` with a *composition relation*
`• : M → M → M → Prop` and `e : M` (no monoid laws; unit, commutativity, associativity
hold up to closure, plus stability `(cl X) • Y ⊆ cl(X • Y)`). Slide 8:

> Let `𝒥 := {x | x ∈ cl{e} ∧ x ∈ cl(x • x)}`. Choose `𝒦 ⊆ 𝒥` such that `e ∈ cl 𝒦` and
> `𝒦 • 𝒦 ⊆ 𝒦`. ... `⟦!A⟧ := cl(𝒦 ∩ ⟦A⟧)`, `⟦Γ₁, …, Γₙ⟧ := ⟦Γ₁ ⊗ ⋯ ⊗ Γₙ⟧`.
> Soundness: if `Γ ⊢ A` has a proof then `⟦Γ⟧ ⊆ ⟦A⟧`.

Slide 9: syntactic model `M := list Form`, `Θ ∈ Γ • Δ ⟺ Γ, Δ ∼ₚ Θ`,
`K := {!Γ | Γ ∈ M}`, contextual closure `Δ ∈ cl X ⟺ ∀Γ A, X, Γ ⊨ A → Δ, Γ ⊨ A` for a
deduction relation `⊨` "such as provability or cut-free provability"; slide 10: "`K ⊆ J`
iff `⊨` closed under W and C"; slide 11 "Okada's lemma: for `⊨` defined as `⊢cf` ...
`∀A, ⌊A⌋ ∈ ⟦A⟧ ⊆ ↓A`", giving cut-admissibility. Again weak idempotents, chosen `K`, **no
quotient** (lists up to permutation only). See Q-D for the code.

### A.5 Summary of Q-A

| | idempotents used for `!` | structure carries `K`? | syntactic monoid | completeness stated |
|---|---|---|---|---|
| KOT 2006, Def. 2.2/2.4, Thm 2.9 (pp. 3–6) | `I = {x ∈ 1 | x·x = x}` | no | multisets **modulo multiplicity of `!`-formulas** | with cut (Thm 2.9); cut-free in Remark 2.11, pointing to Okada 1996 |
| Okada–Terui 1998, Def. 1, Thm 2 (pp. 59–60, 71) | `J(M) = {x ∈ 1 | x ∈ Cl({xx})}` | yes, submonoid `K ⊆ J(M)` | multisets of one open OR-tree plus a sink `√`, no quotient | cut-free (Thm 2), for sequents |
| Lafont 1997, §3 (classical) | `J(M)`, with `I(M)` as the special case | yes | free commutative monoid; quotient by `?A ∼ ?A,?A` recovers `I` | cut-free (Lemma 3) |
| Larchey-Wendling 2018 (Coq) | `𝒥 = {x | x ∈ cl{e} ∧ x ∈ cl(x•x)}` | yes, `𝒦 ⊆ 𝒥`, `e ∈ cl 𝒦`, `𝒦•𝒦 ⊆ 𝒦` | lists up to permutation, relational composition | cut-free |

Not obtained, so nothing is asserted from them: Okada TCS 227 (1999), Okada TCS 281
(2002), Okada–Terui JSL 64 (1999), Abrusci 1990, Ono 1993, Troelstra 1992 ch. 8, Girard
1995. From memory only, **not checked**: Okada 2002 treats intuitionistic phase
semantics with a closure operator in the same way and proves cut-free completeness for
(higher-order) ILL; Troelstra's book defines an "intuitionistic phase structure" as a
commutative monoid with a closure operation satisfying `C(X)·C(Y) ⊆ C(X·Y)`. KOT 2006
p. 3 confirms the second attribution in general terms ("in the style of (Troelstra
1992)") **[read]**.
