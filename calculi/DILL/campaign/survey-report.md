# DILL campaign: literature survey report

Written 2026-11-26, 14:49–15:10 GMT (times from `date`). Status: complete for the bounded
survey asked for; what could not be obtained is listed at the end.

Convention: every claim is marked **[read]** (read in the named file, at the page given;
pages are given as printed page and file page where they differ) or **[memory]** (from memory, not checked). Formulas marked "rendered" were read
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
is this survey's, not the source's: **no source was found that builds the syntactic phase
model from a two-zone calculus**. The published proofs that avoid the quotient (A.2–A.4)
do it on a one-zone monoid, with a chosen `K`.

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

### A.5 Okada 2002 at second hand: closed sets instead of a closure operator, `!`-free

Okada's TCS 281 paper itself was refused (see "Could not get"). Its definitions for the
`!`-free fragment are recalled, with pointers into it, in J. Suzuki, C. Grellois, K. Sano,
"Phase Semantic Cut-elimination for Intuitionistic Linear Logic with Fixed Points", EPTCS
449 (2026) 221–238, file `arxiv2607.20187.pdf` (printed pp. 224–225 = file pp. 4–5)
**[read in that file; `pdftotext` output, formulas not rendered; second-hand for Okada]**:

> here we adopt Okada's definition [19, Section 2] ...
> Definition 2.2. A set `D_M ⊆ ℘(M)` is a *set of closed sets* if it satisfies the
> following: 1. for any `D′ ⊆ D_M`, `⋂D′ ∈ D_M`; 2. for any `X ∈ ℘(M)` and `Y ∈ D_M`,
> `X ⊸ Y = {y ∈ M | for all x ∈ X, xy ∈ Y} ∈ D_M`. An *intuitionistic phase space* is a
> pair `(M, D_M)` of a commutative monoid and a set of closed sets. The closure function
> `cl : ℘(M) → ℘(M)` is defined by `cl(X) = ⋂{Y ∈ D_M | X ⊆ Y}`.
> Proposition 2.3 (Okada [19, p. 475]). 1. `X ⊆ cl(X)`, 2. `cl(cl(X)) = cl(X)`, 3. if
> `X ⊆ Y` then `cl(X) ⊆ cl(Y)`, 4. `cl(X)·Y ⊆ cl(X·Y)`.
> Proposition 2.6 (Okada [19, Theorem 3.1]). If a sequent `A₁, …, Aₙ ⊢ C` is provable in
> IMALL, then `⟦A₁⟧_V ⋯ ⟦Aₙ⟧_V ⊆ ⟦C⟧_V` for any intuitionistic phase model
> `(M, D_M, V)`, where the zero-ary product of the monoid operation is `{1}`.
> Definition 2.7. `Pr_cf(C) = {Γ | Γ ⊢ C is provable without (Cut) in IMALL}` ... `M` the
> set of all finite multisets of formulas, union as product, `X ∈ D_M` iff
> `X = ⋂{Pr_cf(C) | C ∈ F}` for some set `F` of formulas, `V(p) := Pr_cf(p)`.
> Proposition 2.8 (Okada [19, Lemma 3.6]). For any formula `A`, `[A] ∈ ⟦A⟧_V ⊆ Pr_cf(A)`.

This is a third presentation of the structure (a family of closed sets closed under
`⋂` and `X ⊸ –`; compare KOT 2006 Theorem 2.8) and a second statement of sequent
validity, here without closing the product (`⟦A₁⟧⋯⟦Aₙ⟧ ⊆ ⟦C⟧`, equivalent to the
`⊗`-form since `⟦C⟧` is closed). The paper treats IMALL with fixed points and **no `!`**
(p. 15: the relation between `!` and fixed points "within an intuitionistic setting" is
left for further work), so it gives nothing on the exponential clause.

### A.6 Summary of Q-A

| | idempotents used for `!` | structure carries `K`? | syntactic monoid | completeness stated |
|---|---|---|---|---|
| KOT 2006, Def. 2.2/2.4, Thm 2.9 (pp. 3–6) | `I = {x ∈ 1 : x·x = x}` | no | multisets **modulo multiplicity of `!`-formulas** | with cut (Thm 2.9); cut-free in Remark 2.11, pointing to Okada 1996 |
| Okada–Terui 1998, Def. 1, Thm 2 (pp. 59–60, 71) | `J(M) = {x ∈ 1 : x ∈ Cl({xx})}` | yes, submonoid `K ⊆ J(M)` | multisets of one open OR-tree plus a sink `√`, no quotient | cut-free (Thm 2), for sequents |
| Lafont 1997, §3 (classical) | `J(M)`, with `I(M)` as the special case | yes | free commutative monoid; quotient by `?A ∼ ?A,?A` recovers `I` | cut-free (Lemma 3) |
| Larchey-Wendling 2018 (Coq) | `𝒥 = {x : x ∈ cl{e} ∧ x ∈ cl(x•x)}` | yes, `𝒦 ⊆ 𝒥`, `e ∈ cl 𝒦`, `𝒦•𝒦 ⊆ 𝒦` | lists up to permutation, relational composition | cut-free |
| Okada 2002 as recalled by Suzuki–Grellois–Sano 2026 (A.5) | none (`!`-free IMALL only) | – | free commutative monoid of multisets; closed sets `⋂ Pr_cf(C)` | cut-free |

What the sources read agree on: a commutative monoid; a closure operator with
`Cl(X)·Cl(Y) ⊆ Cl(X·Y)` (equivalently a family of closed sets closed under `⋂` and
`X ⊸ –`); `⊗ ⊕` closed, `& ⊸` not needing closure, `1 = Cl({ε})`, `0 = Cl(∅)`, `⊤ = M`;
`!X = Cl(X ∩ S)` for a set `S` of (weak) idempotents inside `1`; a sequent is valid when
the product of the antecedent's values is included in the value of the succedent. They
differ only in `S` and, correspondingly, in the syntactic monoid.

For the campaign's plan (this survey's reading, not a source's): the `K ⊆ J(M)` form is
the one with a written cut-free completeness proof for exactly the campaign's
connectives (A.2) and a mechanised precedent (A.4), and it needs no quotient type;
soundness proved for `K`-models covers the strict-idempotent models as the case
`K := I(M)` (Lafont, A.3). The strict form `I` needs either the quotient of A.1 or, on a
two-zone monoid of pairs (set, multiset), nothing extra; that last construction is not
in any source read.

Not obtained, so nothing is asserted from them: Okada TCS 227 (1999), Okada TCS 281
(2002, except at second hand in A.5), Okada–Terui JSL 64 (1999), Abrusci 1990, Ono 1993, Troelstra 1992 ch. 8, Girard
1995. From memory only, **not checked**: Okada 2002 treats intuitionistic phase
semantics with a closure operator in the same way and proves cut-free completeness for
(higher-order) ILL; Troelstra's book defines an "intuitionistic phase structure" as a
commutative monoid with a closure operation satisfying `C(X)·C(Y) ⊆ C(X·Y)`. KOT 2006
p. 3 confirms the second attribution in general terms ("in the style of (Troelstra
1992)") **[read]**.

---

## Q-B. The finite model property

**Lafont 1997 (classical), author's copy `lafont97-model.ps` [read, symbols decoded, see
the caveat in A.3].** Introduction (p. 1):

> One says that the propositional classical logic and the propositional intuitionistic
> logic satisfy a *finite model property*. In particular, they are decidable: there is a
> semi-algorithm for provability (proof search) and a semi-algorithm for non provability
> (model search). For that reason, a logic which is undecidable, such as first order
> logic, cannot satisfy a finite model property. The case of linear logic is more
> complicated. The full propositional fragment LL has a complete semantics in terms of
> phase spaces [Gir87, Gir95], but it is undecidable [LMSS92]. The multiplicative
> additive fragment MALL is decidable, in fact PSPACE-complete [LMSS92], but the
> decidability of the multiplicative exponential fragment MELL is still an open problem.
> For affine logic, that is, linear logic with weakening, the situation is somewhat
> better: the full propositional fragment LLW is decidable [Kop95a]. Here, we show that
> the finite phase semantics is complete for MALL and for LLW, but not for MELL.

- Theorem 2 (p. 3): for any formula `A` in MALL, equivalent are "(1) `A` is provable in
  MALL; (2) `A` is satisfied by all finite phase models; ..." **FMP for MALL.**
- Theorem 4 (p. 5): for any formula `A` in LL, equivalent are "(1) `A` is provable in
  LLW; (2) `A` is satisfied by all finite affine phase models; ..." **FMP for LLW
  (classical affine logic with exponentials).** "In particular, LLW is decidable."
- Theorem 3 (p. 4): "φ is satisfied by all finite phase models, but it is not provable",
  for `φ = !a ⊗ !(a ⊗ b) ⊗ !(a ⊗ b ⊸ 1) ⊸ b = ?a^⊥ ⅋ ?(a^⊥ ⅋ b^⊥) ⅋ ?(a ⊗ b ⊗ ⊥) ⅋ b`
  with `a, b` positive atoms (the two forms, both in the file, agree under duality, which
  checks the symbol decoding). **FMP fails for MELL**, and the text adds: "φ belongs to
  the so-called multiplicative exponential Horn fragment of linear logic, which encodes
  the reachability problem for Petri nets. This means that this fragment does not satisfy
  the finite model property, whereas it is decidable." The proof: in a finite model
  `(b^p)• = (b^q)•` for some `p < q`, so `ψ = b^p ⊸ b^q` is satisfied, and `ψ ⊸ φ` is
  provable; non-provability of φ by an infinite model on the free group on `a` with
  `K = {1}`.

**Okada & Terui, JSL 64(2), 1999, 790–802: abstract only [read, on the publisher's page;
the paper itself not obtained].**

> Recently Lafont [6] showed the finite model property for the multiplicative additive
> fragment of linear logic (MALL) and for affine logic (LLW), i.e., linear logic with
> weakening. In this paper, we shall prove the finite model property for intuitionistic
> versions of those, i.e. intuitionistic MALL (which we call IMALL), and intuitionistic
> LLW (which we call ILLW). In addition, we shall show the finite model property for
> contractive linear logic (LLC), i.e., linear logic with contraction, and for its
> intuitionistic version (ILLC). The finite model property for related substructural
> logics also follow by our method. In particular, we shall show that the property holds
> for all of FL and GL⁻-systems except FLc and [one more, symbol lost on the page] of Ono
> [11], that will settle the open problems stated in Ono [12].

Theorem numbers and exact statements: **not available** (paper not obtained). KOT 2006
p. 2 **[read]** cites the pair as "decidability of some fragments (Lafont 1997; Okada and
Terui 1999)".

**So, for the intuitionistic side:** FMP is proved for IMALL (the campaign's fragment
without `!`), for ILLW (with `!`, plus weakening) and for ILLC (plus contraction), per
the abstract.

**Full ILL with `!`.** No source was found that states "ILL does not have the finite
model property" in those words. What the sources read give:
1. Lafont's general remark quoted above (an undecidable logic cannot have the FMP)
   **[read]**, together with LMSS Corollary 3.8 (ILL undecidable; Q-C) **[read]**.
2. Lafont's Theorem 3 formula φ lies in the campaign's language (`! ⊗ ⊸ 1`, single
   conclusion). His argument appears to transfer to intuitionistic phase models
   unchanged: a finite model has finitely many closed sets, so it satisfies some
   `b^p ⊸ b^q` with `p < q`; `(b^p ⊸ b^q) ⊸ φ` has an intuitionistic proof (make `p`
   pairs `a, b` from `!(a ⊗ b)`, trade `b^p` for `b^q`, cancel `p + (q−p−1)` pairs using
   `!a` for the missing `a`s, leaving one `b`); φ is unprovable in LL, hence in ILL.
   **This transfer is this survey's observation, checked on paper only, not found in a
   source and not machine-checked.** It would give a concrete, small witness of FMP
   failure for DILL: `· ; · ⟹ !a ⊗ !(a ⊗ b) ⊗ !(a ⊗ b ⊸ 1) ⊸ b` is underivable and has
   no finite countermodel.

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

## Q-D. Existing formalisations

Search bounded to about 20 minutes (2026-11-26). Where I looked: the public GitHub API
(file trees and raw files, unauthenticated) for the repositories named below; the
Isabelle AFP site; a local Mathlib checkout (commit `fabf563`, 2026-06-15) by `grep`;
four web searches (Lean, Agda, Abella, Isabelle/Coq). "Not found" below means not found
in this search, not that none exists. **No mechanisation of a two-zone, single-conclusion
intuitionistic calculus `Γ ; Δ ⟹ C` (DILL sequent calculus) with cut elimination was
found in any prover.** The nearest things, each read in its source file:

| Where | System | Proved | How read |
|---|---|---|---|
| **Rocq: Yalla** (O. Laurent, C. Lucas), `github.com/olaure01/yalla`, files `yalla/iformulas.v`, `ill_def.v`, `ill_cut.v`, `ill_prop.v`, `ill_vs_ll.v` | **One-zone** ILL, `ill P : list iformula → iformula → Type`, lists with explicit exchange (`ex_ir`), parametrised by a fragment `P` (cut on/off, axioms, permutation or not, which covers Lambek calculus). Connectives: `ione, itens, ilpam` and `ilmap` (two implications), `igen`/`ineg` (negations to a constant `N`), `itop, iwith, izero, iplus, ioc`. Rules `oc_irr` (promotion on `map ioc l`), `de_ilr`, `wk_ilr`, `co_ilr`. | Cut admissibility (`cut_admissible_ill`, `cut_admissible_ill_axfree`, `cut_ill_admissible` in `ill_cut.v`); reversibility lemmas (`ione_rev_noax`, `itens_rev_noax`, `ilpam_rev_noax`, `iwith_rev1_noax`, `iplus_rev1_noax`, `ioc_rev_noax`, …), subformula property (`isubformula_cutfree`, `isubformula`), conservativity over fragments, `strong_consistency_ill_axfree : notT (ill P nil izero)` in `ill_prop.v`. No phase semantics for ILL seen in the file list. | [read: file list, rule constructors and lemma names in the fetched `.v` files; proofs not checked or compiled] |
| **Coq: Coq-Phase-Semantics** (D. Larchey-Wendling), `github.com/DmxLarchey/Coq-Phase-Semantics`, e.g. `coq.prop/ill_rules.v`, `phase_sem.v`, `cut_elim.v` | **One-zone** ILL, `ill_proof : list ill_form → ill_form → Type` with a permutation rule; connectives `⊸ & ! ⊗ ⊕ ⟘ ⟙ 𝝐` (`⟘` has the rule `⟘::Γ ⊢ A`, i.e. it is the additive zero; `𝝐` is the unit 1): the campaign's connective set. Rules `in_llp_bang_l` (dereliction), `in_llp_bang_r` (promotion on `‼Γ`), `in_llp_weak`, `in_llp_cntr`, `in_llp_cut`. | Relational phase semantics (A.4): soundness `ill_Form_sem_sound Γ a : Γ ⊢ a → ⟬Γ⟭ ⊆ ⟦a⟧`; `Okada_formula A : sg (A::nil) ⊆ ⟦A⟧ ∧ ⟦A⟧ ⊆ ↓A`; `ill_cut_admissibility Γ A : Γ ⊢ A → exists p : Γ ⊢ A, ill_cut_free p`. **This is the semantic (Okada) cut-elimination proof for ILL with `!`, mechanised**, with `K ⊆ J` and no quotient. Variants in `coq.type`, `coq.nc` (non-commutative), `coq.gen`. | [read: the three `.v` files and the slides] |
| **Rocq: coq-ll** (B. Xavier, C. Olarte, with Reis, Nigam), `github.com/meta-logic/coq-ll`, `PLL/LL/SequentCalculi.v`, `PLL/LL/MetaTheory/CutElimination.v`, `PLL/LL/Focusing/TriSystem.v`; `FOLL/` | **Classical**, one-sided, **dyadic** `sig2` (notation `\|-- B ; L`, classical zone `B`, linear zone `L`), with height-indexed variants `sig2h`, with cut `sig2hc`, with two cuts `sig2hcc`, and `sig3`; triadic focused system. Propositional and first-order. | Equivalence of the systems, cut elimination (`sig2hc_then_sig2h : n \|-c B ; L → exists m, m \|-- B ; L`), `strong_consistency`, completeness of focusing. Two-zone but not intuitionistic. | [read: README, constructor headers and theorem names] |
| **Abella: abella-reasoning** (K. Chaudhuri, L. Lima, G. Reis), `github.com/meta-logic/abella-reasoning`; paper draft `clr16-lincut-draft.pdf` ("Formalized Meta-Theory of Sequent Calculi for Substructural Logics") | Classical: one-sided MLL, MALL, MELL, first-order MALL, synthetic (focused) MALL; two-sided **classical** MALL (`two-sided/mall.thm`, `prove : olist → olist → prop`). For exponentials the paper (p. 12) moves "to a dyadic sequent calculus with sequents of the form `⊢ Γ; Δ` where Γ is interpreted as a set", with two cuts (`cut` and `ucut`) and an explicit height bound. | Cut elimination for those marked `o` in `status.txt` (MLL, MALL, MALL+exponentials, first-order MALL, synthetic MALL, two-sided MALL); full LL and the two-sided LJ files are marked incomplete. No intuitionistic linear calculus. | [read: `status.txt`, `two-sided/mall.thm` head, paper p. 12] |
| **Elf/Twelf: Pfenning 1994**, "Structural Cut Elimination in Linear Logic", CMU-CS-94-222, `pfenning94-CMU-CS-94-222.ps` | **Classical** two-sided system LV "very close to Andreoli's dyadic system Σ₂ ... and similar to Girard's LU ... a complete classical analogue of Hodas & Miller's 𝓛", with linear and non-linear zones on both sides and three cut rules. | Admissibility of the three cuts "by three nested structural inductions", cut elimination, implemented in Elf (Appendix A). The introduction says "The seeds for this proof may already be found in [Hod94], where cut elimination is proven for 𝓛, a fragment of intuitionistic linear logic." | [read: abstract, contents, pp. 1–3; text recovered from the PostScript strings, symbols not rendered] |
| **Twelf wiki**, `wiki/pages/linear-logic.elf` in `github.com/standardml/twelf` (also `TEST/crary/substruct/linear.elf`) | A linear **natural deduction / term calculus** with types `-o * & + ! zero top` (`one = ! top`), terms with `bang`/`letb`, a `linear` judgement enforcing single use of linear variables on top of LF's unrestricted hypotheses: in effect a two-kinds-of-hypotheses (DILL-style) natural deduction. | A "Subject Reduction" section follows the typing rules. Not a sequent calculus; no cut elimination. | [read: head of the file and its section headings only] |
| **Isabelle distribution**, `src/Sequents/ILL.thy` (S. Kalvala, V. de Paiva, 1995); paper `kalvala-depaiva95.pdf` "Mechanizing Linear Logic in Isabelle" | One-zone ILL as an object logic of Isabelle's `Sequents`, rules as axioms (`derelict "$F, A, $G \|- C ==> $F, !A, $G \|- C"`, a context-splitting `cut`). | An interactive prover for ILL; no metatheory (cut elimination is cited, not proved: "While Girard has shown that the cut rule can be eliminated from proofs in ILL, in practice it is very useful to have some form of cut"). | [read: paper text; the `.thy` itself was not fetched (redirect)] |
| **Isabelle AFP: "ILL"** (F. Smola, J. Fleuriot), `isa-afp.org/entries/ILL.html`, outline `afp-ill-outline.pdf` | One-zone ILL, `inductive sequent :: 'a ill_prop list ⇒ 'a ill_prop ⇒ bool`, explicit `exchange`, `cut` a primitive rule; deep embedding of propositions, shallow and deep embeddings of deductions. | Derived rules and equivalences; a deep embedding of deductions. No cut-elimination theorem in the outline. | [read: outline text] |
| **Lean: cslib**, `Cslib/Logics/LinearLogic/CLL/` (`Basic.lean`, `CutElimination.lean`, `EtaExpansion.lean`, `MLL.lean`, `PhaseSemantics/Basic.lean`) | **Classical** LL, one-sided, `Sequent Atom` a multiset, rules `ax cut one bot parr tensor oplus₁ oplus₂ with top quest weaken contract bang`. Phase semantics for CLL: `class PhaseSpace (M) extends CommMonoid M` with a distinguished `⊥`, facts, `I := idempotentsIn (1 : Set P)` (strict idempotents in `1`), `bang X := dualFact (X ∩ I)⫠`. | `CutElimination.lean` contains only the definition `CutFreeProof` and two `-- TODO` comments (cut admissibility, cut elimination). `PhaseSemantics/Basic.lean` lists "## TODO - Soundness theorem - Completeness theorem". **No intuitionistic linear logic directory.** | [read: file tree of `main` and the three files, fetched 2026-11-26] |
| **Lean: Mathlib** | No sequent calculus for linear logic: a case-insensitive `grep` for "linear logic", "PhaseSpace" and "sequent calculus" over `Mathlib/` finds only `CategoryTheory/Dialectica/Basic.lean`. | — | [read: local checkout at `fabf563`, 2026-06-15; newer Mathlib not checked] |

Seen only in search-result snippets, **not read**: Power & Webster, "Working with Linear
Logic in Coq" (TPHOLs 1999 emerging trends; Maynooth repository record 6461; the logic
variant not confirmed); `github.com/heades/cut-fill-agda` (Agda, cut elimination for
*full* intuitionistic linear logic FILL, multi-conclusion); G. Allais 2017 and Wood &
Atkey ("A Linear Algebra Approach to Linear Metatheory", arXiv 2005.02247) in Agda;
`reservoir.lean-lang.org/@fushanbobfan/proofnet-ir` (Lean, MLL proof nets); Felty,
Olarte, Xavier, MSCS 2021 (`coq-fll`, focused classical LL as a framework). Laurent's
Yalla paper (`perso.ens-lyon.fr/olivier.laurent/yalla_jar.pdf`) has a related-work
section that was not fetched.

Consequences for the campaign: (1) a Lean 4 mechanisation of two-zone DILL with cut
elimination would not duplicate anything found; (2) the phase-semantic route has a
mechanised precedent for one-zone ILL (Larchey-Wendling) whose design choices
(`K ⊆ J`, closure defined contextually from the deduction relation, no quotient) can be
copied; (3) cslib's CLL phase semantics uses strict idempotents and has neither
soundness nor completeness yet.

---

## Q-E. Places in the literature for results about the two-zone calculus

**Identity expansion (init restricted to atoms).**
- CCP03 itself has `init` on arbitrary propositions, `Γ ; A ⟹ A ; ·` (printed p. 11 =
  file p. 13) **[read, text]**; no theorem restricting it to atoms was found in the
  report (searched the text for "atomic").
- F. Pfenning, "Linear Logic" lecture notes, draft of January 26, 2002
  (`pfenning-linear02.pdf`; printed page = file page − 4), §4.1, **Theorem 4.2
  (Completeness of Atomic Initial Sequents)**, printed p. 71 = file p. 75 **[read,
  text]**: "we can restrict ourselves to initial sequents of the form `Γ; P ⟹ P`, where
  `P` is an atomic proposition. We write `Γ; Δ ⟹⁻ A` for the restricted judgment ...
  Theorem 4.2. If `Γ; Δ ⟹ A` then `Γ; Δ ⟹⁻ A`." Proof by induction on the derivation,
  with an auxiliary induction on the proposition for initial sequents, one case shown
  (`A₁ ⊗ A₂`), "the others ... follow the local expansions".
- Mechanised, one-zone: cslib has a file `CLL/EtaExpansion.lean` (classical; not read);
  Larchey-Wendling's `in_llp_ax` is on arbitrary formulas.

**Disjunction property.** Pfenning's notes, **Theorem 3.12 (Disjunction Property for
Intuitionistic Linear Logic)**, printed p. 60 = file p. 64 **[read, text]**: "If
`·; · ⊢ A ⊕ B true` then either `·; · ⊢ A true` or `·; · ⊢ B true`." Stated for natural
deduction; the proof goes through the cut-free sequent calculus ("there are only two
rules that end with this judgment: ⊕R₁ and ⊕R₂"). Same place: **Theorem 3.11
(Consistency)**, printed p. 59: "`·; · ⊢ 0 true` is not derivable." Not found in CCP03
or Barber.

**Subformula property.** No numbered theorem for the two-zone sequent calculus was
found. Remarks: Pfenning's notes, printed p. 56 = file p. 60 **[read]**: without cut,
"all the remaining rules have the property that the premises contain only instances of
propositions in the conclusion, or parts thereof. This latter property is often called
the subformula property"; printed p. 37 = file p. 41: normal natural deductions "have the
important subformula property". CCP03 printed p. 17 = file p. 19 **[read]** mentions it
for normal natural deductions only. One-zone, classical: LMSS "Corollary A.4 (Subformula
Property)" (the SRI copy numbers it Corollary A.4; statement begins "Any formula in any
cut-free proof of ⊢ ..."; **[read, first line only]**). Mechanised one-zone ILL: Yalla
`isubformula_cutfree`, `isubformula` (Q-D).

**Correspondence `Γ ; Δ ⟹ C` iff `!Γ, Δ ⟹ C` in one-zone ILL.**
- **CCP03, Theorem 7 (JILL as Unitary CLL), printed p. 20 = file p. 22 [read, text]** is
  the sequent-calculus statement, for the campaign's own calculus:
  > 1. If `!Γ, Δ →ILL C` then `Γ ; Δ ⟹ C ; ·`
  > 2. If `!Γ, Δ →ILL ?C` then `Γ ; Δ ⟹ · ; C`
  > 3. If `Γ ; Δ ⟹ C ; ·` then `!Γ, Δ →ILL C`
  > 4. if `Γ ; Δ ⟹ · ; C` then `!Γ, Δ →ILL ?C`.

  Here `→ILL` (printed p. 19 = file p. 21) is the set of sequents of the two-sided
  classical calculus CLL of Figure 3 "that have a derivation consisting entirely of
  unitary sequents — sequents with a single proposition on the right of the arrow", and
  "for these sequents, we allow only the core connectives of JILL, omitting ¬, ⊥, ? and ⅋"
  (items 2 and 4 keep `?` on the right; for the campaign's fragment only 1 and 3 are
  needed). Figure 3 has explicit `!L`, `!R`, `weak!`, `contr!` (names read in the proof
  text on file pp. 22–23). Also printed p. 22 = file p. 24: "`Γ ; Δ ⟹ γ` iff
  `· ; !Γ, Δ ⟹ γ`. This follows by repeated applications of `!L` in one direction and by
  repeated application of `!L⁻¹` (Lem. 6) in the other direction."
- **Barber, ECS-LFCS-96-347 (`barber96.pdf`, printed page = file page), §5, natural
  deduction with terms, connectives `I, ⊸, ⊗, !` only** (p. 3: "A, B ::= Y ∈ Ob(G) | I |
  A ⊸ B | A ⊗ B | !A"; Γ a set, Δ a multiset; additives are "further work", §7.1 p. 50)
  **[read, text]**. Lemma 5.1 (Properties of the Translations), p. 35, for translations
  `Φ : ILL → DILL`, `Ψ_V : DILL → ILL` which are the identity on types:
  > 1. If `Δ ⊢ILL t : A`, then `; Δ ⊢DILL Φ(t) : A`
  > 2. If `x⃗ : Γ; Δ ⊢DILL u : A`, then `x⃗ : !Γ, Δ ⊢ILL Ψ_x⃗(u) : A`
  > 3. If `Δ ⊢ILL t =_A u`, then `; Δ ⊢DILL Φ(t) =_A Φ(u)`
  > 4. If `x⃗ : Γ; Δ ⊢DILL t =_A u`, then `x⃗ : !Γ, Δ ⊢ILL Ψ_x⃗(t) =_A Ψ_x⃗(u)`
  > 5. If `Δ ⊢ILL t : A`, then `Δ ⊢ILL Ψ_⟨⟩(Φ(t)) =_A t`
  > 6. If `; Δ ⊢DILL t : A`, then `; Δ ⊢DILL Φ(Ψ_⟨⟩(t)) =_A t`

  (proved separately as Lemmas 5.1.1, p. 36; 5.1.2, p. 43; 5.1.3, p. 38; 5.1.4, p. 45;
  5.1.5, p. 46; 5.1.6, p. 47), and
  > Theorem 3 (Conservative Extension), p. 35.
  > • `Δ ⊢ILL t =_A u` iff `; Δ ⊢DILL Φ(t) =_A Φ(u)`
  > • `; Δ ⊢DILL t =_A u` iff `Δ ⊢ILL Ψ_⟨⟩(t) =_A Ψ_⟨⟩(u)`

  So Theorem 3 is about **equality of proofs (terms)**, with empty unrestricted zone; the
  provability-level facts are items 1 and 2 of Lemma 5.1. The direction "`!Γ, Δ ⊢ILL A`
  implies `Γ; Δ ⊢DILL A`" is not an item; it follows from item 1 and Lemma 2.3
  (!-Equivalence), p. 5: "In the presence of the cut rules, the two-way proof rule
  `Γ, A; Δ ⊢ B` ⇔ `Γ; !A, Δ ⊢ B` is equivalent in strength to the (!-I), (!-E) pair".
  Cut admissibility in Barber: Lemma 2.1 (Intuitionistic Cut), p. 4, "If `Γ, A; Δ ⊢ B`
  and `Γ; ⊢ A`, then `Γ; Δ ⊢ B` without using cuts", and Lemma 2.2 (Linear Cut), p. 5,
  "If `Γ; Δ₁, A ⊢ B` and `Γ; Δ₂ ⊢ A`, then `Γ; Δ₁, Δ₂ ⊢ B` without using cuts".
- **Hodas & Miller, I&C 110 (1994), author's copy `hodasmiller94-ic.pdf` (printed page =
  file page), Proposition 3, p. 8 [read, text]**, for the two-zone sequent system 𝓛 over
  `⊤, &, ⊸, ⇒, ∀` (Figure 6, p. 8): "Let `B°` be the result of repeatedly replacing all
  occurrences of `C₁ ⇒ C₂` in `B` with `(!C₁) ⊸ C₂` ... Then `Γ; Δ ⊢𝓛 B` if and only if
  `!(Γ°), Δ° ⊢LL B°`", `LL` being their single-conclusion one-zone system of Figure 4
  (p. 7) for `⊤, &, ⊗, ⊸, !, ∀`. Proof: "a simple transformation between proofs in the
  two proof systems". Figure 7 (p. 8) gives the two cuts `cut`, `cut!` for 𝓛.

**A published one-zone sequent calculus for ILL with explicit `!` rules, public source.**
- **Okada & Terui 1998, Appendix A, printed pp. 73–74 = file pp. 17–18** of
  `kokyuroku1023-4.pdf`: exactly `1 ⊗ ⊸ ⊤ 0 & ⊕ !`, sequents `Γ ⊢ C`, rules `!D !C !W !r`
  **[read, rendered]**. This is the best match for the campaign.
- KOT 2006, Figure 1, p. 4 of `kot06-iphase.pdf`: the same plus `⊥` and an optional empty
  succedent **[read, rendered]**.
- CCP03 Figure 3, printed p. 19 = file p. 21 (two-sided CLL; its unitary restriction is
  their ILL) **[read, text only; figure not rendered]**.
- Benton, Bierman, de Paiva, "Term assignment for intuitionistic linear logic
  (preliminary report)", Cambridge TR 262, August 1992 (`bbph92-tr262.pdf`, a scan; the
  cover names three authors), **Figure 1 "(Multiplicative) Intuitionistic Linear Logic",
  printed p. 4 = file p. 6 [read, rendered]**: Identity, Exchange, Cut, `I_L I_R ⊗_L ⊗_R
  ⊸_L ⊸_R`, and `!_{L-1}` (Weakening), `!_{L-2}` (Contraction), `!_{L-3}` (Dereliction),
  `!_R` (Promotion, `!Γ ⊢ A / !Γ ⊢ !A`). **Multiplicative fragment only** ("we shall
  consider only the multiplicative fragment ... the (⊗, ⊸, !)-fragment", printed p. 3).
- Mechanised versions of the same rules: Yalla `ill_def.v`, Larchey-Wendling
  `ill_rules.v` (Q-D).
- Not fetched: Girard & Lafont 1987; Troelstra 1992. LMSS 1992 Appendix B is the
  one-sided classical system (not looked at beyond its mention on journal p. 243).

**Resource management / lazy splitting (input–output contexts).** All three sources
treat the logic-programming fragment (linear hereditary Harrop formulas, goal-directed
proofs), not the full set of left rules:
- Hodas & Miller 1994, §7 "A model of resource consumption", pp. 24–28 of the author's
  copy **[read, text]**: IO-contexts (lists of R-formulas, `!`'ed R-formulas, and `del`),
  the predicate `I{G}O`, Figure 15 (p. 26) "Specification of an interpreter for the
  propositional language", Figure 16 (p. 28) the Prolog implementation, and
  **Proposition 11 (p. 25)**: "Let `I` and `O` be IO-contexts where `O` is a subcontext
  of `I`. Let `I − O` be the pair `⟨Γ, Δ⟩` and let `G` be a goal formula. The proposition
  `I{G}O` is provable if and only if `Γ; Δ ⟶ G` has an 𝓛″-proof." (𝓛″, p. 11–12, adds
  right rules for positive `1, ⊗, ⊕, !, ∃`, Figure 9.)
- Cervesato, Hodas, Pfenning, "Efficient Resource Management for Linear Logic Proof
  Search", version of August 29, 1997 (`chp-erm97.pdf`, 26 pages; the TCS 232 (2000)
  version was not fetched) **[read, text]**: resolution calculus R for LHHF (Figure 1,
  p. 4); RM₁ with judgments `Γ; Δ_I \ Δ_O ⟹ G` (Figure 2, p. 6), **Theorem 3.5
  (Soundness of RM₁ with respect to R), p. 8**: "If `Γ; Δ_I \ Δ_O ⟹ G`, then
  `Γ; (Δ_I − Δ_O) ⟹ G`", **Theorem 3.6 (Completeness), p. 9**: "If `Γ; Δ ⟹ G`, then,
  for every context `Δ_O`, the judgment `Γ; Δ, Δ_O \ Δ_O ⟹ G` is derivable"; RM₂ with a
  slack indicator for `⊤` (Figure 3, p. 11; Theorems 4.3, 4.5, pp. 13–14); RM₃ improving
  `&` (Figure 4, p. 17; Theorems 5.3, 5.5, pp. 19–21).
- Pfenning's notes, **§5.3 "Deterministic Resource Management", printed pp. 96–99 = file
  pp. 100–103 [read, text]**: judgments `Γ; Δ_I \ Δ_O ⟹ A ⇑` and
  `Γ; Δ_I \ Δ_O ; A ⇓ ⟹ P` with Boolean-annotated hypotheses `u:A[1]`, `u:A[0]`;
  **Theorem 5.1 (Soundness of I/O Resource Management)**, printed p. 98: "1. If
  `Γ; Δ_I \ Δ_O ⟹ A ⇑` then `Δ_I − Δ_O = Δ` and `Γ; Δ ⟹ A ⇑`. 2. If
  `Γ; Δ_I \ Δ_O ; A ⇓ ⟹ P` then `Δ_I − Δ_O = Δ` and `Γ; Δ; A ⇓ ⟹ P`"; **Theorem 5.2
  (Completeness)**, printed p. 99: "1. If `Γ; Δ ⟹ A ⇑` then
  `Γ; Δ[1], Δ_O \ Δ[0], Δ_O ⟹ A ⇑` for any `Δ_O`. 2. ..." Both proofs are one line with a
  footnote "[check for lemmas and write out some cases]": **the notes do not give the
  proofs.** The notes (printed p. 95 = file p. 99) point to Boolean constraints [HP97]
  (Harland & Pym) for the general case; not followed up.

No source was found (in this search) that gives an input–output system, with soundness
and completeness, for the full two-zone sequent calculus with all left rules (`⊗L`,
`⊕L`, `!L`, `⊸L` on arbitrary goals).

---

## Files fetched

All into the scratch `src/` folder named at the top; nothing was run from it. Sizes in
bytes as stored.

| File | URL | Bytes |
|---|---|---|
| `kot06-iphase.pdf` | https://www.kurims.kyoto-u.ac.jp/~terui/iphasemscsfinal.pdf | 291251 |
| `kokyuroku1023-4.pdf` | https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1023-4.pdf | 1646962 |
| `lafont97-model.ps` | https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/model.ps | 99405 |
| `lmss92-apal.pdf` | https://curien.galene.org/ECI2023/Lincoln%2B-decision-LL.pdf | 5200610 |
| `lmss-sri94.pdf` | https://www.csl.sri.com/papers/lmss90/lmss90.pdf | 562323 |
| `larchey18-slides.pdf` | https://members.loria.fr/DLarchey/files/papers/cut_elim_2018.pdf | 207178 |
| `arxiv2607.20187.pdf` | https://arxiv.org/pdf/2607.20187 | 300255 |
| `clr16-lincut-draft.pdf` | https://www.lix.polytechnique.fr/~kaustuv/papers/draft16lincut.pdf | 327674 |
| `kalvala-depaiva95.pdf` | https://www.cl.cam.ac.uk/~lcp/papers/Workshop/papers/kalvala-linear.pdf | 140824 |
| `afp-ill-outline.pdf` | https://www.isa-afp.org/browser_info/current/AFP/ILL/outline.pdf | 228970 |
| `pfenning94-CMU-CS-94-222.ps` | http://reports-archive.adm.cs.cmu.edu/anon/1994/CMU-CS-94-222.ps | 323562 |
| `hodasmiller94-ic.pdf` | https://www.lix.polytechnique.fr/~dale/papers/ic94.pdf | 272565 |
| `chp-erm97.pdf` | https://www.cs.cmu.edu/~fp/papers/erm97.pdf | 317841 |
| `bbph92-tr262.pdf` | https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-262.pdf | 1903434 |

Already present (not fetched by this survey): `ccp03.pdf` (272702), `barber96.pdf`
(682508), `pfenning-linear02.pdf` (866345), `cairespfenning10.pdf` (234366), with their
`.txt` files.

Fetched as text into the scratch folder next to `src/` (subfolder `gh/`), not papers:
source files and READMEs from `raw.githubusercontent.com` and file trees from
`api.github.com` for `DmxLarchey/Coq-Phase-Semantics`, `olaure01/yalla`,
`leanprover/cslib`, `meta-logic/coq-ll`, `meta-logic/abella-reasoning`,
`standardml/twelf`; the publication page
`https://www.kurims.kyoto-u.ac.jp/~terui/pub.html`; Lafont's publication page
`https://www.i2m.univ-amu.fr/perso/yves.lafont/publications.html`; the Cambridge Core
abstract page of Okada–Terui 1999; four CORE API search results.

Fetched and deleted: a second copy of the Kôkyûroku paper from
`repository.kulib.kyoto-u.ac.jp` (same paper as `kokyuroku1023-4.pdf`);
`https://www.cs.cmu.edu/~fp/papers/tcs00.pdf` (a different paper, Colby et al.); six
HTML refusal pages saved under `.pdf` names (see below).

Reading notes: the two PostScript files could not be rendered (running a PostScript
interpreter on a downloaded file was refused in this session), so their text was
recovered by extracting the string constants with a small script kept outside `src/`;
symbols in them were decoded from font codes and are flagged where used.

## Could not get

- **M. Okada, "Phase semantic cut-elimination and normalization proofs of first- and
  higher-order linear logic", TCS 227 (1999) 333–396.** ScienceDirect
  (`/science/article/pii/S0304397599000584/pdf`) and CORE
  (`core.ac.uk/download/pdf/186658059.pdf`) both returned HTTP 403 to an automated
  client. No author's copy found.
- **M. Okada, "A uniform semantic proof for cut-elimination and completeness of various
  first and higher order logics", TCS 281 (2002) 471–498.** Same: ScienceDirect
  (`pii/S030439750200024X`) and CORE (`81134806`) returned 403. Partly covered at second
  hand by A.6.
- **M. Okada, "Phase semantics for higher order completeness, cut-elimination and
  normalization proofs (extended abstract)", ENTCS 3 (1996)** (the "Okada 1996" that KOT
  2006 cites for Lemma 2.10 and Remark 2.11): CORE `82372511` returned 403.
- **Okada & Terui, JSL 64(2) (1999) 790–802.** Only the abstract (Cambridge Core page).
  Terui's publication page links JSTOR only; CORE `1045090057` returned 403.
- **Lafont 1997 in rendered form.** Only the author's PostScript, read as extracted text.
- **Cervesato, Hodas, Pfenning, TCS 232 (2000)**: the 1997 author's version was read
  instead.
- Not attempted (time): Abrusci 1990; Ono 1993; Troelstra, *Lectures on Linear Logic*
  (1992), ch. 8 (a book, no public copy known to me); Girard 1995 ("Linear logic: its
  syntax and semantics"); Girard & Lafont 1987; Hodas's 1994 thesis; Power & Webster
  1999; Laurent's Yalla paper; Isabelle's `src/Sequents/ILL.thy` (the raw-file URL
  redirected and was not followed up).

Report finished 2026-11-26 (times from `date`: started 14:49 GMT).
