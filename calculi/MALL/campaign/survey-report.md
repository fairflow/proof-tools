*Written by an agent of the operator (a fresh agent, briefed to fetch the sources and survey the mechanisations), 2026-11-26, and copied here unchanged. `S` in it is the session's scratchpad: the files it names are not in the repository. What the plan relies on from it is in `plan.md`, Q2, Q3 and Q5.*

# MALL campaign: literature files and survey of mechanisations

Written 2026-11-26 (about 09:50 to 10:05 GMT, from `date`). Scratch folder S =
`/private/tmp/claude-501/-Users-matthew-Lean-Sources-proof-tools--claude-worktrees-ecstatic-benz-bee260/8955b83d-a143-40ea-aa9c-61f6985d6604/scratchpad`

Conventions in this report. "READ" means I read it in the named file at the named line or page.
"INFERRED" means it is my own reasoning and is not stated in the source. Paper definitions are
restated as formulas rather than copied out at length; page numbers are given so the wording can
be checked in the PDF. Code excerpts from the open-source repositories (Yalla: LGPL-3; cslib:
Apache-2.0) are quoted with file and line.

Nothing was written into any git repository. Nothing was executed from inside the download
folders. The one conversion (PostScript to PDF) was run by Ghostscript 10.07.1 with `-dSAFER`,
from a different working directory, with the file paths passed as arguments.

---------------------------------------------------------------------------------------------

## Part A. Files

| # | Paper | Saved as (under S) | Source URL | Bytes | Pages | Text |
|---|-------|--------------------|-----------|-------|-------|------|
| 1 | Lafont, FMP | `src/lafont/fmp.pdf` (converted) and `src/lafont/model.ps` (original) | https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/model.ps | pdf 138260; ps 99405 | 6 | pdftotext extracts prose; the mathematical symbols are lost (Type 3 dvips fonts), so formulas must be read from the page image |
| 2 | LMSS, journal version | `src/lmss/lmss.pdf` | https://curien.galene.org/ECI2023/Lincoln%2B-decision-LL.pdf | 5200610 | 73 (= pp. 239-311) | A scan with an OCR text layer (Acrobat Capture). pdftotext works; prose is good, formulas and some letters are garbled |
| 2b | LMSS, SRI report version dated 13 Sept 1994 | `src/lmss/lmss-sri-tr.pdf` | https://www.csl.sri.com/papers/lmss90/lmss90.pdf | 562323 | 89 | Born-digital (dvi), clean text |
| 4 | Hodas and Miller | `src/hodas-miller/hm.pdf` | https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/ic94.pdf | 272565 | 32 | Born-digital, clean text. Author's copy, not the journal's pagination |
| 5 | Cervesato, Hodas, Pfenning | `src/chp/chp.pdf` | https://www.cs.cmu.edu/~fp/papers/erm97.pdf | 317841 | 26 | Born-digital, clean text. This is the preprint dated 29 August 1997, linked from Pfenning's publication list under the TCS 2000 entry; it is not the published TCS typesetting (TCS 232 pp. 133-163 is 31 pages) |
| 3 | Okada, TCS 227 | NOT OBTAINED | see below | | | |
| - | Okada and Terui, "Completeness proofs for linear logic based on the proof search method" (RIMS Kokyuroku 1023, 1998, pp. 57-75) | `src/okada/kurims-1023-4.pdf` | https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1023-4.pdf | 1646962 | 19 | Scan with OCR text, poor quality. This is a DIFFERENT paper, kept only because it is on the same subject |

Every file in the table was checked with `file`; each is a real PDF (or PostScript for model.ps).

Notes on the individual items.

1. **Lafont.** His publications page, https://www.i2m.univ-amu.fr/perso/yves.lafont/publications.html,
   lists the JSL paper with a single link `pub/model.ps` (READ: the page's HTML, line 264-270 of my
   saved copy `wk/lafont-pubs.html`). That file is 6 pages; the JSL article is pp. 1202-1208
   (7 pages). So what we have is the author's version. I did not compare it with the published
   text. All page numbers for Lafont below are pages 1-6 of this file, not JSL pages.
   The two HTML error pages that were already sitting in `src/lafont/fmp.pdf` and
   `src/lmss/lmss.pdf` when I started have been overwritten by the real files.
2. **LMSS.** The curien.galene.org copy carries the journal header "Annals of Pure and Applied
   Logic 56 (1992) 239-311" on its first page and has the journal's page numbers. The SRI copy is
   the same paper retypeset (title page dated September 13, 1994); its theorem numbering was not
   compared with the journal's.
3. **Okada (not obtained).** Tried: (a) the Elsevier open-archive PDF
   `https://www.sciencedirect.com/science/article/pii/S0304397599000584/pdf` (HTTP 403 to curl;
   Unpaywall names this as the only open location and reports no repository copy);
   (b) CORE (`core.ac.uk/outputs/186658059`, 403, and its API reports no download URL);
   (c) one web search, which found only the publisher page and the Okada-Terui Kokyuroku paper
   above. The article is in Elsevier's open archive, so a browser will fetch it from
   https://doi.org/10.1016/S0304-3975(99)00058-4 .
5. **CHP.** My first attempt (`.../~fp/papers/tcs00.pdf`) returned a different paper (Colby et al.,
   "Automated techniques for provably safe mobile code"); that file was deleted and replaced.

---------------------------------------------------------------------------------------------

## Part B. What the papers say

### B.1 Lafont, "The finite model property for various fragments of linear logic"

All of B.1 is READ from the page images of `src/lafont/fmp.pdf` unless marked INFERRED.

#### (iii) The calculus (Section 1, p. 1)

* Formulas: multiplicatives `A ⅋ B`, `A ⊗ B`, `⊥`, `1`; additives `A & B`, `A ⊕ B`, `⊤`, `0`;
  exponentials `?A`, `!A`.
* Negation is not a connective. It is given on positive atoms and extended by `A⊥⊥ = A` and
  De Morgan: `(A ⅋ B)⊥ = A⊥ ⊗ B⊥`, `⊥⊥ = 1`, `(A & B)⊥ = A⊥ ⊕ B⊥`, `⊤⊥ = 0`, `(?A)⊥ = !A⊥`.
  `A ⊸ B` abbreviates `A⊥ ⅋ B`.
* Sequents `Γ, Δ` are **multisets** of formulas; exchange is implicit. One-sided.
* Identity `⊢ A, A⊥` for an arbitrary formula `A` (not only atoms). Cut: from `⊢ A, Γ` and
  `⊢ A⊥, Δ` infer `⊢ Γ, Δ`.
* Logical rules for MALL:

  ```
  ⊢ A, B, Γ          ⊢ A, Γ    ⊢ B, Δ          ⊢ Γ
  -----------        ------------------       --------        -----
  ⊢ A ⅋ B, Γ           ⊢ A ⊗ B, Γ, Δ          ⊢ ⊥, Γ          ⊢ 1

  ⊢ A, Γ   ⊢ B, Γ        ⊢ A, Γ            ⊢ B, Γ
  ----------------     ------------      ------------       --------
    ⊢ A & B, Γ          ⊢ A ⊕ B, Γ        ⊢ A ⊕ B, Γ         ⊢ ⊤, Γ
  ```

  No rule for `0`. "Cut-free MALL" is this system without cut. (The exponential rules are
  dereliction, contraction, weakening, promotion; not needed for MALL.)

#### Phase spaces and models (Section 2, p. 2)

For a commutative monoid `M` and `X, Y ⊆ M`:

    XY = { xy ; x ∈ X, y ∈ Y }            X ⊸ Y = { z ∈ M ; xz ∈ Y for all x ∈ X }

* A *phase space* is a commutative monoid `M` with a chosen subset `⊥•`. `X⊥ := X ⊸ ⊥•`.
* `X ⊆ X⊥⊥`; `X ⊆ Y` gives `Y⊥ ⊆ X⊥`. A *fact* is an `X` with `X⊥⊥ = X`, equivalently `X = Y⊥`
  for some `Y`. `⊥• = {1}⊥` is a fact; `X ⊸ Y` is a fact when `Y` is; intersections of facts are
  facts; `X⊥⊥` is the least fact containing `X`.
* Constants and connectives on facts:

      1• = ⊥•⊥ = {1}⊥⊥       ⊤• = M       0• = ⊤•⊥ = ∅⊥⊥
      X ⅋ Y = (X⊥ Y⊥)⊥                  X ⊗ Y = (X⊥ ⅋ Y⊥)⊥ = (XY)⊥⊥
      X & Y = X ∩ Y                     X ⊕ Y = (X⊥ & Y⊥)⊥ = (X ∪ Y)⊥⊥

  and `X ⊸ Y = X⊥ ⅋ Y` when `Y` is a fact.
* A *phase model* is a phase space with an *interpretation* sending each positive atom `α` to a
  fact `α•`. `A•` is defined by induction with the clauses above. `M` *satisfies* `A` when
  `1 ∈ A•`.
* INFERRED: the paper does not write the clause for a negative atom; since negation is defined
  syntactically, it must be `(α⊥)• = (α•)⊥`, and the lemma `(A⊥)• = (A•)⊥` is then needed for
  soundness of identity and cut. The proof of Lemma 1 uses exactly this clause in its second
  bullet.

#### The syntactical model and Okada's lemma (p. 2)

`MALL•` is the phase model with

* monoid: the free commutative monoid on all MALL formulas, that is, all sequents, with product
  `Γ · Δ = Γ, Δ` (multiset union) and unit the empty sequent;
* `⊥•` = the set of sequents provable in **cut-free** MALL;
* `α• = {α}⊥` for each positive atom `α`.

So `{A}⊥ = { Γ ; ⊢ A, Γ is cut-free provable }`.

**Lemma 1 (attributed to Okada), p. 2.** For every MALL formula `A`:

    A•  ⊆  {A}⊥        in MALL•.

Hence any formula satisfied by `MALL•` is cut-free provable (take the empty sequent in `A•`).
Proof by induction on `A`, never using cut:

* `α• = {α}⊥` by definition; `(α⊥)• = {α}⊥⊥ ⊆ {α⊥}⊥` because `α ∈ {α⊥}⊥` by the identity axiom
  (only the atomic instance of identity is used);
* `(A ⅋ B)• = (A•⊥ B•⊥)⊥ ⊆ ({A}⊥⊥ {B}⊥⊥)⊥ = ({A}{B})⊥ ⊆ {A ⅋ B}⊥` by the ⅋ rule;
* `(A ⊗ B)• = (A• B•)⊥⊥ ⊆ ({A}⊥ {B}⊥)⊥⊥ ⊆ {A ⊗ B}⊥` since `{A}⊥{B}⊥ ⊆ {A ⊗ B}⊥` by the ⊗ rule;
* `(A & B)• = A• ∩ B• ⊆ {A}⊥ ∩ {B}⊥ ⊆ {A & B}⊥` by the & rule;
* `(A ⊕ B)• = (A• ∪ B•)⊥⊥ ⊆ ({A}⊥ ∪ {B}⊥)⊥⊥ ⊆ {A ⊕ B}⊥` by the ⊕ rules;
* `⊥• ⊆ {⊥}⊥` by the ⊥ rule; `1• = ⊥•⊥ ⊆ {1}⊥` since `1 ∈ ⊥•` by the 1 rule; `⊤• ⊆ {⊤}⊥` by the
  ⊤ rule; `0• = M⊥ ⊆ {0}⊥`.

INFERRED (a detail a formalisation needs): the step `({A}⊥⊥ {B}⊥⊥)⊥ = ({A}{B})⊥` is the general
identity `(X⊥⊥ Y⊥⊥)⊥ = (XY)⊥`, and the ⊗ and ⊕ steps use that `{C}⊥` is a fact, so
`Z ⊆ {C}⊥` gives `Z⊥⊥ ⊆ {C}⊥`.

**Theorem 1, p. 2.** For a MALL formula `A` the following are equivalent:
(1) `A` is provable in MALL; (2) `A` is satisfied by all phase models; (3) `A` is satisfied by
`MALL•`; (4) `A` is provable in cut-free MALL.
Proof: (2)⇒(3) and (4)⇒(1) trivial; (1)⇒(2) soundness by induction on proofs (referred to
Girard 1987, not written out); (3)⇒(4) is Lemma 1. This one theorem is soundness, completeness
and cut elimination together.

#### (ii) The finite model (p. 3)

Step 1, the subformula model. `MALL[A]` is MALL restricted to the subformulas of `A`.
`MALL•[A]` is:

* monoid: the free commutative monoid on the subformulas of `A`;
* `⊥•` = sequents provable in cut-free `MALL[A]`;
* `α• = {α}⊥` if `α` occurs in `A`; `α• = {α⊥}⊥⊥` if `α⊥` occurs in `A` but `α` does not.

Then `A` is provable in MALL iff `MALL•[A]` satisfies `A`. This gives the subformula property
and completeness of finitely generated phase semantics.

Step 2, logical congruences. A *logical congruence* on a phase model `M` is a monoid congruence
`∼` such that `⊥•` is closed under `∼` (`x ∈ ⊥•` and `x ∼ y` give `y ∈ ⊥•`). The finest is
equality; the coarsest is `x ≡ y :⇔ {x}⊥ = {y}⊥`. For a logical congruence all facts are
`∼`-closed, so `M/∼` is a phase model (with `π : M → M/∼`, and `⊥•`, `α•` the images).

**Lemma 2, p. 3.** For every MALL formula `A`:  `π⁻¹(A•_∼) = A•`. So `M/∼` satisfies the same
formulas as `M`. Proof: true for `⊥•` and atoms by construction; since `π` is a surjective
morphism, `π⁻¹(X ⊸ Y) = π⁻¹(X) ⊸ π⁻¹(Y)` for all `X, Y ⊆ M/∼`; then induction on `A`.

Step 3, the ordering. `⊑` is the smallest preorder on sequents such that

    Γ ⊑ Γ, Δ        A, B, Γ ⊑ A ⅋ B, Γ        A, Γ ⊑ A ∗ B, Γ        B, Γ ⊑ A ∗ B, Γ

where `∗` is any of `⊗`, `&`, `⊕`. The paper asserts (without proof, "easy to see") that `⊑` is
a partial order and that for each formula `A` the set `{ Γ ; Γ ⊑ A }` is finite.

Step 4, the model. `MALL⟨A⟩` is `MALL[A]` **extended with an axiom `⊢ Γ` for every sequent `Γ`
with `Γ ⋢ A`**. `MALL•⟨A⟩` is the corresponding syntactical model (same monoid and valuation as
`MALL•[A]`, with `⊥•` = cut-free provable in `MALL⟨A⟩`). The relation `∼_A` identifies all
sequents `Γ` with `Γ ⋢ A` and nothing else:

    Γ ∼_A Δ   :⇔   Γ = Δ   or   (Γ ⋢ A and Δ ⋢ A).

The paper asserts that `∼_A` is a logical congruence on `MALL•⟨A⟩` and that the quotient
`MALL•⟨A⟩/∼_A` is finite.

**(i) Theorem 2, p. 3 (the finite model property for MALL).** For a MALL formula `A` the
following are equivalent:

1. `A` is provable in MALL;
2. `A` is satisfied by all **finite** phase models;
3. `A` is satisfied by `MALL•⟨A⟩/∼_A`;
4. `A` is satisfied by `MALL•⟨A⟩`;
5. `A` is provable in cut-free `MALL⟨A⟩`.

Proof as given: (1)⇒(2) by Theorem 1; (2)⇒(3) trivial (the quotient is finite); (3)⇒(4) by
Lemma 2; (4)⇒(5) by the analogue of Lemma 1 for `MALL⟨A⟩`; (5)⇒(1) because `⊑` was defined so
that the premises of a logical rule are always below its conclusion.

The paper's sentence before the theorem says that it gives the completeness of the finite phase
semantics for MALL. The statement is about a single formula `A` (equivalently a sequent, via ⅋).

INFERRED: the details a formalisation has to supply, none of them written in the paper.

* *Why `{Γ ; Γ ⊑ A}` is finite.* Each generating step of `⊑`, read downwards, deletes formulas or
  replaces one formula by one or two of its immediate subformulas. So `Γ ⊑ A` forces `Γ` to be a
  multiset of subformulas of `A` whose total symbol count is at most that of `A`. A sharper
  description: `Γ` uses each subformula *occurrence* of `A` at most once, and never two
  occurrences one of which lies inside the other or which are separated by `⊗`, `&` or `⊕`.
* *Why `∼_A` is a congruence.* If `Γ ⋢ A` then `Γ, Σ ⋢ A` for every `Σ`, because
  `Γ ⊑ Γ, Σ` and `⊑` is transitive. So the set `I = {Γ ; Γ ⋢ A}` is a monoid ideal, and `∼_A` is
  the Rees congruence of `I`. The quotient is `{Γ ; Γ ⊑ A} ∪ {∞}` with
  `Γ · Δ = Γ, Δ` if that is `⊑ A`, and `∞` otherwise. Its size is `|{Γ ; Γ ⊑ A}| + 1`.
  This Rees-quotient presentation avoids a `Quotient` type in Lean: the carrier can be
  `Option {Γ // Γ ⊑ A}`.
* *Why it is logical.* Every `Γ ∈ I` is an axiom of `MALL⟨A⟩`, so `I ⊆ ⊥•`, and `⊥•` is closed
  under `∼_A`. In the quotient, `⊥•` is `{∞} ∪ {Γ ⊑ A ; Γ cut-free provable in MALL⟨A⟩}`.
* *(5)⇒(1).* In a cut-free `MALL⟨A⟩` proof of `⊢ A`, every sequent is `⊑ A` (induction from the
  root: for each rule, each premise is `⊑` the conclusion; for ⊗ use
  `A, Γ ⊑ A ⊗ B, Γ ⊑ A ⊗ B, Γ, Δ`; for ⊥ use `Γ ⊑ ⊥, Γ`). The added axioms all have
  `Γ ⋢ A`, so none is used, and the proof is a cut-free MALL proof. In particular, for
  `Γ ⊑ A`, `Γ` is cut-free provable in `MALL⟨A⟩` iff it is cut-free provable in MALL. So the
  finite model can be described with no reference to `MALL⟨A⟩` at all:
  carrier `Option {Γ // Γ ⊑ A}`, `⊥• = {none} ∪ {some Γ ; ⊢ Γ cut-free in MALL}`.
* *The analogue of Lemma 1 for `MALL⟨A⟩`.* The induction runs over subformulas of `A` only. The
  atom case needs `α ∈ {α⊥}⊥`, i.e. `⊢ α, α⊥` in `MALL⟨A⟩`, only when both `α` and `α⊥` occur in
  `A`; then it is an identity axiom. When only `α⊥` occurs, the valuation `α• = {α⊥}⊥⊥` makes
  `(α⊥)• = {α⊥}⊥⊥⊥ = {α⊥}⊥` hold outright. Atoms occurring in neither polarity can be sent to
  any fact.
* *Decidability does not need the model.* The finite model property gives a semi-decision
  procedure for non-provability; together with proof search it gives decidability, but for MALL
  cut-free proof search already terminates (LMSS Theorem 2.2). The paper presents the MALL
  result as a finite model property, and the "new proof of decidability" claim is made for
  affine logic LLW (Theorem 4, p. 5), not for MALL.
* The size of the finite model is not stated in the paper.

Other results in the paper, for orientation: Lemma 3 (Okada's lemma for full LL with enriched
phase spaces, p. 4); Theorem 3 (finite phase semantics is NOT complete for MELL, with the
formula `!a ⊗ !(a ⊗ b) ⊗ !(a ⊗ b ⊸ 1) ⊸ b`, p. 4); Lemma 4 (finitely generated free commutative
monoids are noetherian, i.e. Dickson's lemma, p. 5); Lemma 5 and Theorem 4 (finite model
property for affine logic LLW, p. 5), where the quotient is by the coarsest logical congruence
`≡` rather than by `∼_A`.

### B.2 LMSS, "Decision problems for propositional linear logic"

READ from the OCR text of `src/lmss/lmss.pdf` (journal pagination). The calculus is one-sided,
negation defined, literals in positive/negative pairs (p. 243); rules in Appendix B.

* **Theorem 2.1 (p. 244):** any sequent provable in MALL is provable without cut. Proof: by
  cut elimination for full linear logic (Theorem A.3, p. 307) and the subformula property
  (Corollary A.4, p. 308), a cut-free LL proof of a MALL sequent is a MALL proof.
* **Theorem 2.2 (Section 2.1, pp. 244-245):** provability in MALL of a given sequent can be
  decided by a polynomial-space bounded Turing machine.
* **Theorem 2.12 (p. 259):** "MALL provability is PSPACE-complete." It follows from Theorem 2.2
  and the hardness reduction from QBF validity (Lemma 2.11 and the log-space encoding).

The reason for membership (proof of Theorem 2.2, restated): by Theorem 2.1 a provable sequent has
a cut-free proof. In a cut-free MALL proof every rule has at most two premises and each premise
is strictly smaller than its conclusion, so the depth of the proof tree is at most linear in the
size of the end sequent. An alternating Turing machine guesses and checks such a proof in linear
time (existential branching to choose a rule instance, universal branching for the two premises).
Alternatively, without alternation: a nondeterministic machine explores the proof depth-first;
the stack holds at most linearly many sequents, each no larger than the end sequent, giving a
quadratic space bound. Decidability itself is just termination of backward cut-free proof search
under the size measure.

INFERRED: for a Lean decision procedure the measure is the total number of connective and
constant occurrences in the sequent (each MALL rule read upwards removes one), and the finite
branching is the choice of principal formula, the choice of ⊕ disjunct, and the 2^|Γ| splits
of the context at ⊗.

---------------------------------------------------------------------------------------------

## Part C. Existing mechanisations

### C.1 Yalla (Olivier Laurent, Rocq)

Cloned read-only to `S/src/mech/yalla/repo`, commit `a138437625f5bb39221cd6171b7dc464e15bbf8b`
(13 April 2026). Release notes: version 2.1.0, tested with Rocq 9.2, needs OLlibs 2.1.1.
Licence LGPL-3. All of the following is READ at the lines given (paths relative to
`repo/yalla/`).

* **Formulas** (`formulas.v:22-28`): negation is NOT a constructor. There are positive and
  negative atoms, `var` and `covar`, over a `DecType` of atoms:

  ```coq
  Inductive formula :=
  | var (_ : atom) | covar (_ : atom)
  | one | bot
  | tens (_ _ : formula) | parr (_ _ : formula)
  | zero | top
  | aplus (_ _ : formula) | awith (_ _ : formula)
  | oc (_ : formula) | wn (_ : formula).
  ```

  `dual` is a `Fixpoint` (`formulas.v:110-123`). It reverses the order under the
  multiplicatives, `dual (tens A B) = parr (dual B) (dual A)`, so that it also fits the cyclic
  (non-commutative) case. `bidual : dual (dual A) = A` (`formulas.v:125`).
* **Sequents** are `list formula`, with an **explicit exchange rule** carrying a permutation
  hypothesis in `Type`. The system is parametrised by a record (`ll_def.v:60-64`):

  ```coq
  Record pfrag := mk_pfrag {
    pcut : formula -> bool;
    pgax : { ptypgax : Type & ptypgax -> list formula };
    pmix : nat -> bool;
    pperm : bool }.
  ```

  (which cut formulas are allowed, a family of extra axioms, which n-ary mix rules, and whether
  exchange is arbitrary or cyclic permutation).
* **The proof predicate** (`ll_def.v:185-203`), in `Type`:

  ```coq
  Inductive ll P : list formula -> Type :=
  | ax_r X : ll P (covar X :: var X :: nil)
  | ex_r l1 l2 : ll P l1 -> PCPermutationT (pperm P) l1 l2 -> ll P l2
  | ex_wn_r l1 lw lw' l2 : ll P (l1 ++ map wn lw ++ l2) -> PermutationT lw lw' -> ll P (l1 ++ map wn lw' ++ l2)
  | mix_r L (f : pmix P (length L)) : ForallT (ll P) L -> ll P (concat L)
  | one_r : ll P (one :: nil)
  | bot_r l : ll P l -> ll P (bot :: l)
  | tens_r A B l1 l2 : ll P (A :: l1) -> ll P (B :: l2) -> ll P (tens A B :: l2 ++ l1)
  | parr_r A B l : ll P (A :: B :: l) -> ll P (parr A B :: l)
  | top_r l : ll P (top :: l)
  | plus_r1 A B l : ll P (A :: l) -> ll P (aplus A B :: l)
  | plus_r2 A B l : ll P (A :: l) -> ll P (aplus B A :: l)
  | with_r A B l : ll P (A :: l) -> ll P (B :: l) -> ll P (awith A B :: l)
  | oc_r A l : ll P (A :: map wn l) -> ll P (oc A :: map wn l)
  | de_r A l : ll P (A :: l) -> ll P (wn A :: l)
  | wk_r A l : ll P l -> ll P (wn A :: l)
  | co_r A l : ll P (wn A :: wn A :: l) -> ll P (wn A :: l)
  | cut_r A (f : pcut P A = true) l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
  | gax_r a : ll P (projT2 (pgax P) a).
  ```

  Points to note: the identity axiom is **atomic** (`ax_r`), and the general one is a lemma,
  `ax_exp P A : ll P (A :: dual A :: nil)` (`ll_def.v:1207`). The principal formula is always
  at the head of the list. The **tensor context split** is written by concatenation with the
  two contexts in reversed order, `tens A B :: l2 ++ l1`, again for the cyclic case; cut is
  written the same way. There is no rule for `zero`. Rules are stated with a shared context
  for `with_r`.
* **Type or Prop:** proofs are in `Type` (so proof size and proof transformations are
  definable). `mell_Prop.v` shows a `Prop`-valued interface (`mell_Prop.v:76`), and
  `mell_mset.v`/`mell_msetoid.v` show multiset-based interfaces with no exchange rule
  (`mell_mset.v:115`, cut at `:417`).
* **Proof size** `psize` (`ll_def.v:465-478`): 1 + the sum over premises, except `with_r`, where
  it is 1 + the **max** of the two premises; exchange counts 1.
* **Cut elimination** (`ll_cut.v`). The central lemma is

  ```coq
  Lemma cut_r_gax A l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).   (* :345 *)
  ```

  under a section hypothesis that the extra axioms are closed under cut. It is proved by a
  generalised statement with the cut formula in the middle of the second sequent,
  `ll P (dual A :: l0) -> ll P (l1 ++ A :: l2) -> ll P (l1 ++ l0 ++ l2)`, by **nested
  well-founded induction: outer on `c = fsize A` (size of the cut formula), inner on
  `s = psize pi1 + psize pi2` (sum of the sizes of the two proofs)**, both by `lt_wf_rect`
  (`ll_cut.v:347-360`). The `oc`/`wn` case goes through a separate substitution lemma
  (`substitution_oc`, `:121`) and `cut_oc_comm` (`:22`). The statements are admissibility
  statements:

  ```coq
  Lemma cut_admissible (Hgax_at : atomic_ax P) (Hgax_cut : cut_closed P) l : ll P l -> ll (cutrm_pfrag P) l.   (* :1588 *)
  Lemma cut_r_axfree (P_axfree : no_ax P) A l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1). (* :1606 *)
  Lemma cut_admissible_axfree (P_axfree : no_ax P) l : ll P l -> ll (cutrm_pfrag P) l.                         (* :1611 *)
  ```

  `ll_cut.v` is 1614 lines. For standard LL: `pfrag_ll` (no cut, no axioms, no mix, full
  permutation), `ll_ll := ll pfrag_ll`, `cut_ll_r`, `cut_ll_admissible`
  (`ll_fragments.v:359-367`).
* **Consequences proved** (`ll_prop.v`): consistency (`:20`, `:37`); `fragment FS` = a set of
  formulas closed under subformulas (`:61`); `conservativity` of LL over any fragment for
  cut-free proofs (`:64`); `subformula_cutfree` (`:93`); `cut_admissible_fragment_axfree`
  (`:118`); `subformula` (`:129`); a deduction theorem (`:139` on). Reversibility lemmas
  `bot_rev`, `parr_rev`, `with_rev1/2`, `oc_rev`, `one_rev`, `zero_rev`, `tens_rev`, `plus_rev`
  in `ll_def.v:616-1040`.
* **Focusing** (`llfoc.v`, `llfoc_triadic.v`, `nn_foc.v`): `Lemma focusing l : ll_ll l -> llFoc l None`
  (`llfoc.v:1644`), soundness `llFoc_to_ll` (`:1555`), and Andreoli's triadic system.
* **MALL specifically: nothing.** `grep -i` for `mall`, `phase`, `decidab`, `finite model` over
  all `.v` and `.md` files finds only "decidability of equality on formulas" in the release
  notes. There is no MALL fragment file, no phase semantics, no finite model property and no
  decidability result. INFERRED: MALL cut elimination, the subformula property and focusing for
  MALL follow from the general results by taking `FS` = exponential-free formulas in
  `cut_admissible_fragment_axfree` / `conservativity`, but no file does this.
* `microyalla/` holds a cut-down kernel version (`microll.v`, `nanoll.v`); not examined.
* `ll_smp.v:91-105` gives the plain standard system as an interface example: lists,
  `ex_r l1 l2 : ll l1 -> PermutationT l1 l2 -> ll l2`, tensor as `tens A B :: l1 ++ l2`, atomic
  axiom, no cut constructor; `ax_gen_r` and `cut_r` are imported from the library (`:167-181`).

### C.2 cslib (Lean 4)

Cloned read-only to `S/src/mech/cslib/repo`, commit `907f9348c282243a0bb7e47a6661d6d6174dd433`
(26 November 2026). Toolchain `leanprover/lean4:v4.37.0-rc1`; Mathlib at rev
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (input rev `v4.37.0-rc1`) (READ: `lean-toolchain`,
`lake-manifest.json`). Classical linear logic IS present, in
`Cslib/Logics/LinearLogic/CLL/`:

| File | Lines | Authors (file header) |
|------|-------|-----------------------|
| `Basic.lean` | 605 | Fabrizio Montesi |
| `CutElimination.lean` | 34 | Fabrizio Montesi |
| `EtaExpansion.lean` | 133 | (not read) |
| `MLL.lean` | 204 | (not read) |
| `PhaseSemantics/Basic.lean` | 660 | Tanner Duve, Bhavik Mehta |

No `sorry` in any of the five files (grep).

* **Propositions** (`Basic.lean:32-52`): negation is not a constructor; atoms and dual atoms.

  ```lean
  inductive Proposition (Atom : Type u) : Type u where
    | atom (x : Atom)
    | atomDual (x : Atom)
    | one
    | zero
    | top
    | bot
    | tensor (a b : Proposition Atom)
    | parr (a b : Proposition Atom)
    | oplus (a b : Proposition Atom)
    | with (a b : Proposition Atom)
    | bang (a : Proposition Atom)
    | quest (a : Proposition Atom)
  deriving DecidableEq, BEq
  ```

  `Proposition.dual` is a function (`:126-138`), notation `a⫠`; `dual_involution` (`:157`),
  `dual_neq : a ≠ a⫠` (`:152`), `dual_sizeOf` (`:147`). `a ⊸ b := a⫠ ⅋ b` (`:167`).
* **Sequents are multisets:** `abbrev Sequent Atom := Multiset (Proposition Atom)` (`:172`).
  **There is no exchange rule**; exchange is the equality of multisets, and proofs are moved
  along sequent equalities with `Proof.rwConclusion` (`:212`) and `▸`.
* **The proof system** (`Basic.lean:189-204`), in `Type u`:

  ```lean
  inductive Proof : Sequent Atom → Type u where
    | ax : Proof {a, a⫠}
    | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
    | one : Proof {1}
    | bot : Proof Γ → Proof (⊥ ::ₘ Γ)
    | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
    | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
    | oplus₁ : Proof (a ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
    | oplus₂ : Proof (b ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
    | with : Proof (a ::ₘ Γ) → Proof (b ::ₘ Γ) → Proof ((a & b) ::ₘ Γ)
    | top : Proof (⊤ ::ₘ Γ)
    | quest : Proof (a ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
    | weaken : Proof Γ → Proof (ʔa ::ₘ Γ)
    | contract : Proof (ʔa ::ₘ ʔa ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
    | bang {Γ : Sequent Atom} {a} : Γ.allQuest → Proof (a ::ₘ Γ) → Proof ((!a) ::ₘ Γ)
    -- No rule for zero.
  ```

  The identity axiom is general (any `a`), cut is a constructor, the tensor split is `Γ + Δ`.
  `⇓Γ` is notation for `Proof Γ` through `HasInferenceSystem`; `Derivable` is its `Prop`
  truncation.
* **What is proved** in `Basic.lean`: inversions obtained **by cut** (`parrInversion :226`,
  `botInversion :231`, `withInversion₁/₂ :236,240`); logical equivalence `≡⇓` (proof-relevant)
  and `≡` (Prop), with reflexivity, symmetry, transitivity, `Equiv.dual` (`:282-308`); a list of
  equivalences (`bangTopEqvOne :324`, `questZeroEqvBot :329`, `tensorZeroEqvZero :335`,
  `parrTopEqvTop :340`, `tensorDistribOplus :353`, `tensorSymm :559`, `tensorAssoc :567`,
  `oplusIdem :583`, `withIdem :589`); substitution of equivalents (`substEqv :382`) and a
  congruence instance (`:546`); `Proof.cutFree : ⇓Γ → Bool` (`:598`).
* **Cut elimination is NOT proved.** `Basic.lean:17-19` lists it under TODO, and
  `CutElimination.lean` contains only `abbrev CutFreeProof (Γ) := { q : ⇓Γ // q.cutFree }`
  (`:20`) and two commented-out signatures, `Proof.cutAdm` and `Proof.cut_elim`, each marked
  `-- TODO` (`:22-32`).
* `EtaExpansion.lean`: `Proposition.expand (a) : ⇓{a, a⫠}` building identity from atomic axioms
  (`:29`), `Proof.onlyAtomicAxioms` (`:81`), `expand_onlyAtomicAxioms` (`:118`).
* `MLL.lean`: the multiplicative fragment as a predicate plus a subtype (`Proposition.IsMLL :38`,
  `Proof.IsMLL :101`, `MLL.Proof :179`); `Proof.isMLL_cutFree` (`:158`): a cut-free CLL proof of
  an MLL sequent is an MLL proof. The header calls this file the reference recipe for defining a
  fragment of an inference system in cslib. **There is no MALL file.**
* `PhaseSemantics/Basic.lean`: `class PhaseSpace (M) extends CommMonoid M where bot : Set M`
  (`:68-70`); `imp` (`:82`), `orthogonal` (`:85`), biorthogonal closure as a Mathlib
  `ClosureOperator` (`:107`), `isFact` (`:136`), `structure Fact` (`:139`); the connectives on
  facts (`tensor :340`, `parr :348`, `linImpl :428`, `withh :483`, `oplus :490`, `bang :497`,
  `quest :504`, exponentials via idempotents `I`, Girard 1995 style); De Morgan, commutativity,
  associativity and distributivity lemmas (`:362-590`); `Fact.IsValid G := 1 ∈ G` (`:629`);
  `interpProp (v : Atom → Fact M) : Proposition Atom → Fact M` (`:642-654`).
  **Soundness and completeness are listed as TODO** (`:45-47`); there is no theorem connecting
  `Proof` to `interpProp`.

### C.3 Others

READ = I fetched the named file; the saved copies are in `S/src/mech/abella/`, `S/src/mech/misc/`
and `S/src/mech/ffl/`. Otherwise the line is from a README or a search result and is marked.

* **Abella: Chaudhuri, Lima, Reis, "Formalized meta-theory of sequent calculi for linear logics"**,
  https://github.com/meta-logic/abella-reasoning (last push 2019-01). READ `one-sided/mall/mall.thm`
  (775 lines): one-sided MALL with units, formulas as `o` with `atom`/`natom`, sequents as
  lists handled through the relations `adj` (insert one element) and `merge` (interleave two
  lists), so there is no exchange rule but `mall_perm` is a theorem (`:113`); atomic initial
  rule, `generalized_id` (`:91`), inversion lemmas for ⊥, ⅋, & (`:183-378`), and
  **`mall_cut` (`:545`)**, cut admissibility by nested induction on the cut formula (through
  the `dual` judgment) and on the first derivation. `status.txt` marks as complete: MALL
  (one- and two-sided), MALL focused ("synthetic", `mallf.thm`), first-order MALL
  (`mallq.thm`), MLL, MELL; and as incomplete: full LL, focused LL. This is the only
  development found that proves cut admissibility for exactly the one-sided MALL calculus.
* **Lean 4: FormalizedFormalLogic/LinearLogic**, https://github.com/FormalizedFormalLogic/LinearLogic ,
  commit `ead7870ee0` (2026-11-21), toolchain Lean v4.35.0, depends on Mathlib and their
  Foundation library. READ `LinearLogic/LL/Propositional.lean`: unit-free propositional LL
  (`atom`, `natom`, `tensor`, `par`, `plus`, `with`, `bang`, `quest`; no `1, ⊥, ⊤, 0`),
  `Sequent := Multiset Formula` (`:147`), `Derivation : Sequent → Type` with atomic axiom and a
  cut constructor (`:171-188`), `eta` (`:213`), and **soundness for phase semantics**
  (`derivation_sound :300`, `provable_sound :334`) over `LinearLogic/PhaseSpace/Basic.lean`.
  Same pattern for MLL and MELL files. No cut elimination, no completeness, no MALL file
  (grep for `cutElim`, `hauptsatz`, `complete` finds nothing in the files fetched). Also has
  coherence spaces and a geometry-of-interaction file for MLL, not read.
* **Coq: Xavier, Olarte, Reis, Nigam, "Mechanizing focused linear logic in Coq"** (ENTCS 2018),
  https://github.com/meta-logic/coq-ll (last push 2026-11; README says tested with Rocq 9.3).
  Directories `PLL` (propositional) and `FOLL` (first-order). READ
  `PLL/LL/SequentCalculi.v`: several two-zone (dyadic) one-sided systems as
  `list lexp -> list lexp -> Prop`, some indexed by height and cut count, sequents treated up
  to multiset equality `meq` (`Proper (meq ==> meq ==> iff)`). README: cut elimination and
  completeness of the focused (triadic) system. Full LL, not a MALL fragment.
  The follow-up is https://github.com/meta-logic/coq-fll (from a search result, not opened).
* **Coq: Larchey-Wendling, relational phase semantics**, https://github.com/DmxLarchey/Coq-Phase-Semantics .
  READ `coq.type/cut_elim.v`: **intuitionistic** linear logic (two-sided, `Γ ⊢ A`),
  `Okada_formula` (`:180`) and `ill_cut_elimination Γ A : Γ ⊢ A -> { p : Γ ⊢ A | ill_cut_free p }`
  (`:252`). This is the Okada-lemma route to cut elimination that Lafont's Lemma 1 uses, done
  for ILL with exponentials, with phase spaces presented relationally (no monoid quotient).
  Four variants of the development (`coq.type`, `coq.prop`, `coq.nc`, `coq.gen`). Not classical,
  no finite model property.
* **Coq: P.-M. Pédrot, ll-coq**, https://github.com/ppedrot/ll-coq . READ `src/All.v` (894 lines):
  classical one-sided full LL, lists with a permutation rule, `derivation : sequent -> Prop`
  with general identity and a cut constructor (`:68-100`); phase semantics with
  `eval_φ_sound : derivation Γ -> [[Γ]] M_nul` (`:568`) and `eval_φ_complete` (`:846`) for the
  syntactic model. Completeness is against derivations WITH cut, so it is not a cut-elimination
  proof. The file has one `admit` (`:122`) and an axiom for decidable equality on variables
  (`:10`). Not a finite model property.
* **Coq: Larchey-Wendling, "Constructive decision via redundancy-free proof-search"** (IJCAR
  2018; JAR 2020), https://github.com/DmxLarchey/Relevant-decidability (from the search result
  and abstract; repository not opened). Decidability of implicational relevance logic by
  Kripke's method with Dickson's lemma via almost-full relations. Related in technique to
  Lafont's Lemma 4/5 (affine logic), not to MALL.
* **Coq: Forster and Larchey-Wendling, undecidability library**,
  https://github.com/uds-psl/coq-library-undecidability , `theories/ILL/`. READ `ILL/CLL.v`:
  cut-free two-sided classical LL `S_cll : list cll_form -> list cll_form -> Prop` (`:219`),
  used for the undecidability of CLL (`CLL_undec.v`). Undecidability of the full logic, nothing
  on MALL.
* **Isabelle:** AFP entry "ILL" (Filip Smola, 2025), a deep embedding of intuitionistic linear
  logic, https://www.isa-afp.org/entries/ILL.html and https://github.com/pilif0/isa-ILL (from
  search results; not opened). No MALL cut elimination found in the AFP.
* **Agda:** nothing found for classical MALL. `phadej/ncill` (cut elimination for
  non-commutative ILL) and `brunoczim/linear-logic` appear in a GitHub repository search by
  description only; not opened.
* **Proof nets in Rocq:** Di Guardia and Laurent, unit-free multiplicative proof nets with
  sequentialisation (from a search result, https://perso.ens-lyon.fr/olivier.laurent/rocqpn.pdf ;
  not opened). MLL, not MALL.

### C.4 What was not found

Two web searches and three GitHub repository searches (Lean, Agda, Isabelle; by the phrase
"linear logic") found **no mechanisation of the MALL finite model property**, **no mechanised
decision procedure for MALL provability**, and **no mechanised phase-semantic completeness or
cut elimination for classical MALL by Okada's lemma**. The nearest pieces are: Okada's lemma
for ILL (Larchey-Wendling), syntactic MALL cut admissibility (Abella), phase soundness in
Lean 4 (FormalizedFormalLogic) and phase-space algebra without soundness in Lean 4 (cslib).
This is absence in a bounded search, not a proof of absence.

### C.5 Design contrasts relevant to a Lean 4 MALL formalisation (INFERRED, from the above)

| Choice | Yalla | cslib | Abella MALL | Lafont's paper |
|--------|-------|-------|-------------|----------------|
| Negation | defined; `var`/`covar` | defined; `atom`/`atomDual` | relation `dual` | defined; positive atoms |
| Sequent | list + explicit `ex_r` | `Multiset`, no exchange | list + `adj`/`merge` | multiset |
| Identity | atomic | general | atomic | general (only atomic used in Lemma 1) |
| ⊗ split | `l2 ++ l1` | `Γ + Δ` | `merge JJ KK LL` | `Γ, Δ` |
| Proofs | `Type` | `Type u` | `prop` | - |
| Cut | parameter `pcut`, admissible | constructor; elimination TODO | admissible (`mall_cut`) | Theorem 1 via Lemma 1 |

Lafont's argument is stated over multisets, and the monoid of the syntactical model is the
free commutative monoid, which in Lean is `Multiset Formula` under `+` (Mathlib has the
`AddCommMonoid`; a `Multiplicative` wrapper or an additive phase space is needed to match
cslib's `PhaseSpace`, which `extends CommMonoid`).
