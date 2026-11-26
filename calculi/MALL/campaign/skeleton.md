# MALL: the source's numbered results

Written by hand, 2026-11-26, from the printed numbers of the scan
`linear.pdf` (J.-Y. Girard, *Linear logic*, Theoretical Computer Science
50 (1987) 1-102; `decisions.md`, the first entry). The source is a scan
with no LaTeX and no labels, so an item is cited by its printed number
and page. Only the items of Section 1 that are about the propositional
fragment without exponentials are listed in full; the rest of the paper
is listed by section. Pages are the paper's (the file's page is one
more).

## Section 1, "The phase semantics", pp. 17-28

| item | page | what it states (in the source's words where short) |
|---|---|---|
| Definition 1.1 | 18 | "A *phase space* P consists in the following data: (i) a monoid, still denoted P, and whose elements are called *phases*; the monoid is supposed to be commutative, i.e., neutrality: 1p = p1 = p for all p ∈ P, commutativity: pq = qp for all p, q ∈ P, associativity: (pq)r = p(qr) for all p, q, r ∈ P; (ii) a set ⊥_P (often denoted ⊥ for short), the set of *antiphases* of P." |
| Definition 1.2 | 18 | "Assume that G is a subset of P; then we define its *dual* G^⊥ by G^⊥ = {p ∈ P; ∀q(q ∈ G → pq ∈ ⊥)}." |
| Definition 1.3 | 18 | "A *fact* is a subset G of P such that G^⊥⊥ = G; the elements of G are called the *phases* of G; G is *valid* when 1 ∈ G." |
| 1.4, Immediate properties | 18 | (i) G ⊂ G^⊥⊥; (ii) G ⊂ H → H^⊥ ⊂ G^⊥; (iii) G is a fact iff G is of the form H^⊥ for some subset H of P. |
| 1.5, Examples | 18 | (i) ⊥ is a fact because ⊥ = {1}^⊥; (ii) the fact **1** = ⊥^⊥, with 1 ∈ **1**; (iii) the fact ⊤ = ∅^⊥ = P; (iv) the fact **0** = ⊤^⊥, the smallest fact. |
| Proposition 1.6 | 18-19 | Facts are closed under arbitrary intersections. |
| Definition 1.7 | 19 | Linear negation ("nil") of a fact G is G^⊥. |
| Definition 1.8 | 19 | The multiplicatives, from the product GH = {pq; p ∈ G and q ∈ H}: (i) par, G ⅋ H = (G^⊥.H^⊥)^⊥; (ii) times, G ⊗ H = (G.H)^⊥⊥; (iii) entails, G ⊸ H = (G.H^⊥)^⊥. |
| 1.9, Basic properties of multiplicatives | 19 | De Morgan forms; par and times commutative and associative, with neutral elements ⊥ and **1**; five equations for ⊸. |
| Lemma 1.9.1 | 20 | (F.G)^⊥⊥ ⊃ F^⊥⊥.G^⊥⊥. |
| Remark 1.10 | 20 | p ∈ G ⊸ H iff, for all q ∈ G, pq ∈ H. |
| Definition 1.11 | 20 | The additives: (i) with, G & H = G ∩ H; (ii) plus, G ⊕ H = (G ∪ H)^⊥⊥. |
| 1.12, Basic properties of additives | 20 | De Morgan; commutative, associative, neutral elements ⊤ and **0**. |
| 1.13, Distributivity properties | 20-21 | (i) ⊗ distributes over ⊕ and ⅋ over &, as equations; **0** ⊗ G = **0**; ⊤ ⅋ G = ⊤; (ii) "half-distributivity": G ⊗ (H & K) ⊂ (G ⊗ H) & (G ⊗ K), (G ⅋ H) ⊕ (G ⅋ K) ⊂ G ⅋ (H ⊕ K). |
| Lemma 1.13.1 | 21 | G^⊥⊥ is the smallest fact containing G. |
| (the syntax, not numbered) | 21 | "(i) The atomic propositions are **1**, ⊥, ⊤, **0** together with propositional letters a, b, c, … and their duals a^⊥, b^⊥, c^⊥, … (ii) Propositions are constructed from atomic ones by applying the binary connectives ⊗, ⅋, ⊕, &." Linear negation is defined: **1**^⊥ = ⊥, ⊥^⊥ = **1**, ⊤^⊥ = **0**, **0**^⊥ = ⊤, a^⊥⊥ = a, (A ⊗ B)^⊥ = A^⊥ ⅋ B^⊥, (A ⅋ B)^⊥ = A^⊥ ⊗ B^⊥, (A ⊕ B)^⊥ = A^⊥ & B^⊥, (A & B)^⊥ = A^⊥ ⊕ B^⊥. |
| Definition 1.14 | 22 | (i) a *phase structure*: a phase space and, for each propositional letter a, a fact a_S; (ii) the interpretation S(A) of a proposition, a fact, "in a completely straightforward way"; (iii) A is valid in S when 1 ∈ S(A); (iv) A is a *linear tautology* when valid in any phase structure. |
| Definition 1.15 | 22 | The sequent calculus: sequents ⊢ A₁, …, Aₙ; logical axioms, cut, exchange, the additive rules, the multiplicative rules (the figure: `rule-table.md`). |
| Proposition 1.16 | 23 | "Linear sequent calculus is sound w.r.t. validity in phase structures." The proof reads a sequent "as the *par* of its components (and, when the list is void, as ⊥)". |
| Theorem 1.17 | 23-24 | "Linear sequent calculus is complete w.r.t. phase semantics." By the phase space of multisets of formulas, with antiphases the provable ones; equation (3), S(A) = Pr(A) = {**B**; ⊢ A, **B** is provable}. |
| 1.18, Remarks | 24-25 | (i) no notion of a linear logical theory; (ii) phase spaces need not be commutative. |
| Definitions 1.19-1.21, Theorem 1.22, Lemma 1.22.1 | 25-27 | Topolinear spaces, the exponentials and their rules: not in the fragment. |

## The rest of the paper, by section (not in the fragment, or about proof nets)

| section | pages | what it has that the plan cites |
|---|---|---|
| II.2, II.3 | 4-5 | the two conjunctions from the two ∧-rules; "A ⊸ A ⊗ A is not derivable, but A ⊸ A & A is" (p. 5) |
| 2, Proof-nets | 28-47 | 2.2 the cut rule for nets (p. 40); 2.3 cut elimination for multiplicative nets: Proposition 2.10 (a contractum of a proof-net is a proof-net, and is strictly smaller), Proposition 2.11 (reduction is Church-Rosser), Theorem 2.12 (strong normalisation: "a proof-net of size n normalizes into a cut-free proof-net in less than n steps"), pp. 41-42; 2.4 the system PN1, 2.5 PN2 (nets with boxes for the additives and the rest) |
| 4, Normalization in PN2 | 60-78 | normalisation for the nets of the full calculus (not read) |
| 3, 5, 6, V | 48-60, 78-101 | coherent semantics, translations, slices (not read) |
