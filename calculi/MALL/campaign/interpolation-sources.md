# Interpolation for linear and substructural logics: what four sources state

Read 2026-11-26, 15:07 to 15:18 GMT (times from `date`). Reading only; nothing here is machine-checked. "p." is the printed page number of the source. Formal statements are transcribed into one notation (Γ, Δ, Π, Λ multisets; V(·) the set of variables).

## Files

| # | Source | URL | Bytes | Pages | Status |
|---|--------|-----|------:|------:|--------|
| 1 | Alizadeh, Derakhshan, Ono, "Uniform interpolation in substructural logics", RSL 7(3) 2014, 455–483 | https://www.andrew.cmu.edu/user/fderakhs/publications/RSL.pdf | 246606 | 29 | obtained (publisher's PDF on an author's page) |
| 2 | Akbar Tabatabai, Jalali, "Universal proof theory: semi-analytic rules and uniform interpolation", arXiv:1808.06258 **v2**, 26 Jun 2025, CC BY 4.0 | https://arxiv.org/pdf/1808.06258 | 641253 | 56 | obtained |
| 3 | Akbar Tabatabai, Jalali, "Universal proof theory: semi-analytic rules and Craig interpolation", arXiv:1808.06256 **v3**, 3 Sep 2024, CC BY 4.0 | https://arxiv.org/pdf/1808.06256 | 407445 | 38 | obtained |
| 4 | Roorda, "Interpolation in fragments of classical linear logic", JSL 59(2) 1994, 419–444 | cambridge.org, article EE459646FE31AEEBA0ED30063886F778 | n/a | n/a | **not obtained** (purchase only; abstract page read) |
| 4′ | Roorda, *Resource Logics: Proof-theoretical Investigations*, PhD thesis, Amsterdam 1991, Ch. V "Interpolation", pp. 62–86 | https://ndownloader.figshare.com/files/1460649 (author's deposit, doi:10.6084/m9.figshare.995908, CC BY 4.0) | 5491521 | 72 sheets, two thesis pages each (pp. 1–130) | obtained; **scan, no text layer**; read from page images |

Notes on the files.

- Quotation. Sources 2, 3 and 4′ are CC BY 4.0 and are quoted verbatim. Source 1 is under publisher's copyright: it is given in close paraphrase with locations and **one** short quotation. Greek capitals and ⊤ were lost in the text extraction of source 1; every table and theorem cited from it was checked against a page image (pp. 462, 463, 464, 467, 468, 469).
- Source 4′ pages read from images: 15, 16, 62–68, 70–73, 77, 78, 86. **Not read**: 69, 74–76, 79–85 (most of the proof for the fragment (⊸), the proof of the counterexample, the appendix on the Lambek calculus) and Chapter IV (quantum graphs).
- Other attempts for 4/4′: the KNAW Pure copy of the thesis answered HTTP 403 with a bot-detection page and was left alone. ILLC eprints lists only Roorda's report ML-1989-08, a different work (not fetched).
- The earlier arXiv versions (v1 of both, 2018) were **not read**; their statements may differ.
- Local copies are in the session scratchpad under `src-interp/` (not durable).

## 0. Summary of the answers

| | 1 (ADO 2014) | 2 (AT–J, UIP) | 3 (AT–J, CIP) | 4′ (Roorda 1991) |
|---|---|---|---|---|
| Name of MALL with 4 units | **InFLₑ** (glossed as MALL) | **CFLₑ** (4 constants; the word MALL does not occur) | **MALL**; here CFLₑ has only 0, 1 | type II fragment of CLL without !, ? |
| Sequents | two-sided, multisets; FLₑ single succedent (or empty), InFLₑ multi-succedent | two-sided, multisets, multi- or single-conclusion | same as 2 | two-sided, multisets, multi-conclusion |
| Primitive connectives | FLₑ: ∧ ∨ · → ; InFLₑ: ∧ ∨ · + ¬ | ∧ ∨ ∗ → (¬, + defined) | ∧ ∨ ∗ → (+ !ᵅ) | ⊓ ⊔ • + ⊸ ⁰ ! ? |
| Identity axiom | atomic `p ⇒ p` | schematic `p ⇒ p`, instances `φ ⇒ φ` | as 2 | `A ⊢ A` |
| Property | UIP | UIP | Craig | Craig with polarity |
| Mechanised proof mentioned | no | no | no | no |

No source uses a one-sided calculus.

## 1. Alizadeh, Derakhshan, Ono (2014)

**(a) The logics.**
- FL: constants ⊤, ⊥, 1, 0; connectives ∧, ∨, ·, \, / (§2, p. 457). The paper says that the usual definition has only 1 and 0, and that ⊤ and ⊥ are needed for uniform interpolation (p. 457); the reason is on p. 461: without them a variable p has no post-interpolant with respect to ∅.
- FLₑ (§2.2, p. 458): sequents Γ ⇒ α or Γ ⇒ (empty succedent) with Γ a multiset, so no exchange rule; α\β written α → β; ¬α abbreviates α → 0. Initial sequents (p. 457): p ⇒ p (p a variable), Γ ⇒ ⊤, Γ, ⊥, Δ ⇒ φ, ⇒ 1, 0 ⇒. Rules: (1w), (0w), two ∧-left, ∧-right, ∨-left, two ∨-right, ·-left, ·-right (context-splitting), →-left (context-splitting), →-right (p. 458). The calculi are given without cut; cut is admissible (Theorem 2.1, p. 459).
- FLₑw (§2.3, p. 459): 1 ≡ ⊤ and 0 ≡ ⊥, so 1 and 0 are dropped; sequents Γ ⇒ α only; initial sequent Γ, p ⇒ p replaces p ⇒ p and left weakening.
- **InFLₑ** (§4, pp. 466–467) is FLₑ plus ¬¬φ → φ. Sequents Γ ⇒ Δ, both multisets. Primitive ¬ and + (dual of fusion); α → β is defined as ¬α + β. Constants ⊤, ⊥, 1, 0. Initial sequents: (1) p ⇒ p for a variable p; (2) Γ ⇒ ⊤, Δ; (3) Γ, ⊥ ⇒ Δ; (4) ⇒ 1; (5) 0 ⇒. Rules: (1 ⇒), (⇒ 0), (¬ ⇒), (⇒ ¬), (∧1 ⇒), (∧2 ⇒), (⇒ ∧), (∨ ⇒), (⇒ ∨1), (⇒ ∨2), (· ⇒), (⇒ ·), (+ ⇒), (⇒ +). Cut admissible: Theorem 4.1, citing Girard 1987 and Troelstra 1992.
- The name CFLₑ does not occur in this paper.
- On linear logic: p. 456 glosses InFLₑ as MALL; §4, p. 466, of InFLₑ and InFLₑw: "They are sometimes called linear logic (denoted by MALL) and affine logic" (the one quotation from this source). FLₑ is said to be known as intuitionistic linear propositional logic without exponentials (p. 457). The paper gives **no** table relating its symbols to Girard's. From the rules: 1 and 0 are the multiplicative units and ⊤ and ⊥ the additive ones, so its 0 is Girard's ⊥ and its ⊥ is Girard's 0 (my reading; it agrees with Table 1 of source 3).

**(b) The property** (§3, pp. 460–461). For a formula and a **set** of variables. L has UIP iff for each α and each V₀ ⊆ V(α) there is a *post-interpolant* α∗[V₀] with

    (1) V(α∗[V₀]) ⊆ V₀   (2) ⊢ α → α∗[V₀]
    (3) for every β with V(α) ∩ V(β) ⊆ V₀:  ⊢ α → β  implies  ⊢ α∗[V₀] → β

and for each β and V₁ ⊆ V(β) a *pre-interpolant* β\*[V₁] with the dual (4)–(6). (Lower star: post; upper star: pre.) The test formula in (3) may contain variables outside V(α). Lemma 3.4 (p. 461) reduces sets to one variable at a time (V₀ = V(α)∖{p}), by induction on the size of V(α)∖V₀. The sequent forms that are proved:

    Theorem 3.5 (FLₑ, pp. 463–464). Γ a multiset, α a formula or empty, p a variable.
    There are formulas E_p(Γ), A_p(Γ; α) with
    (1a) V(E_p(Γ)) ⊆ V(Γ)∖{p}        (1b) V(A_p(Γ; α)) ⊆ V(Γ, α)∖{p}
    (2a) ⊢ Γ ⇒ E_p(Γ)                (2b) ⊢ Γ, A_p(Γ; α) ⇒ α
    (3)  for Π not containing p, if ⊢ Π, Γ ⇒ α then
         (a) ⊢ Π, E_p(Γ) ⇒ α  when p ∉ V(α)       (b) ⊢ Π ⇒ A_p(Γ; α)

    Theorem 4.3 (InFLₑ, p. 468). Γ, Δ multisets, p a variable. There is A_p(Γ; Δ) with
    (1) V(A_p(Γ; Δ)) ⊆ V(Γ, Δ)∖{p}
    (2) ⊢ Γ, A_p(Γ; Δ) ⇒ Δ
    (3) for Π, Λ not containing p:  ⊢ Π, Γ ⇒ Δ, Λ  implies  ⊢ Π ⇒ A_p(Γ; Δ), Λ

E_p(α) and A_p(∅; α) are the post- and pre-interpolants for V(α)∖{p} (p. 462). For InFLₑ only A_p is defined; Lemma 4.2 (p. 467) gives the post-interpolant as ¬(¬α)\*[V₀].

**(c) Scope.** Proved: FLₑ (Cor. 3.6), FLₑw (Thm 3.7), InFLₑ = MALL (Cor. 4.4), InFLₑw (Thm 4.5), FL (Cor. 5.3), and the predicate extensions QFL, QFLₑ, QFLₑw, QInFLₑ, QInFLₑw without function symbols (Thm 7.5). With contraction: nothing is proved or refuted; the introduction (p. 456) names contraction as the obstacle, since a premise is then not lighter than the conclusion, and states only the expectation that UIP holds without it. With exponentials: nothing; the abstract restricts to linear and affine logic without exponentials. Failures recalled from the literature: S4, classical and intuitionistic predicate logic (pp. 455–456).

**(d) The method** is Pitts's (p. 456, p. 462). The weight w is the number of symbols; w(Γ) is the sum; every rule's premises are strictly lighter (p. 459). The tables define finite **sets** 𝓔_p(Γ), 𝓐_p(Γ; α) by pattern matching on Γ (and α); then E_p(Γ) := ⋀𝓔_p(Γ) and A_p(Γ; α) := ⋁𝓐_p(Γ; α), by simultaneous recursion on weight (p. 462). q is a variable ≠ p or a constant; r is any variable or a constant.

Table 1, FLₑ, 𝓔_p (p. 462): ∅ ↦ 1; p ↦ ⊤; q ↦ q; Γ′,φ∧ψ ↦ E(Γ′,φ) ∧ E(Γ′,ψ); Γ′,φ∨ψ ↦ E(Γ′,φ) ∨ E(Γ′,ψ); Γ′,φ·ψ ↦ E(Γ′,φ,ψ); Γ′,φ→ψ ↦ ⋀_{Γ₁,Γ₂=Γ′} [A(Γ₁;φ) → E(Γ₂,ψ)]; Γ ↦ ⋀_{Γ₁,Γ₂=Γ} E(Γ₁)·E(Γ₂) (both parts non-empty); otherwise ⊤. Table 2, FLₑ, 𝓐_p (p. 463), 18 lines, among them the context-division line Γ; α ↦ ⋁_{Γ₁,Γ₂=Γ, Γ₁≠∅} [E(Γ₁) → A(Γ₂; α)].

Table 4, **InFLₑ**, 𝓐_p(Γ; Δ) (p. 469), all 20 lines:

    r; r ↦ 1          ∅; ∅ ↦ 0          q; ∅ ↦ ¬q          ∅; q ↦ q
    Γ′,1; Δ ↦ A(Γ′; Δ)                  Γ; 0,Δ′ ↦ A(Γ; Δ′)
    Γ; ⊤,Δ′ ↦ ⊤                         Γ′,⊥; Δ ↦ ⊤
    Γ; φ∧ψ,Δ′ ↦ A(Γ; φ,Δ′) ∧ A(Γ; ψ,Δ′)      Γ; φ∨ψ,Δ′ ↦ A(Γ; φ,Δ′) ∨ A(Γ; ψ,Δ′)
    Γ′,φ∧ψ; Δ ↦ A(Γ′,φ; Δ) ∨ A(Γ′,ψ; Δ)      Γ′,φ∨ψ; Δ ↦ A(Γ′,φ; Δ) ∧ A(Γ′,ψ; Δ)
    Γ′,φ·ψ; Δ ↦ A(Γ′,φ,ψ; Δ)                 Γ; φ+ψ,Δ′ ↦ A(Γ; φ,ψ,Δ′)
    Γ₁,Γ₂; φ·ψ,Δ₁,Δ₂ ↦ A(Γ₁; φ,Δ₁) · A(Γ₂; ψ,Δ₂)
    Γ₁,Γ₂,φ+ψ; Δ₁,Δ₂ ↦ A(Γ₁,φ; Δ₁) · A(Γ₂,ψ; Δ₂)
    Γ₁,Γ₂; Δ₁,Δ₂ ↦ A(Γ₁; Δ₁) + A(Γ₂; Δ₂)     (Γᵢ = Δᵢ = ∅ not allowed, i = 1, 2; p. 468)
    Γ; ¬φ,Δ′ ↦ A(φ,Γ; Δ′)                    Γ′,¬φ; Δ ↦ A(Γ′; φ,Δ)
    otherwise ↦ ⊥

Shape: one line per rule read backwards (each choice of principal occurrence and each division of the context is a separate member of the set), one line that divides the context with no principal formula, the atomic and constant cases, and a default. Table 5 (p. 470) modifies three lines for InFLₑw.

Proofs for FLₑ (pp. 464–465): (1) by inspection; (2) by simultaneous induction on weight; (3) by induction on the weight of Π, Γ ⇒ α, by cases on the last rule of a cut-free proof and on whether its principal formula lies in Π or in Γ. The paper says this is not an induction on the length of a given proof (p. 464); only the cases (→ ⇒) and (⇒ →) are written out. **For InFLₑ no proof is written**: Theorem 4.3 is said to be shown similarly to Theorem 3.5, with a pointer to Theorem 5.1 of Bílková 2007 (p. 468). FL (§5) needs side conditions (provability of certain A_p formulas), decidable since FL is (p. 470); §5 ends by showing that under exchange they become redundant.

**(f)** No mention of a mechanised proof (text searched for Coq, Lean, Isabelle, Agda, "mechani", "proof assistant").

## 2. Akbar Tabatabai, Jalali: uniform interpolation (arXiv v2, 2025)

**(a) The logics.** Language 𝓛_p = {∧, ∨, ∗, →, ⊤, ⊥, 1, 0} (§2, p. 6); ¬A := A → 0 and A + B := ¬(¬A ∗ ¬B) are definitions. A sequent is Γ ⇒ Δ with finite multisets; it is single-conclusion when |Δ| ≤ 1 (pp. 7–8). **CFLₑ** is Figure 1 (p. 10): axioms p ⇒ p (id), ⇒ 1, 0 ⇒, Γ ⇒ ⊤, Δ, and Γ, ⊥ ⇒ Δ; rules (1w), (0w), (L∧₁), (L∧₂), (R∧), (L∨), (R∨₁), (R∨₂), (L∗), (R∗), (L→), (R→). Rules are schemes closed under substitution of formulas for atoms, so (id) gives φ ⇒ φ (used so on p. 23). (L+), (R+) are derived (p. 10). "The calculus FLe is the single-conclusion version of CFLe" (p. 10). Cut is admissible (p. 11). Remark 2.5 (p. 11): "the presence of ⊥ and ⊤ is crucial for establishing the uniform interpolation property", "in alignment with [3]" (source 1). The paper never uses the name MALL and does not relate CFLₑ to linear logic; linear logic appears only for the modal rules, which "are used in Linear Logic when □ is denoted by '!'" (p. 12). Comparing definitions, this CFLₑ is the calculus source 3 calls MALL (without cut) and the logic source 1 calls InFLₑ (my comparison; no source says it).

**(b) The property.** For a formula and **one** atom, both quantifiers (Definition 4.1, p. 19): there are p-free ∃pφ, ∀pφ with V(∃pφ), V(∀pφ) ⊆ V(φ) and

    (i) ⊢ φ → ∃pφ      (ii) for p-free ψ:  ⊢ φ → ψ  implies  ⊢ ∃pφ → ψ
    (iii) ⊢ ∀pφ → φ    (iv) for p-free ψ:  ⊢ ψ → φ  implies  ⊢ ψ → ∀pφ

For sequents with a context (Definition 5.1, pp. 20–21; S·T is the union on each side): for all sequents T, S and atoms p there are p-free ∃pT, ∀pS with V(∃pT) ⊆ V(T), V(∀pS) ⊆ V(S) and

    (i)   ⊢ T · (⇒ ∃pT)
    (ii)  for p-free multisets C̄, D̄:  ⊢ T · (C̄ ⇒ D̄)  implies  ⊢ ∃pT, C̄ ⇒ D̄
    (iii) ⊢ S · (∀pS ⇒)
    (iv)  for p-free multisets C̄, D̄:  ⊢ S · (C̄ ⇒ D̄)  implies  ⊢ C̄ ⇒ ∀pS, D̄

Single-conclusion variant: T has empty succedent, S is single-conclusion, D̄ = ∅ in (iv), and D̄ has at most one formula in (ii). Theorem 5.3 (p. 21) passes from the calculus to the logic.

**(c) Scope.** Theorem 4.3 (p. 19): a logic L ⊇ FLₑ with a terminating single-conclusion semi-analytic calculus, or L ⊇ CFLₑ with a terminating multi-conclusion one, "has the uniform interpolation property". Corollary 4.4 (p. 19): FLₑX, FLₑwX, CFLₑX, CFLₑwX for X ⊆ {K, T, KD, Lw□}, and CPC, K, KD (CPC through the G3-style calculus Gcs, Figure 2). For the purely substructural cases the paper says UIP was known (p. 6, citing source 1). Contraction: FLₑc, CFLₑc are defined (p. 11) but nothing is claimed for them; Theorem 3.11 covers "All contraction-free sequent calculi" of §2. Exponentials: no result for ILL or CLL; "we do not consider contraction-like rules" (p. 12); of the modal rules of source 3 "only (K) and (KD) can be handled to prove UIP" (Remark 3.9, p. 17). Negative: K4 and S4 lack UIP, hence have no terminating semi-analytic calculus (Corollary 4.5, p. 20). Left open (p. 54): calculi with analytic cut; a generic form of modal rules.

**(d) The method** is Pitts's, made generic. A calculus is *terminating* for a well-founded order ≼ on sequents if the premises of every rule instance with conclusion S, the proper subsequents of S, and Γ ⇒ Δ when S = □Γ ⇒ □Δ, are strictly below S (Definition 3.10, p. 17). For the calculi above ≼ is "replace one formula by finitely many shorter ones", ranked by an ordinal below ω^ω (Theorem 3.11, pp. 17–18). The interpolants are defined "by recursion on ≼" and their properties proved "by induction on ≼" (p. 47). Multi-conclusion case (Theorem 5.9, p. 47): ∀pS := 0 for the empty sequent, otherwise

    ∀pS := ⋁_{(S₁,…,Sₙ) ∈ par(S)} (∀pS₁ + ⋯ + ∀pSₙ)  ∨  ∀ᴸpS ∨ ∀ᴿpS ∨ ∀ᴹpS ∨ ∀^□pS ∨ ∀ᴬpS
    ∀ᴸpS := ⋁_{(R,σ)} ∗ᵢ ⋀ᵣ ∀pS_ir     (same form for ∀ᴿ)        ∃pS := ¬∀pS

- par(S): the non-trivial partitions of S, tuples of non-empty sequents with n ≥ 2 and S = S₁·…·Sₙ (Definition 5.6, p. 28). The context is divided into n parts, not two.
- (R, σ) ranges over the finitely many (Remark 3.7) instances of left (right) rules with conclusion S; S_ir are the premises, i over context-splitting branches, r over context-sharing premises of a branch. One disjunct per rule instance.
- ∀ᴹ, ∀^□ are ⊥ without modal rules.
- ∀ᴬpS := ¬∃ᴬpS for the axioms (Theorem 5.5, p. 26): for S = (Σ ⇒ Λ) with p-free parts Σ_p, Λ_p, ∃ᴬpS := [(∗Σ_p) ∗ (∗¬Λ_p) ∗ A₁] ∧ A₂ ∧ A₃ with A₁ = 1 if S is p-free, A₂ = 0 if S is an instance of μ ⇒ μ, ⇒ ν̄ or ρ̄ ⇒, A₃ = ⊥ if S is an instance of a context axiom, and each Aᵢ = ⊤ otherwise.

Proofs (pp. 48–50): the variable condition and (iii) by induction on ≼. (iv) by induction on ≼ and, inside each step, "induction on the depth of the proof" of S·(C̄ ⇒ D̄), by cases on the last rule and on whether its main formula lies in the p-free part; in the latter case by whether the part of S is spread over one premise branch or several, which uses the partition disjunct. The single-conclusion case (Theorem 5.7, pp. 28–31) defines ∃pV (conjunctions) and ∀pU (disjunctions) by mutual recursion, with ⋁_{par•(U)} ((∗_{i≠e} ∃pSᵢ) → ∀pSₑ) as the context-division clause.

**(f)** No mention of a mechanised proof.

## 3. Akbar Tabatabai, Jalali: Craig interpolation (arXiv v3, 2024)

**(a) The logics.** Two languages (p. 4): bounded 𝓛ᵇ = {∧, ∨, →, ∗, 0, 1, ⊤, ⊥} ∪ {!ᵅ} and unbounded 𝓛ᵘ = 𝓛ᵇ ∖ {⊤, ⊥}. **Here CFLₑ is over the unbounded language** (0 and 1 only): Table 2 (p. 8), which includes cut. "The calculus MALL is defined over the language [bounded] as the calculus consisting of all the axioms and rules in Table 2 plus" the axioms Γ ⇒ ⊤, Δ and Γ, ⊥ ⇒ Δ (p. 8). FLₑ and IMALL are the single-conclusion versions. So in this paper CFLₑ is not MALL: MALL = CFLₑ + ⊤, ⊥. The name CFLₑ therefore means different things in sources 2 and 3. The correspondence with Girard is Table 1 (p. 5):

    Girard:      ⊸   &   ⊕   ⊗   ⅋   (−)^⊥   ⊥   1   ⊤   0
    this paper:  →   ∧   ∨   ∗   +   ¬       0   1   ⊤   ⊥

introduced with "it is worth recalling the translation between our language and the one used by Girard" (p. 4). CLL (ILL) is MALL (IMALL) plus (R!), (L!), (W!), (C!) (p. 9).

**(e) Craig interpolation.** For the logic, for an implication (Definition 5.1, p. 21): if φ → ψ ∈ L there is θ with φ → θ ∈ L, θ → ψ ∈ L, V(θ) ⊆ V(φ) ∩ V(ψ). For the calculus, for a sequent divided in two (Definition 5.2, p. 21, "following the Maehara split-interpolation technique", p. 20):

    multi-conclusion: for S, any partition Σ ∪ Λ of its antecedent and Θ ∪ Δ of its
    succedent, if ⊢ S there is C with V(C) ⊆ V(Σ ∪ Θ) ∩ V(Λ ∪ Δ),
        ⊢ Σ ⇒ C, Θ   and   ⊢ Λ, C ⇒ Δ
    single-conclusion: the antecedent only is divided; ⊢ Σ ⇒ C and ⊢ Λ, C ⇒ succedent

**No Lyndon (polarity) refinement is stated**; "Lyndon" occurs only in titles in the bibliography. Proved (Theorem 5.7, Corollary 5.9, pp. 29–30) for every logic with a semi-analytic calculus that extends IMALL or MALL (bounded) or FLₑ or CFLₑ (unbounded); the calculus must be cut-free, since cut is not semi-analytic. Corollary 6.1 (p. 30) lists the calculi of Theorem 2.4 (p. 9): FLₑ, FLₑw, FLₑc, CFLₑ, CFLₑw, CFLₑc, LJ, LK, IMALL, AIMALL, RIMALL, MALL, AMALL, RMALL, ILL, CLL, ALL, RLL, ELL, and the multimodal calculi of §3. So Craig interpolation, unlike UIP in source 2, is obtained with contraction and with exponentials. Credit (p. 31): "the CIP for CLL and MALL is proved in [49] and for FLe in [48]", [49] being Roorda's JSL paper and [48] Ono–Komori 1985. Failures (Corollary 6.3, p. 33) include R, MTL, BL, Ł, and "continuum-many extensions of MALL and CLL".

Method: "induction on the structure of π", π a proof, by cases on the last rule and on the side of the division that holds the main formula. For a left rule with premises S_ir and interpolants C_ir: main formula in Σ gives C = +ᵢ ⋁ᵣ C_ir; in Λ gives C = ∗ᵢ ⋀ᵣ C_ir (p. 28). Axioms: Theorem 5.4 (pp. 21–23); for instance μ ⇒ μ with the formula on the Σ side gives C = φ, on the Λ side C = 1; a context axiom with its formulas in Σ gives ⊥, in Λ gives ⊤.

**(f)** No mention of a mechanised proof.

## 4. Roorda

**4 (JSL 1994): not obtained.** The public abstract says the paper proves interpolation for many elementary fragments of classical linear logic, refutes it for the multiplicative fragment (→, +) using proof nets and quantum graphs, and treats implication with product without permutation. Nothing else of the article was read; what follows is the thesis chapter, which may differ from the article.

**4′ (thesis, Ch. V).** Notation (p. 15, "new notation vs. Girard's notation"):

    Roorda:   •   +   ⊸   1   0   ⊓   ⊔   ⊤   ⊥        A⁰ := A ⊸ 0
    Girard:   ⊗   ⅋   ⊸   1   ⊥   &   ⊕   ⊤   0

CLL (pp. 15–16): two-sided sequents x ⊢ y, "x, y are multisets of formulas"; axioms A ⊢ A; rules for 1, 0, ⊥, ⊤, •, +, ⊸, ⁰, ⊓, ⊔, !, ?, and cut. An *elementary fragment* is the set of formulas over a subset of {0, 1, ⊥, ⊤, ⊓, ⊔, •, +, ⁰, ⊸, !, ?} (p. 62). Three kinds (p. 63): I "without ⁰ (linear negation) and without ⊸"; II "with negation, or ⊸ together with 0 (falsum)"; III "other". MALL with four units, and CLL, are of type II.

**(e) Statement.** For an implication (p. 62): "If an implication A ⊸ B is provable, then there exists an I such that A ⊸ I and I ⊸ B are provable", with a condition on material. The condition is a **polarity (Lyndon-style) condition**: Mat(A, B, I) holds "if every proposition letter having a positive (negative) occurrence in I, also has positive (negative) occurrences in A and in B" (p. 63). In purely multiplicative fragments it is strengthened to counting: for each letter there are injections from its positive (negative) occurrences in I into those in A and into those in B (p. 63). For sequents divided in two (p. 64): a *selection* marks some formulas on both sides, written x y̲ ⊢ u v̲; I is a positive interpolant if

    x, I ⊢ u   and   y ⊢ I, v   and   Mat(x̄ u, y v̄, I)

and a negative one if x ⊢ I, u and y, I ⊢ v and Mat(x ū, ȳ v, I) (bar: signs exchanged).

**Results.**
- "For every type I fragment 𝓕 interpolation holds" (§4, p. 65).
- "For every type II fragment 𝓕 interpolation holds" (§5, p. 65). This covers MALL and CLL. Proof: "induction on a cut-free proof", with the hypothesis loaded so that "for every selection we can find a positive as well as a negative interpolant"; I is positive iff I⁰ is negative for the same selection (Lemma, p. 66). Interpolants stay in the fragment. The clauses listed on pp. 66–67 are for the axioms, 1, 0, •, +, ⊸, ⁰, ⊓, ⊔; unary rules are said to copy sign and interpolant from the premiss, and no clause for ! or ? is shown.
- Type III, multiplicative only, without 0 (p. 68): "Interpolation holds for (⊸, •, +)" (6.3.2, p. 71); "Interpolation holds for (⊸, •)" (6.4.3, p. 73); for (⊸) it fails for sequents with several antecedent formulas, the example being p, r ⊢ (p ⊸ (r ⊸ q)) ⊸ q whose only multiplicative interpolant is p • r (p. 73), and holds "with respect to sequents of the form A ⊢ B" (6.5.6, p. 77).
- **Counterexample: the fragment (⊸, +), in Girard's notation (⊸, ⅋).** "Interpolation fails for this fragment" (6.6, p. 78), also for sequents A ⊢ B. Theorem (p. 78): there is no interpolant for

      (((a ⊸ f) ⊸ d) ⊸ ((f + b) ⊸ e)) ⊸ g  ⊢  ((a ⊸ (b ⊸ c)) ⊸ c) + ((d ⊸ e) ⊸ g)

  Footnote 3 (p. 78): this uses the strong (counting) Mat condition; whether an interpolant exists under the weaker condition "remains" a question. The proof (proof nets, quantum graphs; pp. 79 onwards) was **not read**.
- Open questions (§8, p. 86): the Lambek calculus without empty antecedents; "What happens if we add the additive ⊓ and ⊔?"; "What happens if we add modalities?". They follow the appendix on the Lambek calculus (§7, not read), so their scope was not established.

**(b)–(d)** Uniform interpolation is not treated in the pages read. **(f)** No mechanised proof; p. 78 remarks only that the finitely many candidate interpolants could be tested "by means of an automatic theorem prover".

## 5. Points that bear on a mechanisation of MALL

1. The MALL case of UIP in source 1 (Theorem 4.3) has a definition (Table 4) and no written proof. Source 2 has a written proof (Theorem 5.9) for a calculus with → primitive.
2. Source 1 fixes the identity axiom to atoms; source 2 has identity on all formulas.
3. Source 1's Table 4 divides the context in two; source 2 uses partitions into n ≥ 2 parts.
4. Source 1 states (3) with a context Π, Λ on both sides, and its recursion is on weight alone; source 2 adds an inner induction on proof depth.
5. Both UIP papers require ⊤ and ⊥ in the language; with only 0 and 1 (source 3's CFLₑ) source 1 says the post-interpolant of p for ∅ does not exist (p. 461).
6. None of the four sources reports a mechanised proof of interpolation for a linear or substructural logic. This is a statement about these files only, not about the literature.
