# Intuitionistic variants of GL: the literature, the feasibility, consistency

2026-11-26. Operator: Claude Opus 5.5, with one agent for the literature.
The reviewer's task, verbatim:

> (B) report on literature and feasibility of extending these results to
> an intuitionistic setting; consistent or not?

**Who read what.** The sources were read by the literature agent of this
session. Its notes list, for each source, the sections it read or that it
had only the abstract. I read its notes, not the papers. Below, READ means
the agent read the text; *abstract* means it had only the abstract;
*cited* means it is known only through another source. The elementary
facts about GL in §3 were checked again here by the GLS search, and are
pinned in `GLS/InterpolationTest.lean`. The facts about the intuitionistic
logics themselves were checked by hand (by the agent), not by machine.

**In short.**

* **Consistent.** No intuitionistic variant contradicts a classical result
  proved here. iGL is a sublogic of GL, and adding excluded middle to it
  gives GL exactly. The others (iSL, KM, mHC, the provability logic of HA)
  prove principles that GL does not, such as `p → □p` and `¬¬□⊥`. Their
  classical versions are not GL but extensions of it: for iSL and KM,
  `Ver = K + □⊥`. They are consistent extensions, and their `□` means
  something else.
* **Uniform interpolation**: PROVED for iSL and for KM, OPEN for iGL,
  REFUTED for iK4.
* **Feasibility.** iSL is the best-prepared target: a strongly terminating
  calculus, syntactic cut elimination and uniform interpolation, all
  mechanised in Coq, and a semantic proof of uniform interpolation to
  compare with the route of report A. iGL's uniform interpolation is an
  open problem, which the semantic route of report A could be tried on.

## 1. The logics

Box-only language; `⊡A := A ∧ □A`.

| logic | axioms, over IPC | frames (birelational: `≤` intuitionistic, `R` modal) |
|---|---|---|
| iGL | K + Löb `□(□A→A)→□A` | `R` transitive and conversely well-founded; `w ≤ v R x ⇒ w R x` |
| iSL | K + strong Löb `(□A→A)→A`; equivalently iGL + CP `A→□A` | iGL frames with `R ⊆ ≤` |
| mHC (Esakia) | K + `p→□p` + `□p→(q∨(q→p))` | "transits": `R` is the strict part of `≤` |
| KM (Kuznetsov–Muravitsky) | mHC + `(□p→p)→p` | as mHC, with `R` conversely well-founded |
| iK4 | K + `□p→□□p` | `R` transitive |
| PL(HA) | iGL + further principles, e.g. Leivant's `□(B∨C)→□(□B∨C)` | — |

## 2. What is known, logic by logic

P = PROVED (a proof exists, source named), R = REFUTED, O = OPEN or no
result found, C = claimed but not refereed.

| logic | FMP | cut-free calculus | naive search terminates | syntactic cut elimination | Craig | UI | formalised |
|---|---|---|---|---|---|---|---|
| GL (here) | P | GLS (multi-succedent) | with the IdB check | P | P | **P** (report A) | Coq; Lean (this repository) |
| iGL | P [Mojtahedi, Thm 2.3] | G3iGL, G4iGL (single) | G4iGL loops only on provable sequents; a local check ends it [Goré–Shillito 2022] | P [vdG–Iemhoff 2021; Goré–Shillito 2022] | P [vdG–Iemhoff 2021] | **O** [Férée et al. 2024; Visser–Litak 2024] | Coq [Goré–Shillito 2022] |
| iSL | P [vdG–Iemhoff, §7] | G3iSL, G4iSL, G4iSLt (single) | G4iSLt: yes [Shillito et al. 2023] | P | P | **P**, twice [Férée et al. 2024, Coq; Visser–Litak 2024, semantic] | Coq |
| KM | P [Muravitsky 1981, cited] | G4KM (multi-succedent) [Férée–Shillito 2026] | yes | P | P (from UI) | **P** [Férée–Shillito 2026, Rocq, preprint] | Rocq |
| mHC | O | O | O | O | O | O | none found |
| iK4 | — | — | — | — | — | **R** [van der Giessen 2022, via Iemhoff–Jalali] | none found |
| PL(HA) | — | none | — | — | O | O | C: axiomatised, decidable [Mojtahedi, arXiv v4, Jan 2026, not refereed] |

Notes on the table:

* **iGL.** The NDJFL paper of van der Giessen and Iemhoff (2021), which
  gives G3iGL and G4iGL, was not obtained (*abstract*). Its rules are
  known through their iSL paper (READ, §§1–2, 7, 9) and through Goré and
  Shillito, AiML 2022 (READ in part), who prove cut elimination for G4iGL
  directly and verify it in Coq. Uniform interpolation for iGL is stated
  open by Férée, van der Giessen, van Gool and Shillito (IJCAR 2024, READ
  in part) and by Visser and Litak (arXiv 2404.11969, READ in part).
  Van Gool's 2026 survey chapter reports, in a footnote, an *unpublished*
  proof by van der Giessen, Sierra Miranda and Menéndez Turata (*cited*;
  treat as unconfirmed).
* **iSL.** G4iSLt (Shillito, van der Giessen, Goré, Iemhoff, TABLEAUX 2023,
  READ §1) is the calculus where naive backward search strongly terminates,
  with no loop check, and cut elimination is direct. Uniform interpolation
  has two proofs: Pitts-style in Coq (Férée et al. 2024), and model-theoretic
  by bounded bisimulation (Visser and Litak 2024). The second is the same
  kind of proof as report A's.
* **KM.** Férée and Shillito (arXiv 2602.16445, READ) give the first
  multi-succedent G4-style calculus for KM. Its `→R` has two premises: one
  for the reflexive step and one for the strict successor. Naive search
  terminates and cut elimination is syntactic, all in Rocq. The agent could
  not confirm the IJCAR 2026 venue.
* **Correction to the brief.** "Uniform interpolation with constructive
  diamond" (van der Giessen and Shillito) is about CK and WK, not about a
  provability logic, and appeared at IJCAR 2026, not AiML 2026.
* **Translations** (PROVED in the sources): KM ⊢ A iff GL ⊢ T(A)
  (Kuznetsov–Muravitsky, re-proved by Bezhanishvili and Cleani 2025, READ
  §5), and the lattices of normal extensions match, NExt(KM) ≅ NExt(GL).
  For mHC: mHC ⊢ A iff K4.Grz ⊢ #A (Esakia 2006, READ in part), with
  NExt(mHC) ≅ NExt(K4.Grz). In this sense KM, not iGL, is "the
  intuitionistic GL": its translation into GL is faithful. iGL is the
  intuitionistic GL in the other sense, of having GL's axioms.

## 3. Consistent or not?

The question is whether an intuitionistic variant sits consistently with
classical GL, or contradicts it. There are four separate answers.

**(i) Sublogic of GL?** iGL: yes. Every axiom and rule of iGL is GL-valid.
iK4: yes. iSL, KM, mHC: **no**, since they prove `p → □p`, and iSL and KM
also prove `¬¬□⊥`. PL(HA): **no**, since it contains Leivant's principle.
Checked here by the search (`#guard`, which runs the search; the kernel does not check these):

    GL ⊬ □⊥     GL ⊬ ¬¬□⊥     GL ⊬ p → □p     GL ⊬ □(p ∨ q) → □(□p ∨ q)

**(ii) The classical collapse** (add excluded middle):

* iGL + EM = GL.
* iSL + EM = KM + EM = **Ver** = K + `□⊥`, the logic of the one-point
  irreflexive frame. Strong Löb `(□A → A) → A` is classically `□A ∨ A`,
  and at `A := ⊥` it is `□⊥`. Intuitionistically that instance is only
  `¬¬□⊥`. Checked here:

      ((□p → p) → p) ↔ (□p ∨ p)          ((□⊥ → ⊥) → ⊥) ↔ □⊥

  are derivable in GLS, and so is `□⊥ ⇒ (□p → p) → p`: with `□⊥`, every
  instance of strong Löb holds.
* mHC + EM = K + `(p → □p)`. Joined with GL it is again Ver, because a
  single instance of `p → □p` already gives `□⊥` in GL. Checked here:

      ⇒ (¬□⊥ → □¬□⊥) → □⊥

  is derivable in GLS. With Löb at `⊥`, `□¬□⊥ → □⊥` is the formalised
  second incompleteness theorem.
* PL(HA) + EM proves `□□⊥` (the agent's derivation by hand, from
  Leivant's principle; not machine-checked), and is contained in Ver.

Ver is consistent, and is itself a finite irreflexive transitive tree's
logic (the one-point tree). By Makinson's theorem (cited from memory by
the agent, not re-read), every consistent normal extension of GL is
contained in Ver. So none of these logics is inconsistent with GL. Their
classical versions are GL's extensions, up to the largest one.

**(iii) Faithful translations.** KM embeds faithfully into GL, and mHC into
K4.Grz. No faithful translation of iSL into GL was found.

**(iv) Does any intuitionistic result contradict a result proved here?**
No. For iGL: iGL ⊆ GL and iGL + EM = GL, so an iGL theorem refuted by one
of the finite trees of `GLS/Search.lean` would be a GL theorem refuted
there, which soundness forbids. The metatheorems (cut admissibility,
Craig interpolation, the finite model property, decidability) are proved
for each logic separately and do not transfer in either direction, so
they cannot conflict. In particular, "GL has uniform interpolation, iGL's
is open" is not a tension. Uniform interpolation passes in neither
direction between a logic and its classical version: K4 and iK4 both lack
it, while iSL has it and so does its collapse Ver (trivially). For iSL,
KM, mHC and PL(HA), the principles GL lacks (`p → □p`, `¬¬□⊥`, Leivant)
show only that their `□` is a different modality. It is a strict-successor
step for KM and iSL, slow provability for iSL in arithmetic (Visser and
Zoethout, *cited*), and HA-provability for PL(HA).

## 4. Feasibility: what would transfer, and at what cost

The GLS development is 2,474 lines of theory (formulas, the two families,
semantics, soundness, the tree model, the measure, the search,
completeness, the structural rules, inversion, contraction, PS, cut),
plus 983 for uniform interpolation. What an intuitionistic version would
reuse:

| part | transfers? | cost |
|---|---|---|
| the campaign's method and tools (`ProofTools`, the explorer, `#rules`, `#slime`, `#statement`, the certifiers) | yes, unchanged | none |
| formulas | add primitive `∧`, `∨`: they are not definable intuitionistically (report C, §2) | small |
| the calculus | new: G4iSLt or G4iGL (single-succedent), or G4KM (multi-succedent) | the rule table and transcription, as stage 1 of a campaign |
| structural rules, inversion, contraction | new proofs, same shape. In G4 calculi, `→L` is not invertible, and contraction needs the Dyckhoff–Negri analysis | moderate; the Coq proofs are a guide |
| termination | new measure (Dyckhoff's weight, multiset ordering); `GLS/Measure.lean`'s usable-boxes count carries over for the modal rule | moderate |
| cut admissibility | new; the Coq files (mhd technique) give the route | the largest single item, as it was here |
| the semantics | birelational models: two relations, persistence of the valuation along `≤`. `Tree` would carry two kinds of edge, or a forest of `≤`-trees with `R` between them | moderate |
| soundness | same shape; persistence lemma added | small |
| completeness with countermodels | the hardest transfer. Here the search is "invertible rules, then GLR on every box", and refuting trees are glued under a new root. Intuitionistic search must try the non-invertible rules (`→R` of G4, the modal rule), and the countermodel is built from all failed branches, as in Pinto–Dyckhoff or the countermodel construction of van der Giessen–Iemhoff §7 | large; a design question for stage 0 |
| uniform interpolation (report A's route) | plausibly transfers to iSL: interpolant along the search, correctness by bisimulation on finite birelational trees. The flattening must keep `≤`-persistence when `p` is reset, and Visser–Litak's semantic proof shows how bounded bisimulation is set up there | moderate to large, and research-grade |
| uniform interpolation for iGL | OPEN in the literature. The semantic route is one way to attack it, and nothing here says it will succeed | research |

**Recommendation.** If an intuitionistic campaign is wanted, take **iSL
with G4iSLt** as the source. Everything is proved in Coq to transcribe
from, and there is a semantic uniform-interpolation proof to compare
with report A's route. Do stage 0's countermodel question first, because
it decides whether the search can return refutations as data, as here.
**KM with G4KM** is the multi-succedent alternative, closer in shape to
GLS, but its source is a preprint. **iGL** is the target where something
new could be proved, its uniform interpolation, but that is research,
not adoption.

## 5. Sources (as the agent read them)

* van der Giessen, Iemhoff, *Sequent calculi for intuitionistic
  Gödel–Löb logic*, NDJFL 62 (2021) — abstract only.
* van der Giessen, Iemhoff, *Proof theory for intuitionistic strong Löb
  logic*, arXiv 2011.10383 — READ §§1, 2, 7, 9.
* Shillito, van der Giessen, Goré, Iemhoff, TABLEAUX 2023, arXiv
  2309.00486 — READ §1.
* Goré, Shillito, *Direct elimination of additive-cuts in GL4ip*, AiML 14
  (2022) — READ abstract, §1, parts of §§3–4.
* Férée, van der Giessen, van Gool, Shillito, IJCAR 2024, arXiv
  2402.10494 — READ in part.
* Visser, Litak, *Lewis and Brouwer meet strong Löb*, arXiv 2404.11969 —
  READ abstract, §§1, 2.2–2.7, 6.2–6.3.
* Férée, Shillito, *Pitts and intuitionistic multi-succedent*, arXiv
  2602.16445 — READ §§1–3, 5, 6.
* van der Giessen, Shillito, *Uniform interpolation with constructive
  diamond*, IJCAR 2026 — abstract and §1.
* Esakia, *The modalized Heyting calculus*, JANCL 16 (2006) — READ in part.
* Bezhanishvili, Cleani, arXiv 2511.09824 and 2206.08863 — READ in part.
* Muravitsky, arXiv 1702.00054 and 1612.05273 — READ in part; *Logic KM: a
  biography* (2014) — not obtained.
* Clouston, Goré, FoSSaCS 2015 — READ in part.
* Das, van der Giessen, Marin, CSL 2024 — READ abstract, §§1, 9.
* Mojtahedi, *On the provability logic of HA*, arXiv 2206.00445 v4 — READ
  abstract, §§1, 2.4, 2.6.
* Iemhoff, Jalali, TACL 2022 lecture notes, arXiv 2305.10888 — READ §7.5.
* van der Giessen, Jalali, Kuznets, arXiv 2602.16318 — abstract, §3.
* van der Giessen, PhD thesis, Utrecht 2022 — not obtained.
