# MALL: what runs, and how fast

Written 2026-11-26 10:58 GMT, from two runs of the same day (10:41 to
10:51, and 10:57). Machine: Apple M4 Pro, macOS 15.8.3, arm64; Lean
v4.31.0. The times are single runs, on a machine where other sessions
were building: read them for their order of magnitude.

## What runs

| | what | where | trusted? |
|---|---|---|---|
| the proved search | `searchCF Γ : Option (CF Γ)`: every formula as principal, every split at ⊗; proved complete; structural, so the kernel runs it | `MALL/Decide.lean` | it is a theorem: `Decidable (Derivable Γ)`, `Decidable (Valid Γ)` |
| the lazy search | `Lazy.prove Γ : Option (Cert S)`: input and output contexts, a flag for ⊤ | `MALL/Lazy.lean` | no: `partial`, not proved; its tree is checked |
| trees and scripts, checked | `treeCert`, `scriptCert`: `Cert.check` runs `step` | `MALL/Run.lean` | yes, through S1 |
| against derivability, by the decision | `noDerivable`, `noValid`: the certificate is `()`, the check is the proved search | `MALL/Run.lean` | yes, through S14 |
| against derivability, by a structure | `noDerivableBy`, `noValidBy`: a phase structure on a cyclic group, as data; the check computes the interpretation | `MALL/Model.lean`, `MALL/ModelRun.lean` | yes, through `ZModel.not_valid_of_refutes` and soundness |
| the producer of structures | `refuteBy Γ`: every structure on ℤ/1, ℤ/2, ℤ/3 for at most two letters; otherwise "weights" in ℤ/2 and ℤ/3 | `MALL/ModelRun.lean` | no, and not complete |
| the driver | `mallrun facts`, `status`, `run`, `cert`, `model` | `Main.lean` | no |

Level 3 (`reference/certify.md` §3): `decided` (S18). The lints of
`lean-certify`: R3 and R2 pass on `treeCert`, `noDerivable`, `noValid`,
`noDerivableBy`, `noValidBy`; R1 reports nothing on `produce`; R4 passes
on the facts of `MALL/RunTest.lean` and `MALL/ModelTest.lean`.

## The corpus

38 sequents of known status (`MALL/Corpus/Basic.lean`): 23 derivable, 15
not. `mallrun status`: on all 38 the lazy search, the proved search and
the decision agree with the status. `MALL/Corpus/Facts.lean` (written by
`mallrun facts`) has 38 facts, each checked by the kernel: 23 derivations
by the lazy search's tree; 14 refutations by a finite phase structure;
1 (`halfDistribConv`, three letters) by the decision, the producer of
structures having found none.

**Negative tests** (R9), each rejected in the kernel
(`MALL/Test.lean`, `MALL/RunTest.lean`, `MALL/ModelTest.lean`): a tree
with a wrong move; with a wrong split; with a split that uses a formula
twice (a contraction); an axiom with a formula left over (a weakening); a
tree that stops early; a script with a wrong line, and one that stops
early; the check against derivability on four derivable sequents; a
structure that does not refute; and every structure on ℤ/1, ℤ/2, ℤ/3 for
two letters (584) against four derivable sequents.

## The families

`chain n`: `⊢ p₀⊥, p₀ ⊗ p₁⊥, …, pₙ₋₁ ⊗ pₙ⊥, pₙ`, with `n` tensors.
`fan n`: one nest of `n` tensors and its `n + 1` letters, in the order
that suits a search least. `slack n`: `⊢ p₀ ⊗ ⊤, p₀⊥, p₁, …, pₙ`.
`withTree n`: `⊢ p⊥, W` with `W` a full tree of & of depth `n` over `p`.
`chainBad`, `fanBad`: `chain` and `fan` with one letter changed, so that
there is no derivation.

Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Date: 2026-11-26.  Loading the imports: 0.93 s, taken off the times of the last two columns.
Deadlines: each producer 20 s, each check 30 s.  `flag`: cut off at the deadline, or not elaborated; the column stops there.

| family | n | formulas in the sequent | verdict | the lazy search: moves, nesting, time | the proved search: time | the fact with the lazy search's tree: elaborated, and checked by the kernel | the kernel running the proved search (`decide +kernel`) |
|---|---|---|---|---|---|---|---|
| chain | 2 | 4 | derivable | 5 moves, nesting 3, 0 ms | 0 ms | 0.10 s | 0.13 s |
| chain | 4 | 6 | derivable | 9 moves, nesting 5, 0 ms | 2 ms | 0.11 s | 1.50 s |
| chain | 6 | 8 | derivable | 13 moves, nesting 7, 0 ms | 1680 ms | 0.13 s | flag (> 30 s) |
| chain | 8 | 10 | derivable | 17 moves, nesting 9, 0 ms | flag (> 20 s) | 0.15 s | not run |
| chain | 10 | 12 | derivable | 21 moves, nesting 11, 0 ms | not run | 0.39 s | not run |
| chain | 12 | 14 | derivable | 25 moves, nesting 13, 0 ms | not run | 0.27 s | not run |
| chain | 16 | 18 | derivable | 33 moves, nesting 17, 0 ms | not run | 0.39 s | not run |
| chain | 24 | 26 | derivable | 49 moves, nesting 25, 0 ms | not run | 0.50 s | not run |
| chain | 32 | 34 | derivable | 65 moves, nesting 33, 0 ms | not run | 0.73 s | not run |
| chain | 48 | 50 | derivable | 97 moves, nesting 49, 1 ms | not run | 1.76 s | not run |
| chain | 64 | 66 | derivable | 129 moves, nesting 65, 3 ms | not run | 3.08 s | not run |
| fan | 2 | 4 | derivable | 5 moves, nesting 3, 0 ms | 0 ms | 0.15 s | 0.23 s |
| fan | 4 | 6 | derivable | 9 moves, nesting 5, 0 ms | 0 ms | 0.25 s | 0.25 s |
| fan | 6 | 8 | derivable | 13 moves, nesting 7, 0 ms | 0 ms | 0.28 s | 0.32 s |
| fan | 8 | 10 | derivable | 17 moves, nesting 9, 0 ms | 2 ms | 0.30 s | 1.32 s |
| fan | 10 | 12 | derivable | 21 moves, nesting 11, 0 ms | 27 ms | 0.24 s | 8.15 s |
| fan | 12 | 14 | derivable | 25 moves, nesting 13, 0 ms | 440 ms | 0.24 s | flag (> 30 s) |
| fan | 16 | 18 | derivable | 33 moves, nesting 17, 0 ms | flag (> 20 s) | 0.60 s | not run |
| fan | 24 | 26 | derivable | 49 moves, nesting 25, 0 ms | not run | 0.81 s | not run |
| fan | 32 | 34 | derivable | 65 moves, nesting 33, 1 ms | not run | 1.36 s | not run |
| fan | 48 | 50 | derivable | 97 moves, nesting 49, 1 ms | not run | 3.28 s | not run |
| fan | 64 | 66 | derivable | 129 moves, nesting 65, 2 ms | not run | 6.16 s | not run |
| slack | 2 | 4 | derivable | 3 moves, nesting 2, 0 ms | 0 ms | 0.10 s | 0.12 s |
| slack | 4 | 6 | derivable | 3 moves, nesting 2, 1 ms | 0 ms | 0.17 s | 0.36 s |
| slack | 8 | 10 | derivable | 3 moves, nesting 2, 0 ms | 0 ms | 0.22 s | 0.49 s |
| slack | 12 | 14 | derivable | 3 moves, nesting 2, 0 ms | 82 ms | 0.22 s | 16.46 s |
| slack | 16 | 18 | derivable | 3 moves, nesting 2, 0 ms | flag (> 20 s) | 0.16 s | flag (> 30 s) |
| slack | 24 | 26 | derivable | 3 moves, nesting 2, 0 ms | not run | 0.55 s | not run |
| slack | 32 | 34 | derivable | 3 moves, nesting 2, 0 ms | not run | 0.36 s | not run |
| slack | 64 | 66 | derivable | 3 moves, nesting 2, 0 ms | not run | 1.00 s | not run |
| withTree | 2 | 2 | derivable | 7 moves, nesting 3, 0 ms | 0 ms | 0.19 s | 0.19 s |
| withTree | 4 | 2 | derivable | 31 moves, nesting 5, 0 ms | 0 ms | 0.21 s | 0.21 s |
| withTree | 6 | 2 | derivable | 127 moves, nesting 7, 1 ms | 0 ms | 0.25 s | 0.26 s |
| withTree | 8 | 2 | derivable | 511 moves, nesting 9, 1 ms | 0 ms | 0.59 s | 0.19 s |
| withTree | 10 | 2 | derivable | 2047 moves, nesting 11, 1 ms | 1 ms | 2.26 s | 0.21 s |
| withTree | 12 | 2 | derivable | 8191 moves, nesting 13, 4 ms | 3 ms | 10.52 s | 0.30 s |
| chainBad | 2 | 4 | none found | none, 0 ms | 0 ms (none) | no tree: not a derivation | 0.24 s |
| chainBad | 4 | 6 | none found | none, 0 ms | 6 ms (none) | no tree: not a derivation | 6.74 s |
| chainBad | 6 | 8 | none found | none, 4 ms | 12794 ms (none) | no tree: not a derivation | flag (> 30 s) |
| chainBad | 8 | 10 | none found | none, 256 ms | flag (> 20 s) | no tree: not a derivation | not run |
| chainBad | 10 | 12 | not derivable | flag (> 20 s) | not run | not run | not run |
| fanBad | 2 | 4 | none found | none, 0 ms | 0 ms (none) | no tree: not a derivation | 0.50 s |
| fanBad | 4 | 6 | none found | none, 0 ms | 0 ms (none) | no tree: not a derivation | 0.24 s |
| fanBad | 6 | 8 | none found | none, 0 ms | 1 ms (none) | no tree: not a derivation | 0.32 s |
| fanBad | 8 | 10 | none found | none, 0 ms | 1 ms (none) | no tree: not a derivation | 0.74 s |
| fanBad | 10 | 12 | none found | none, 0 ms | 20 ms (none) | no tree: not a derivation | 4.51 s |
| fanBad | 12 | 14 | none found | none, 0 ms | 354 ms (none) | no tree: not a derivation | flag (> 30 s) |
| fanBad | 16 | 18 | none found | none, 0 ms | flag (> 20 s) | no tree: not a derivation | not run |

Of the measurements above, the last column of `chainBad` and `fanBad` is
the kernel running the proved search to say no.

## Refutations by a finite phase structure

Loading the imports: 1.12 s, taken off the last column.  Deadline: 30 s each.

| family | n | formulas in the sequent | the structure found | the producer | the fact with its structure: elaborated, and checked by the kernel |
|---|---|---|---|---|---|
| chainBad | 4 | 6 | refuted in ℤ/2 | 0 ms | 0.00 s |
| chainBad | 8 | 10 | refuted in ℤ/2 | 0 ms | 0.02 s |
| chainBad | 16 | 18 | refuted in ℤ/2 | 0 ms | 0.05 s |
| chainBad | 32 | 34 | refuted in ℤ/2 | 3 ms | 0.13 s |
| chainBad | 64 | 66 | refuted in ℤ/2 | 10 ms | 0.33 s |
| chainBad | 128 | 130 | refuted in ℤ/2 | 40 ms | 0.84 s |
| chainBad | 256 | 258 | refuted in ℤ/2 | 168 ms | 2.29 s |
| fanBad | 4 | 6 | refuted in ℤ/3 | 0 ms | 0.04 s |
| fanBad | 8 | 10 | refuted in ℤ/3 | 1 ms | 0.14 s |
| fanBad | 16 | 18 | refuted in ℤ/3 | 1 ms | 0.31 s |
| fanBad | 32 | 34 | refuted in ℤ/3 | 3 ms | 8.42 s |
| fanBad | 64 | 66 | refuted in ℤ/3 | 11 ms | 0.91 s |
| fanBad | 128 | 130 | refuted in ℤ/3 | 42 ms | 1.51 s |
| fanBad | 256 | 258 | refuted in ℤ/3 | 174 ms | 3.79 s |

`fanBad 32` took 8.42 s in that run and 0.91 s at twice the size. Three
runs of it by hand afterwards gave 0.46 s, 0.72 s and 6.91 s (less the
imports). The variation is not explained; it is not in the certificate.

## What the measurements say

* **The proved search is exponential on every family with ⊗.** It tries
  each formula as principal and each of the 2ⁿ splits. Compiled, it
  passes 20 s at 10 formulas (`chain 8`) to 18 (`fan 16`, `slack 16`).
  In the kernel it passes 30 s at 8 formulas (`chain 6`), 14 (`fan 12`)
  and 18 (`slack 16`).
* **The lazy search is linear where there is a derivation**: 3 ms at 66
  formulas, on `chain`, `fan` and `slack`. Its tree has two moves for
  each ⊗ and an axiom; the kernel checks it in 3 s (`chain 64`) to 6 s
  (`fan 64`), parsing and elaboration included.
* **Where there is no derivation the lazy search is exponential too**
  on `chainBad` (4 ms at 8 formulas, 256 ms at 10, over 20 s at 12): to
  say no it must try every way to use the context. On `fanBad` it says
  no at once.
* **A finite phase structure says no where neither search does.** On
  `chainBad` and `fanBad` a structure of weights (ℤ/2 or ℤ/3, the
  antiphases {0}) is found in milliseconds and checked by the kernel in
  0.8 s to 1.5 s at 130 formulas, 2.3 s to 3.8 s at 258.
* **A tree of & doubles**: `withTree 12` is 8 191 moves, found in 4 ms
  and checked in 10.5 s; there the kernel running the proved search
  (0.30 s) is the cheaper, since nothing is split.

## The frontier

* A sequent that **has a derivation**: the lazy search, then
  `treeCert`. Not measured beyond 66 formulas and 8 191 moves; no limit
  of the term's elaboration was reached (the facts are written with
  `maxRecDepth 100000`, nesting 65).
* A sequent that **has none**: (a) to 6 formulas on `chainBad` and 12
  on `fanBad`, the decision in the kernel (`chainBad 4`, 6 formulas, 6.7 s; `chainBad
  6`, 8 formulas, over 30 s; `fanBad 10`, 12 formulas, 4.5 s); (b) at
  any size tried, a finite phase structure, **where the producer finds
  one**. It finds one for 14 of the 15 such sequents of the corpus and
  for both families. It is not complete: it tries all small structures
  only for at most two letters, and weights otherwise. The smallest
  input here that it does not settle is `halfDistribConv`, `⊢ ((p ⊗ q)
  & (p ⊗ r))⊥, p ⊗ (q & r)`, which the decision settles (2 formulas).
  **Not settled by anything here within its deadline**: a sequent with
  no derivation, ten or more formulas with ⊗, and no countermodel
  among the structures tried. None is in the corpus; `chainBad 10` with
  a formula such as `halfDistribConv` added to it would be one (not
  tried).
* The finite model property (S17) says a finite structure exists for
  every sequent with no derivation. It does not say a cyclic group, and
  the structure of its proof is too large to write down. So "a better
  producer of structures" is the open end of this stage.
