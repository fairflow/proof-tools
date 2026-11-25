# GLS: measurements

What runs, with its verdicts and its timings. Machine: Apple M4 Pro
(arm64), 48 GB, macOS 15.8.3; Lean 4.31.0. Date: 2026-11-25. Every time
is one run, on the clock; a time under 0.1 s is within the noise of
loading the imports, which is taken off. To run again, from
`calculi/GLS/` after `lake build GLS glsrun`:

    python3 -I Corpus/measure.py
    python3 -I Corpus/measure_set.py

## What runs

| procedure | Lean name | proved? | what it returns |
|---|---|---|---|
| the search over multisets | `search`, `proofOrRefutation` (`GLS/Search.lean`) | proved total and correct (S4) | a derivation in GLS as data, or a finite tree at whose root the sequent is false |
| the producer of certificates | `produce` (`GLS/Run.lean`) | checked answer by answer | a tree of moves, or a tree of worlds |
| the certifier of derivations | `treeCert`, `scriptCert` | sound by S1 | `Fam s`, the derivation as data |
| the certifiers against validity and derivability | `noValid`, `noDerivable` | S21 | `¬ Valid s`, `¬ Nonempty (Fam s)` |
| the engine, level 3 | `glsEngine`, `glsEngine_complete` | S22 | one side always answers |
| the search over sets | `searchSet`, `produceSet` (`GLS/SetSearch.lean`) | **not proved**: code | a tree of moves over sets, or a tree of worlds |
| the certifier over sets | `setCert` | S23 | `Nonempty (Fam s)`: that a derivation exists |
| the checked decisions | `derivableDecidableFast`, `validDecidableFast` | proved (they check the fast search's answer and fall back on `search`) | `Decidable` |

Level reached: 3 (a producer whose every answer is checked, and a proof
that one side always answers).

## The corpus

16 sequents (`GLS/Corpus/Basic.lean`), 8 derivable and 8 not, each with
its status and where the status is from. `glsrun facts` writes
`GLS/Corpus/Facts.lean`: 16 facts, each stated with its certificate and
checked by the kernel when the file is elaborated (1.5 s with its imports). `glsrun
status`: 16 of 16 agree with the recorded status. The derivable ones
have trees of 3 to 12 moves; the others are refuted on trees of 1 to 3
worlds.

Four families that grow:

    boxChain n   ⇒ □p → □ⁿ⁺¹p                                   derivable; GLR nested n + 1 deep
    kChain n     ⇒ □(p₀ → p₁) → … → □(pₙ₋₁ → pₙ) → □p₀ → □pₙ    derivable; one GLR, n uses of ImpL
    consis n     ⇒ □ⁿ⁺¹⊥ → □ⁿ⊥                                  not derivable; a chain of n + 1 worlds
    binTree n    ⇒ Dₙ                                           not derivable; a binary tree of 2ⁿ⁺¹ − 1 worlds

## Table 1: the search over multisets

Measured at 09:53, before the search over sets existed. Loading the
imports: 1.17 s, taken off the last three columns. Deadlines: the
producer 20 s, each check 30 s. `flag`: cut off at the deadline; the
column stops there.

| family | n | verdict | size of the certificate | producer | the fact with its certificate (a tree): elaborated, and checked by the kernel | the fact with its script | the kernel running the search (`decide +kernel`) |
|---|---|---|---|---|---|---|---|
| boxChain | 4 | pass | 7 | 0 ms | 0.02 s | 0.05 s | 0.01 s |
| boxChain | 8 | pass | 11 | 0 ms | 0.00 s | 0.02 s | 0.07 s |
| boxChain | 12 | pass | 15 | 0 ms | 0.06 s | 0.07 s | 1.28 s |
| boxChain | 16 | pass | 19 | 8 ms | 0.05 s | 0.10 s | flag (> 30 s) |
| boxChain | 20 | pass | 23 | 132 ms | 0.08 s | 0.07 s | not run |
| boxChain | 24 | pass | 27 | 2229 ms | 0.00 s | 0.00 s | not run |
| boxChain | 28 | flag | | flag (> 20 s) | not run | not run | not run |
| kChain | 4 | pass | 15 | 0 ms | 0.00 s | 0.00 s | 0.00 s |
| kChain | 16 | pass | 51 | 0 ms | 0.00 s | 0.00 s | 0.00 s |
| kChain | 32 | pass | 99 | 0 ms | 0.06 s | 0.27 s | 0.29 s |
| kChain | 64 | pass | 195 | 2 ms | 0.72 s | 1.53 s | 2.16 s |
| kChain | 128 | pass | 387 | 11 ms | 3.79 s | 8.56 s | 12.22 s |
| kChain | 256 | pass | 771 | 76 ms | 19.03 s | flag (> 30 s) | flag (> 30 s) |
| kChain | 512 | pass | 1539 | 551 ms | flag (> 30 s) | not run | not run |
| consis | 4 | fail | 5 | 0 ms | 0.12 s | no script: not a derivation | 0.17 s |
| consis | 8 | fail | 9 | 0 ms | 0.09 s | no script: not a derivation | 0.28 s |
| consis | 12 | fail | 13 | 1 ms | 0.09 s | no script: not a derivation | 3.49 s |
| consis | 16 | fail | 17 | 12 ms | 0.00 s | no script: not a derivation | flag (> 30 s) |
| consis | 20 | fail | 21 | 207 ms | 0.19 s | no script: not a derivation | not run |
| consis | 24 | fail | 25 | 3776 ms | 0.04 s | no script: not a derivation | not run |
| consis | 28 | flag | | flag (> 20 s) | not run | not run | not run |
| binTree | 2 | fail | 7 | 0 ms | 0.00 s | no script: not a derivation | 0.00 s |
| binTree | 4 | fail | 31 | 0 ms | 0.00 s | no script: not a derivation | 0.48 s |
| binTree | 6 | fail | 127 | 8 ms | 0.18 s | no script: not a derivation | 11.37 s |
| binTree | 8 | fail | 511 | 335 ms | 0.14 s | no script: not a derivation | flag (> 30 s) |
| binTree | 10 | flag | | flag (> 20 s) | not run | not run | not run |

**The frontier of the first search**: the producer is cut off at
`boxChain 28`, `consis 28` and `binTree 10`; its time doubles with each
box. The kernel running the search itself (`decide +kernel` on `Valid
s`) is cut off at `boxChain 16`, `consis 16`, `binTree 8`, `kChain 256`.
A certificate, once had, is checked fast: a tree of moves for `boxChain
24` in under 0.1 s. `kChain` is limited on the other side: its tree of
moves at 512 (1 539 moves, 982 MB as Lean source) is not elaborated in
30 s.

**The cause** (`decisions.md`, 09:48): the premise of GLR holds `B, □B`
for every boxed formula of the antecedent, with repetitions, so the
antecedents double at each nested GLR. A derivation of GLS as a term
holds those sequents, and the compiled search builds them. The cause is
the calculus on multisets as the source states it, not the order of the
search.

## Table 2: the search over sets

Measured at 13:20 to 13:27, **after** the repair of `dedup`
(`method-notes.md`, 26). Before the repair this search was cut off at
`kChain 16`, `consis 16` and `binTree 4` (20 s); that table is not
kept. Loading the imports: 0.91 s, taken off the last three columns.
The same deadlines.

| family | n | verdict | size of the certificate | the search over sets | the fact with its certificate, by `setCert` or `noDerivable` | the same tree of moves by `treeCert`: the derivation as data | the kernel running the decision over sets (`decide +kernel`) |
|---|---|---|---|---|---|---|---|
| boxChain | 16 | pass | 19 | 0 ms | 0.11 s | 0.02 s | 0.11 s |
| boxChain | 24 | pass | 27 | 0 ms | 0.17 s | 0.04 s | 0.26 s |
| boxChain | 32 | pass | 35 | 1 ms | 0.36 s | 0.06 s | 0.48 s |
| boxChain | 64 | pass | 67 | 2 ms | 2.06 s | 0.15 s | 2.53 s |
| boxChain | 128 | pass | 131 | 23 ms | 14.58 s | 0.47 s | 16.53 s |
| boxChain | 256 | pass | 259 | 333 ms | flag (> 30 s) | 1.84 s | flag (> 30 s) |
| kChain | 16 | pass | 51 | 1 ms | 0.57 s | 0.30 s | 0.86 s |
| kChain | 64 | pass | 195 | 11 ms | 20.60 s | 1.18 s | 29.52 s |
| kChain | 128 | pass | 387 | 85 ms | flag (> 30 s) | 4.54 s | flag (> 30 s) |
| kChain | 256 | pass | 771 | 632 ms | not run | 20.05 s | not run |
| kChain | 512 | pass | 1539 | 4918 ms | not run | flag (> 30 s) | not run |
| consis | 16 | fail | 17 | 0 ms | 0.31 s | not a derivation | 0.45 s |
| consis | 24 | fail | 25 | 0 ms | 0.27 s | not a derivation | 0.56 s |
| consis | 32 | fail | 33 | 1 ms | 0.33 s | not a derivation | 0.98 s |
| consis | 64 | fail | 65 | 2 ms | 1.33 s | not a derivation | 4.44 s |
| consis | 128 | fail | 129 | 26 ms | 9.76 s | not a derivation | flag (> 30 s) |
| consis | 256 | fail | 257 | 365 ms | flag (> 30 s) | not a derivation | not run |
| binTree | 4 | fail | 31 | 1 ms | 0.42 s | not a derivation | 0.94 s |
| binTree | 6 | fail | 127 | 5 ms | 0.19 s | not a derivation | 10.81 s |
| binTree | 8 | fail | 511 | 46 ms | 0.38 s | not a derivation | flag (> 30 s) |
| binTree | 10 | fail | 2047 | 402 ms | 2.07 s | not a derivation | not run |
| binTree | 12 | fail | 8191 | 3609 ms | 4.25 s | not a derivation | not run |

**The frontier over sets**: the search itself is not the limit on any
family measured (5 s at `kChain 512`, 3.6 s at `binTree 12`, under
0.4 s elsewhere). The limits are the kernel's checks:

* a derivable sequent: the tree of moves the search over sets returns,
  checked by `treeCert` (which gives the derivation in GLS as data),
  takes 1.8 s at `boxChain 256` and 20 s at `kChain 256`, and is cut
  off at `kChain 512`. The same tree checked by `setCert` is slower
  (cut off at `boxChain 256` and `kChain 128`): the check over sets
  removes repeated formulas at every step, and the kernel does that
  work in full, where on multisets it never looks beyond the formulas a
  move names. So the search over sets is the better producer and
  `treeCert` the better check. That a tree of moves over sets is
  always accepted by `treeCert` is **not proved** and not stated in
  Lean: it held on every member measured, and where it fails `setCert`
  still answers.
* a sequent that is not derivable: the tree of worlds checked by
  `noDerivable` takes 9.8 s at `consis 128` and is cut off at 256; 4 s
  at `binTree 12` (8 191 worlds).
* the kernel running the checked decision (`decide +kernel`): 16.5 s at
  `boxChain 128`, 29.5 s at `kChain 64`, 4.4 s at `consis 64`, 10.8 s
  at `binTree 6`; cut off one step later in each family.

Not measured: a member of a family between the last that passed and the
first that was cut off; memory; anything outside the four families and
the corpus. The build of the whole package from clean was not timed.
