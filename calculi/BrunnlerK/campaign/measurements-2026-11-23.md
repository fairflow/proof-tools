Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Date: 2026-11-23.  Loading the imports: 0.88 s, taken off the kernel times.
Deadlines: producer 10 s, each kernel check 30 s.  `flag`: cut off at the deadline, or not elaborated; the column stops there.

| family | n | verdict | size of the certificate | producer | the fact with its certificate: elaborated, and checked by the kernel | the kernel running the search (`decide +kernel`) |
|---|---|---|---|---|---|---|
| boxAnd | 2 | pass | 10 | 0 ms | 0.02 s | 0.05 s |
| boxAnd | 4 | pass | 25 | 0 ms | 0.03 s | 0.01 s |
| boxAnd | 8 | pass | 67 | 0 ms | 0.09 s | 0.04 s |
| boxAnd | 16 | pass | 199 | 0 ms | 0.32 s | 0.10 s |
| boxAnd | 32 | pass | 655 | 0 ms | 1.81 s | 0.44 s |
| boxAnd | 64 | pass | 2335 | 2 ms | flag: the term was not elaborated (maximum recursion depth) | 2.31 s |
| nest | 4 | pass | 6 | 0 ms | 0.05 s | 0.02 s |
| nest | 16 | pass | 18 | 0 ms | 0.05 s | 0.03 s |
| nest | 64 | pass | 66 | 1 ms | 0.48 s | 0.09 s |
| nest | 256 | pass | 258 | 116 ms | flag: the term was not elaborated (maximum recursion depth) | 0.20 s |
| nest | 1024 | flag | | flag (> 10 s) | not run | not run |
| boxOr | 2 | fail | 3 | 0 ms | 0.04 s | 0.02 s |
| boxOr | 4 | fail | 5 | 0 ms | 0.01 s | 0.02 s |
| boxOr | 8 | fail | 9 | 0 ms | 0.01 s | 0.04 s |
| boxOr | 16 | fail | 17 | 0 ms | 0.03 s | 0.13 s |
| boxOr | 32 | fail | 33 | 0 ms | 0.02 s | 0.48 s |
| boxOr | 64 | fail | 65 | 1 ms | 0.07 s | 2.04 s |
| late | 2 | pass | 1 | 0 ms | 0.01 s | 0.02 s |
| late | 4 | pass | 1 | 0 ms | 0.02 s | 0.01 s |
| late | 6 | pass | 1 | 0 ms | 0.01 s | 0.01 s |
| late | 8 | pass | 1 | 0 ms | 0.03 s | 0.03 s |
| late | 10 | pass | 1 | 0 ms | 0.05 s | 0.01 s |
| late | 12 | pass | 1 | 0 ms | 0.01 s | 0.01 s |
| late | 14 | pass | 1 | 0 ms | 0.01 s | 0.01 s |
| late | 16 | pass | 1 | 0 ms | 0.02 s | 0.02 s |

## What the figures say

Written by `Corpus/measure.py`, above; these lines by the operator.

* **The producer is not where time goes.** It answers every member tried
  in at most 2 ms, but for the family `nest`: 116 ms at depth 256 and no
  answer within 10 s at depth 1024. The search carries a proof of a box
  into its context once at each level (`Fam.lift`), which copies it.
* **The certificate, written out as a term, is.** Stating a fact with a
  tree of 655 moves takes 1.8 s; a tree of 2 335 moves, or one nested
  256 deep, is not elaborated at all (Lean's limit on the depth of
  recursion while it reads the term). These are limits of the term as
  text, met before the kernel sees it: the column measures parsing and
  elaboration together with the kernel's check, and does not separate
  them.
* **The kernel running the search itself is the cheaper route here**,
  at every size tried: 0.44 s against 1.81 s at `boxAnd 32`, and it
  still answers where the certificate is not elaborated. This is
  possible because the search is proved correct and is structural, so
  `Valid Γ` is decidable by evaluation. What the tree of moves gives
  that this does not is the proof itself, as a value of `K Γ` that can
  be printed, walked and compared.
* **Against validity the tree is small and cheap**: 65 nodes and 0.07 s
  at `boxOr 64`, where the kernel running the search takes 2.04 s.

## The frontier

The smallest members not settled within the budget, by route:

| route | family | first member not settled | why |
|---|---|---|---|
| the producer, 10 s | `nest` | between 257 and 1024 | the proof of a box is copied at each level |
| a fact with its certificate | `boxAnd` | between 33 and 64 (656 to 2 335 moves) | the term is not elaborated: recursion depth |
| a fact with its certificate | `nest` | between 65 and 256 | the same |
| the kernel running the search, 30 s | none reached | | the largest tried: `boxAnd 64` (2.31 s), `boxOr 64` (2.04 s), `nest 256` (0.20 s) |

## What the search learnt

In the first run of this script the family `late` (an instance of the
axiom, with `n` conjunctions beside it) had proofs of `2ⁿ⁺¹ − 1` rule
instances: 8 191 at `n = 12`, and at `n = 14` a certificate that was not
elaborated. A proof by hand has one. The search applied `∧` before it
looked for an axiom. It now looks for an axiom first
(`BrunnlerK/Search.lean`, `searchN`); the proofs of completeness and of
what rests on it did not change. The figures above are after that
change: one rule instance at every `n`. `boxAnd` became shorter by it as
well (655 moves for 1 120 at `n = 32`), and the kernel's run of the
search somewhat slower (0.44 s for 0.33 s), since it now looks for an
axiom at every step.
