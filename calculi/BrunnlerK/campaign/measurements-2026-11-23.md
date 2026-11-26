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

## `ksearch prove` beyond the corpus (2026-11-26)

The same machine. `python3 Corpus/prove_families.py --lean-deadline=240
<members>`: the command on a member of a family, then the printed file
elaborated by `lake env lean -M 8000` (8 GB) within 240 s, each in a
process group that is ended at the deadline. `tree k` is F_k with
F_0 = p and F_(k+1) = □F_k ∨ □F_k (not valid; a countermodel of
2^(k+1) − 1 nodes); `chain n` is □ⁿp (not valid; a chain of n + 1
nodes); both are written in the script. The rows for `chain` are of a
second run, after the depth of the sequent was taken out of the test on
the "not derivable" side; nothing else differs between the two runs.

| member | answer | size of the certificate | `ksearch prove` | the file | elaborated | time |
|---|---|---|---|---|---|---|
| `boxAnd 16` | derivable | 199 moves | 0.03 s | 60 838 bytes | yes | 1.2 s |
| `boxAnd 64` | derivable | 2 335 moves | 0.03 s | 2 594 679 bytes | yes | 11.6 s |
| `boxAnd 96` | derivable, on the program's check | 5 039 moves | 0.06 s | 8 378 344 bytes | no: cut off at 240 s | |
| `nest 64` | derivable | 66 moves | 0.03 s | 35 837 bytes | yes | 1.8 s |
| `nest 256` | derivable | 258 moves | 0.15 s | 483 774 bytes | yes | 11.0 s |
| `nest 384` | derivable | 386 moves | 0.44 s | 1 069 118 bytes | yes | 26.8 s |
| `nest 512` | derivable, on the program's check | 514 moves | 1.03 s | 1 883 917 bytes | no: `lean::memory_exception`, excessive memory consumption, at 46 s | |
| `boxOr 16` | not derivable | 17 nodes | 0.03 s | 2 649 bytes | yes | 0.9 s |
| `late 16` | derivable | 1 move | 0.03 s | 1 861 bytes | yes | 0.9 s |
| `tree 8` | not derivable | 511 nodes | 0.03 s | 18 639 bytes | yes | 1.0 s |
| `tree 14` | not derivable | 32 767 nodes | 0.06 s | 1 115 345 bytes | yes | 12.1 s |
| `tree 16` | not derivable | 131 071 nodes | 0.19 s | 4 457 682 bytes | yes | 49.7 s |
| `tree 18` | not run: a text of 2 621 431 bytes is longer than a command line ("Argument list too long") | | | | | |
| `chain 512` | not derivable | 513 nodes | 0.66 s | 14 103 bytes | yes | 1.0 s |
| `chain 1024` | not derivable | 1 025 nodes | 0.03 s | 26 904 bytes | yes | 1.3 s |
| `chain 2048` | not derivable | 2 049 nodes | 0.03 s | 52 504 bytes | yes | 1.6 s |
| `chain 4096` | not derivable | 4 097 nodes | 0.03 s | 103 704 bytes | yes | 2.6 s |

**The frontier of the file, with Lean's limits lifted.** A tree of moves:
checked at 2 335 moves and 2.6 MB, not within 240 s at 5 039 moves and
8.4 MB. A derivable sequent that is deep: checked at depth 385, stopped
at 8 GB at depth 513, though that file is the smaller (1.9 MB): a move
carries its formula, so depth costs by itself. A countermodel: checked at
131 071 nodes; the next member does not fit a command line; depth costs
nothing there (4 097 nodes in a chain, 2.6 s). The command prints each
of these in about a second or less, so between the sizes checked and the
sizes not checked the program's answer is ahead of the kernel's: there
the first line says "on the program's check" (`seenDepth`, `seenMoves`,
`seenTree` in `Main.lean`).

The rows "a fact with its certificate" of the frontier above (between 33
and 64 for `boxAnd`, between 65 and 256 for `nest`) were of Lean's
default limits, and of a certificate printed by `Repr`.

**The certificate printed by `Repr`, and printed directly.** `Repr`
indents a line by the depth of its place in the term.

| member | the file by `Repr` | of which indentation | the file by the printers of `Main.lean` | elaborated: before, after |
|---|---|---|---|---|
| `boxAnd 64` | 86 267 339 bytes | 81 763 131 (95%) | 2 594 679 bytes | 17.9 s, 11.6 s |
| `nest 256` | 41 839 046 bytes | not counted | 483 774 bytes | 14.6 s, 11.0 s |
| `boxAnd 128` | 1 256 703 468 bytes (`ksearch cert`) | not counted | 19 509 529 bytes | neither was elaborated |

**The check once, and twice.** The file for `tree 12` and for `tree 14`,
with `notValid` and `notDerivable` each left to run the check (the
default argument of `verdict`) and with both given the one theorem
`checked`: 3.85 s and 3.93 s; 13.31 s and 13.13 s. No difference to be
seen: at these sizes the time is Lean reading the term, not the kernel's
check. On the "derivable" side there was one check before as well
(`derivable` is `⟨proof⟩`); with the tree of moves named and the check a
theorem, `boxAnd 64` took 15.7 s for 17.9 s and `nest 256` 13.6 s for
14.6 s (both still printed by `Repr`).
