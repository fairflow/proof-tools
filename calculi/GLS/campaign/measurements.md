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

and a fifth, added 2026-11-27 for "The two checks" below (it is in none
of Tables 1 and 2):

    lastChain n  ⇒ □p → □ⁿq → □ⁿp                               derivable; GLR nested n deep, the p of IdP last in the antecedent

## Table 1: the search over multisets (a record of 2026-11-25)

**A record, not a measurement of the program as it is.** It is of
`proofOrRef`, the search that returns a derivation of GLS as a term,
which no command runs since 2026-11-27, and of the certifiers' checks as
they then were (the definitions). The program as it is: Table 5.

Measured on 2026-11-25 at 09:53, before the search over sets existed. Loading the
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

## Table 2: the search over sets (a record of 2026-11-25)

**A record, as Table 1 is.** It is of the search over sets before it was
proved, and of the certifiers' checks as they then were. The program as
it is: Table 5.

Measured on 2026-11-25 at 13:20 to 13:27, **after** the repair of `dedup`
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

## `glsrun prove` on the corpus and on members of the families

Added 2026-11-26 22:28 GMT. The command of `reference/certify.md` §5, "A judgment
typed at a shell". Run by `python3 -I Corpus/prove_corpus.py
--elaborate`, from `calculi/GLS/` after `lake build GLS glsrun`: each
sequent is given as text three times (the source's notation, Lean
source, the signs of a keyboard: `glsrun corpus`, `glsrun families`),
the exit code is compared with the recorded status, and the printed
file is elaborated under `lake env lean -M 8000` with a deadline of
120 s that ends the whole process group.

| sequent | recorded | from the source's notation | from Lean source | from the signs of a keyboard | the answer | elaborated |
|---|---|---|---|---|---|---|
| `axK` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `ax4` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `axLob` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `idBoxImp` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `exFalsoBox` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `godel2` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `boxLobBody` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `lobRuleShape` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `notT` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notAtom` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notConsistency` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notBoxT` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notConverseK` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notConverse4` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notLobBody` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `notLinear` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `boxChain_3` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `boxChain_8` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `boxChain_32` | derivable | derivable | derivable | derivable | derivable, the proposition only | yes |
| `kChain_4` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `kChain_12` | derivable | derivable | derivable | derivable | derivable, the derivation as data | yes |
| `consis_3` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `consis_32` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `binTree_2` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |
| `binTree_4` | not derivable | not derivable | not derivable | not derivable | not derivable, a countermodel | yes |

25 sequents (the 16 of the corpus and 9 members of the families). By
verdict: derivable 13, not derivable 12, flag 0. By kind of answer: the
derivation as data 12, the proposition only 1 (`boxChain 32`), a
countermodel 12. Disagreeing with the recorded status, or answered
differently from two of the three texts: 0. Printed files elaborated:
25 of 25, each with named declarations and
`#axioms_within_file [propext, Quot.sound]` at its foot.

One file of each kind with its certificate altered, each refused by
Lean:

* altered `axLob` (derivable, the derivation as data; the last move IdP p made IdP p7): refused
* altered `boxChain_32` (derivable, the proposition only; the last move IdP p made IdP p7): refused
* altered `notT` (not derivable, a countermodel; p made true at the root): refused

**A first run returned a flag for `consis 32`** (and exit code 3 where 1
was recorded): the compiled check of the tree of worlds by
`Seq.refutedAt` did not end in the 10 s of the default deadline, where
the search over sets finds the tree in a millisecond and the kernel
checks it in 0.3 s. The program then checked a tree by a table
(`GLS/FastCheck.lean`); the figures above are after that change.
(2026-11-27: that table was a way round a fault of the check's
definition, and is gone; the certifier's own check is now the one the
program runs: "The two checks" below.) With
it: `□ⁿ⁺¹⊥ → □ⁿ⊥` answered in 0.6 s at `n = 32`, 0.05 s at 128, 0.4 s at
256 (one run each, the whole command).

A flag, seen by asking for it: `kChain 600` with `--deadline=1` prints
`-- flag:` and the sequent, and ends with exit code 3 after 1.0 s. A
text that is not a sequent (`p -> (q`): exit code 2, nothing on the
standard output.

Not checked: a printed file for a sequent larger than `boxChain 32`,
`consis 32`, `kChain 12`, `binTree 4` was not elaborated. The fallback
on the proved search was never taken by itself; its branch was run by
the option `--proved` on the same 25 sequents with `--deadline=5`: 23
agree with the recorded status, and 2 are flags at the deadline
(`boxChain 32`, `consis 32`: the proved search is cut off there, Table
1). One printed file of each verdict from it was elaborated (`axLob`,
`notConverseK`).

## The two checks: the definitions and the functions the certifiers run

Added 2026-11-27 09:43 GMT. Why: `decisions.md`, the entry of the same date. Run by
`python3 -I Corpus/measure_checks.py`, from `calculi/GLS/` after `lake
build GLS glsrun`. Each certificate is the one the search over sets
returns. *Compiled*: `glsrun check`, one run, the time of the one
function, with a deadline of 20 s; the list replay is not run where a
side would pass 40 000 000 formulas. *Kernel*: `lake env lean -M 8000`
on a file that states the check `= true` by `decide +kernel`, less the
time of the file with the imports and the certificate alone; a deadline
of 120 s that ends the process group.

* the definitions: `Seq.refutedAt` (a countermodel), `Cert.check` (a
  tree of moves, with the sequents written out);
* the certifiers' checks since this date: `noDerivable.check =
  Seq.refutedT` (truth by the marks, S26), `treeCert.check =
  Seq.countCheck` (the replay by counts, S27).

**Table 3: at 16, 24, 32, 48, 64.**

| member | certificate | definition, compiled | certifier's check, compiled | definition, kernel | certifier's check, kernel |
|---|---|---|---|---|---|
| `consis 16` | a tree of 17 worlds | 1.6 ms | 10 µs | 0.02 s | 0.02 s |
| `consis 24` | a tree of 25 worlds | 371.0 ms | 17 µs | 0.04 s | 0.06 s |
| `consis 32` | a tree of 33 worlds | no answer within 20 s | 26 µs | 0.08 s | 0.05 s |
| `consis 48` | a tree of 49 worlds | no answer within 20 s | 75 µs | 0.31 s | 0.11 s |
| `consis 64` | a tree of 65 worlds | no answer within 20 s | 117 µs | 0.77 s | 0.21 s |
| `boxChain 16` | a tree of 19 moves | 5.2 ms | 19 µs | 0.04 s | 0.02 s |
| `boxChain 24` | a tree of 27 moves | 1.54 s | 33 µs | 0.01 s | 0.02 s |
| `boxChain 32` | a tree of 35 moves | not run: a side of more than 40 000 000 formulas | 56 µs | 0.01 s | 0.06 s |
| `boxChain 48` | a tree of 51 moves | not run: a side of more than 40 000 000 formulas | 123 µs | 0.02 s | 0.03 s |
| `boxChain 64` | a tree of 67 moves | not run: a side of more than 40 000 000 formulas | 231 µs | 0.02 s | 0.07 s |
| `lastChain 16` | a tree of 19 moves | 5.7 ms | 27 µs | 10.27 s | 0.04 s |
| `lastChain 24` | a tree of 27 moves | 1.68 s | 56 µs | stack overflow (after 23 s) | 0.08 s |
| `lastChain 32` | a tree of 35 moves | not run: a side of more than 40 000 000 formulas | 106 µs | stack overflow (after 23 s) | 0.17 s |
| `lastChain 48` | a tree of 51 moves | not run: a side of more than 40 000 000 formulas | 263 µs | stack overflow (after 23 s) | 0.36 s |
| `lastChain 64` | a tree of 67 moves | not run: a side of more than 40 000 000 formulas | 500 µs | stack overflow (after 23 s) | 0.59 s |

**Table 4: at 128 and 256**, with `kChain` (`python3 -I
Corpus/measure_checks.py boxChain lastChain kChain consis 128 256`).

| member | certificate | definition, compiled | certifier's check, compiled | definition, kernel | certifier's check, kernel |
|---|---|---|---|---|---|
| `boxChain 128` | a tree of 131 moves | not run: a side of more than 40 000 000 formulas | 1.7 ms | 0.03 s | 0.07 s |
| `boxChain 256` | a tree of 259 moves | not run: a side of more than 40 000 000 formulas | 11.9 ms | 0.02 s | 0.10 s |
| `lastChain 128` | a tree of 131 moves | not run: a side of more than 40 000 000 formulas | 4.0 ms | stack overflow (after 23 s) | 2.50 s |
| `lastChain 256` | a tree of 259 moves | not run: a side of more than 40 000 000 formulas | 25.8 ms | stack overflow (after 23 s) | 11.00 s |
| `kChain 128` | a tree of 387 moves | 342 µs | 348 µs | 0.90 s | 1.42 s |
| `kChain 256` | a tree of 771 moves | 1.2 ms | 1.7 ms | 3.82 s | 5.67 s |
| `consis 128` | a tree of 129 worlds | no answer within 20 s | 497 µs | 7.51 s | 0.97 s |
| `consis 256` | a tree of 257 worlds | no answer within 20 s | 2.0 ms | over the cap on memory (after 91 s) | 4.56 s |

Read by family:

* **`consis n`** (`⇒ □ⁿ⁺¹⊥ → □ⁿ⊥`, refuted on a chain of `n + 1`
  worlds). The definition compiled doubles with each box (1.6 ms at 16,
  0.37 s at 24, no answer in 20 s from 32). The kernel on the definition
  does not double, since it keeps what it has reduced, but it grows
  fast: 0.8 s at 64, 7.5 s at 128, and over the cap on memory at 256.
  The check by the marks: 2 ms compiled at 256; in the kernel 0.2 s at
  64, 1.0 s at 128, 4.6 s at 256.
* **`boxChain n`** (`⇒ □p → □ⁿ⁺¹p`). The list replay compiled doubles
  (5 ms at 16, 1.5 s at 24, where the directing session measured 2.2 GB
  of memory). The kernel on it shows no growth: the `p` that IdP asks
  for is first in the antecedent, and the list is reduced no further.
  The replay by counts: 12 ms compiled at 256, and 0.1 s in the kernel.
* **`lastChain n`** (`⇒ □p → □ⁿq → □ⁿp`: `boxChain` with `□ⁿq` before
  `□p`, so that the `p` is last). The kernel on the list replay: 10 s
  at 16, and **a stack overflow from 24**. The replay by counts: 26 ms
  compiled at 256; in the kernel 0.6 s at 64, 2.5 s at 128, 11 s at
  256.
* **`kChain n`** (one GLR, then `n` uses of ImpL on a side of `n`
  formulas of one size). Neither replay grows fast. The replay by
  counts is the slower in the kernel: 1.4 s against 0.9 s at 128, 5.7 s
  against 3.8 s at 256.

So the kernel's speed on the list replay was a property of `boxChain`.
After the repair no check compiled is slower than the same check in the
kernel, on any member measured, and each certifier's check was checked
by the kernel at every size on every family, which neither definition
was.

**The first two forms of the replay by counts**, which are not kept
(`decisions.md`). The statement proved was the same for each.

| | compiled | kernel |
|---|---|---|
| first form (each formula looked up in the whole side) | 2.5 ms at `boxChain 64`, 40 ms at 128, 0.62 s at 256; 10 ms at `lastChain 64` | `boxChain`: 0.09, 0.21, 0.45, 1.53, 3.67 s at 16 to 64; over the cap on memory at 128 (after 47 s). `lastChain`: 0.25 to 15.1 s at 16 to 64. `kChain 128`: 11.7 s; 256: cut off at 120 s |
| second form (in order of size, GLR by one merge, every formula added with a search among those of its size) | 1.7 ms at `boxChain 128`, 2.4 ms at `kChain 256` | `boxChain 256`: 0.08 s. `lastChain 256`: 11.0 s. `kChain 128`: 4.2 s; 256: cut off at 120 s (at 192: 15 s and 5.4 GB for the whole file, of which the certificate alone 5.6 s and 2.4 GB) |
| the form kept (the formula of ImpR or ImpL added with no search) | Tables 3 and 4 | Tables 3 and 4 |

**The corpus script after the change** (`python3 -I
Corpus/prove_corpus.py --elaborate`): 25 sequents; by verdict derivable
13, not derivable 12, flag 0, as before; disagreeing with the recorded
status or among the three texts 0; printed files elaborated 25 of 25.
By kind of answer: the derivation as data 13, a countermodel 12
(`boxChain 32` was "the proposition only" under the cap of 4 096
formulas and is now a derivation as data). The third kind, asked for by
`--sets` on `axLob` and `boxChain 32`: both elaborated. Four files with
the certificate altered, each refused by Lean: `axLob`, `boxChain_32`
(data), `boxChain_32` with `--sets` (the proposition only), `notT` (a
countermodel). With `--proved --deadline=5` on the same 25: 23 agree
and 2 are flags at the deadline (`boxChain 32`, `consis 32`), as
before.

**Not repaired** at that hour, and why. (Later the same day the search
and the scripts, the second and third below, were repaired: "The search
and the scripts", after this section, which has the list as it now
stands.)

* **The derivation as data is still `2ⁿ` large.** `treeCert.verdict s
  c : Fam s` is a term of the family, whose sequents are those of GLS
  written out; the kernel checks that it exists without reducing it,
  and nothing here evaluates it. Compiled code that did would build the
  sequents. The certificate (the tree of moves) is its short form.
* **The search over multisets** (`proofOrRef`: the proved search, the
  commands `run`, `cert`, `facts`, `status`, and `prove --proved`)
  returns such a derivation, so it writes the sequents out: Table 1,
  cut off at `boxChain 28`. Not a check, and not changed. It now runs
  under the cap on the program's memory (8 GB): above it the program
  leaves with a flag. Seen by asking for it: `glsrun run boxChain 30`
  stopped after 8.2 s with "flag: more than 8000 MB of memory", having
  held 9.4 GB at most (the program asks the system five times a
  second).
* **A script** (`scriptCert`) is replayed with its goals written out,
  as the explorer shows them. No command runs that check compiled on a
  member of a family; the kernel runs it on the files that `glsrun
  cert` writes (Table 1, "the fact with its script"), where it has the
  list replay's behaviour.
* **The definitions themselves** (`Form.holds`, `Seq.refutedAt`,
  `Cert.check`) are as they were, and compiled code that calls them
  directly is as slow as before: the screens and tests do, on small
  cases (the largest: `boxChain 12`), and `glsrun check` does to
  measure them.
* **`setCert`**, the check over sets, is the library's replay on
  sequents with their repeated formulas removed: not changed, and
  slower in the kernel than `treeCert` (Table 2).

Tables 1 and 2 are of the checks as they were on 2026-11-25 (the
definitions); Tables 3 and 4 are of the checks as they are. Not
measured in Tables 3 and 4: memory, except where a cap was reached; `binTree`
with the new checks beyond the corpus script's `binTree 4`; anything
between 64 and 128 or beyond 256.

## The search and the scripts: Table 5, which takes the place of Tables 1 and 2

Added 2026-11-27 10:37 GMT. Why: `decisions.md`, the second entry of 2026-11-27. Every
column is of the program as it is: the search of `GLS/Decide.lean`
(S28), the certifiers' checks of S26, S27 and S29. Run by `python3 -I
Corpus/measure.py`, from `calculi/GLS/` after `lake build GLS glsrun`.
Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Loading the imports: 0.93 s, taken off the kernel's columns
(so a kernel's column includes reading the certificate as a term, which
Tables 3 and 4 took off). Deadlines: the search 20 s, each kernel check
60 s; Lean under `-M 4000`, a cap of 4 GB; a column stops at its first
flag. The compiled checks are one run of `glsrun check`.

| family | n | verdict | size of the certificate | the search, compiled | `treeCert` or `noDerivable`, compiled | `scriptCert`, compiled | the tree by `treeCert` or `noDerivable`, kernel | the tree of moves by `setCert`, kernel | the script by `scriptCert`, kernel | the kernel running the search (`decide +kernel`) |
|---|---|---|---|---|---|---|---|---|---|---|
| boxChain | 16 | pass | 19 | 0 ms | 15 µs | 20 µs | 0.01 s | 0.05 s | 0.03 s | 0.10 s |
| boxChain | 32 | pass | 35 | 0 ms | 48 µs | 56 µs | 0.06 s | 0.35 s | 0.07 s | 0.43 s |
| boxChain | 64 | pass | 67 | 2 ms | 239 µs | 279 µs | 0.15 s | 2.02 s | 0.17 s | 2.46 s |
| boxChain | 128 | pass | 131 | 25 ms | 1.8 ms | 1.9 ms | 0.46 s | flag: over the cap on memory, 4 GB | 0.71 s | flag: over the cap on memory, 4 GB |
| boxChain | 256 | pass | 259 | 340 ms | 10.7 ms | 11.2 ms | 1.61 s | not run | 2.84 s | not run |
| boxChain | 512 | pass | 515 | 4983 ms | 61.6 ms | 65.1 ms | 6.73 s | not run | 16.32 s | not run |
| lastChain | 16 | pass | 19 | 0 ms | 25 µs | 30 µs | 0.07 s | 0.15 s | 0.03 s | 0.17 s |
| lastChain | 32 | pass | 35 | 1 ms | 109 µs | 124 µs | 0.15 s | 0.87 s | 0.16 s | 1.06 s |
| lastChain | 64 | pass | 67 | 7 ms | 520 µs | 544 µs | 0.66 s | 6.57 s | 0.66 s | 7.16 s |
| lastChain | 128 | pass | 131 | 83 ms | 3.9 ms | 4.2 ms | 2.87 s | flag: over the cap on memory, 4 GB | 2.97 s | flag: over the cap on memory, 4 GB |
| lastChain | 256 | pass | 259 | 1263 ms | 25.9 ms | 26.6 ms | flag: over the cap on memory, 4 GB | not run | flag: over the cap on memory, 4 GB | not run |
| lastChain | 512 | pass | 515 | 19333 ms | no answer | no answer | not run | not run | not run | not run |
| kChain | 16 | pass | 51 | 0 ms | 14 µs | 14 µs | 0.16 s | 0.34 s | 0.14 s | 0.44 s |
| kChain | 32 | pass | 99 | 2 ms | 34 µs | 36 µs | 0.32 s | 1.96 s | 0.42 s | 2.64 s |
| kChain | 64 | pass | 195 | 10 ms | 103 µs | 103 µs | 1.02 s | flag (> 60 s) | 1.83 s | flag: over the cap on memory, 4 GB |
| kChain | 128 | pass | 387 | 84 ms | 376 µs | 392 µs | 4.65 s | not run | 8.59 s | not run |
| kChain | 256 | pass | 771 | 611 ms | 1.4 ms | 1.5 ms | flag (> 60 s) | not run | flag: over the cap on memory, 4 GB | not run |
| kChain | 512 | pass | 1539 | 4456 ms | 5.4 ms | 6.1 ms | not run | not run | not run | not run |
| consis | 16 | fail | 17 | 0 ms | 8 µs | not a derivation | 0.00 s | not a derivation | not a derivation | 0.07 s |
| consis | 32 | fail | 33 | 0 ms | 24 µs | not a derivation | 0.07 s | not a derivation | not a derivation | 0.49 s |
| consis | 64 | fail | 65 | 2 ms | 121 µs | not a derivation | 0.35 s | not a derivation | not a derivation | 2.31 s |
| consis | 128 | fail | 129 | 24 ms | 504 µs | not a derivation | 1.00 s | not a derivation | not a derivation | flag: over the cap on memory, 4 GB |
| consis | 256 | fail | 257 | 319 ms | 1.9 ms | not a derivation | 4.60 s | not a derivation | not a derivation | not run |
| consis | 512 | fail | 513 | 4640 ms | 8.1 ms | not a derivation | flag (> 60 s) | not a derivation | not a derivation | not run |
| binTree | 4 | fail | 31 | 0 ms | 111 µs | not a derivation | 0.05 s | not a derivation | not a derivation | 0.71 s |
| binTree | 6 | fail | 127 | 5 ms | 1.8 ms | not a derivation | 0.10 s | not a derivation | not a derivation | 8.99 s |
| binTree | 8 | fail | 511 | 43 ms | 29.0 ms | not a derivation | 0.15 s | not a derivation | not a derivation | flag (> 60 s) |
| binTree | 10 | fail | 2047 | 385 ms | 477.0 ms | not a derivation | 0.52 s | not a derivation | not a derivation | not run |
| binTree | 12 | fail | 8191 | 3541 ms | 7.71 s | not a derivation | 2.01 s | not a derivation | not a derivation | not run |

Read:

* **The search** answers every member up to 512 within its 20 s:
  `boxChain 512` in 5.0 s, `lastChain 512` in 19.3 s, `kChain 512` in
  4.5 s, `consis 512` in 4.6 s, `binTree 12` (8 191 worlds) in 3.5 s. It
  grows about as the fourth power of the number of nested boxes (0.34 s
  at `boxChain 256`, 5.0 s at 512): each step removes the repeated
  formulas of a list by comparing its formulas two by two, and a
  comparison of two formulas with `k` boxes takes `k` steps. The search
  that returned a derivation of GLS was cut off at 28 (Table 1).
* **The certifiers' checks compiled** are under 0.1 s on every member
  measured but `binTree 10` and `12` (below).
* **In the kernel**, under 4 GB: `treeCert` to `boxChain 512` (6.7 s),
  `lastChain 128` (2.9 s), `kChain 128` (4.7 s); `scriptCert` to
  `boxChain 512` (16.3 s), `lastChain 128`, `kChain 128` (8.6 s);
  `noDerivable` to `consis 256` (4.6 s) and `binTree 12` (2.0 s). Where
  a column has a next member, it passes the cap of 4 GB or the 60 s. Under
  8 GB and with the certificate's own time taken off, Table 4 has
  `treeCert` at `lastChain 256` in 11 s and at `kChain 256` in 5.7 s.
* **`setCert` in the kernel** stops first: `boxChain 64` (2.0 s),
  `lastChain 64` (6.6 s), `kChain 32` (2.0 s); beyond, the cap or the
  deadline. Its check removes repeated formulas at every step.
* **The kernel running the search itself** (`decide +kernel` on `Valid`,
  with no certificate): to 64 on `boxChain` (2.5 s), `lastChain`
  (7.2 s) and `consis` (2.3 s), to `kChain 32` and `binTree 6`; beyond,
  the cap or the deadline. On 2026-11-25 the kernel running the search
  over multisets was cut off at 16 (Table 1).

**A third check compiled slower than in the kernel, found by this
table and not repaired: `noDerivable` on `binTree`.** At `binTree 12`
the check by the marks takes 7.7 s compiled and 2.0 s in the kernel; at
10, 0.48 s and 0.52 s. The formula `Dₙ` has `Dₙ₋₁` in it twice, so it
is `2ⁿ` connectives written out and `n` different subformulas. The
marks are computed once for each occurrence of a subformula: `2ⁿ`
occurrences times `2ⁿ⁺¹` worlds, which is the size of the formula as
written times the size of the tree, the bound one expects of the
algorithm for a formula given as text. The kernel keeps the marks of a
subformula it has seen, so it pays `n` times the worlds. By the rule of
`reference/certify.md` §5 ("a compiled check slower than the kernel's is
a fault of the checker") this is one: the repair is a table over the
different subformulas, with its equality to S25's function. It does not
arise for a sequent typed at a shell, whose formula is its text.

**The commands, timed** (one run each, the whole process, on this
machine; memory is the most the process held):

| command | time | memory |
|---|---|---|
| `glsrun run boxChain 32` | 0.02 s | 37 MB |
| `glsrun run consis 32` | 0.02 s | 37 MB |
| `glsrun cert boxChain 32` (three files written) | 0.02 s | 38 MB |
| `glsrun cert consis 32` | 0.02 s | 37 MB |
| `glsrun status` (the 16 of the corpus; 16 agree) | 0.02 s | 37 MB |
| `glsrun facts` (the same file as before, to the byte) | 0.02 s | 37 MB |
| `glsrun run boxChain 256` | 0.43 s | 38 MB |
| `glsrun run lastChain 256` | 1.34 s | 40 MB |
| `glsrun run kChain 256` | 0.60 s | 42 MB |
| `glsrun run consis 256` | 0.34 s | 39 MB |

Before this change `run`, `cert`, `status` and `facts` ran the search
over multisets: `glsrun run boxChain 30` stopped at the cap of 8 GB
after 8 s.

**The corpus script after the change** (`python3 -I
Corpus/prove_corpus.py --elaborate`, Lean under `-M 4000`): 25
sequents; by verdict derivable 13, not derivable 12, flag 0, as before;
disagreeing 0; printed files elaborated 25 of 25; by kind, the
derivation as data 13, a countermodel 12; `--sets` on `axLob` and
`boxChain 32` elaborated; four altered files refused. `glsrun facts`
writes `GLS/Corpus/Facts.lean` unchanged, so the search finds the trees
it found before.

### What remains exponential, and why

* **A derivation of GLS as data.** `Fam s`, `Der S s`, and so
  `proofOrRef` (S4), `treeCert.verdict`, `Der.ofCert`, `famOfDer`: the
  term holds every sequent of the derivation, and the premise of GLR
  doubles the boxed part of an antecedent. It is the calculus on
  multisets as the source states it. Nothing in `glsrun` builds one;
  the kernel checks that one exists without reducing it. `proofOrRef`
  is kept as the theorem (completeness as data) and run by the tutorial
  and the tests on small sequents; its record is Table 1, cut off at 28
  nested boxes.
* **The explorer on such a derivation**: `#walk`, `apply_script`,
  `glsmove` show and hold each goal written out. Tried under a cap of
  4 GB on `boxChain n`: at 10 the walk to the last sequent (2 049
  formulas, a line of 40 000 characters) takes 1.6 s; at 14 the
  derivation takes 23 s and 3 GB to define; at 16 Lean stops at the cap
  (`users-guide.md`).
* **The definitions** `Form.holds`, `Seq.refutedAt`, `Cert.check` on
  lists, and the library's `derives`: each is the statement that a
  check of S25 to S29 is proved equal to. Compiled code calls them only
  in screens and tests on small cases (the largest: `boxChain 12`) and
  in `glsrun check --definitions`, which measures them under its
  deadline and its cap of 40 000 000 formulas.
* **Not exponential, and not repaired**: the check by the marks on a
  formula with repeated subformulas (above); `setCert` in the kernel;
  the fourth power in the search.

Not measured: members between the last that passed and the first
flagged in a column; any column under more than 4 GB; `lastChain 512`
compiled checks (the command that times them runs the search again, and
the two passed its 20 s).
