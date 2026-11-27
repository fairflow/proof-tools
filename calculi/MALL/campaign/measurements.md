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

## Refutations by a saturated set

Added 2026-11-26, after the closing page. `mallrun refute <family> <n>`;
compiled times for the producer and the check; the last column is the
kernel checking the fact, less the imports (0.9 s), under a deadline of
60 s.

| family | n | formulas | sequents in the set | phases of the structure | producer | check, compiled | the kernel |
|---|---|---|---|---|---|---|---|
| chainBad | 2 | 4 | 22 | 45 | 0 ms | 0 ms | not run |
| chainBad | 3 | 5 | 86 | 135 | 0 ms | 2 ms | 3.39 s |
| chainBad | 4 | 6 | 305 | 405 | 2 ms | 65 ms | flag (> 60 s) |
| chainBad | 5 | 7 | 1 015 | 1 215 | 18 ms | 1 566 ms | not run |
| chainBad | 6 | 8 | flag (> 40 s, the three steps together) | | | | |
| fanBad | 4 | 6 | 33 | 81 | 0 ms | 0 ms | not run |
| fanBad | 6 | 8 | 129 | 321 | 0 ms | 1 ms | 1.57 s |
| fanBad | 8 | 10 | 513 | 1 281 | 1 ms | 21 ms | not run |
| fanBad | 10 | 12 | 2 049 | 5 121 | 4 ms | 396 ms | not run |

For the corpus: all 15 entries with no derivation get a set that the
check accepts; the largest is `halfDistribConv`, 17 sequents, 35 phases,
the one entry for which no cyclic structure was found.

The set grows by a factor of about 3.3 for each ⊗ of `chainBad`, and
doubles for each two of `fanBad`: every part of the context is a premise
of some division. The check tries each division of each member against
the whole set, so it is quadratic in the set. On these two families the
cyclic structures are the certificate to use (130 formulas in about a
second, above). (The check of this table is `refutedBy` on lists. In
numbers, since 2026-11-27: `chainBad 5`, 1 015 sequents, 4.5 s in the
kernel; `fanBad 10`, 2 049 sequents, 5.0 s; below.)

## `mallrun prove`

Added 2026-11-26. `Corpus/prove_corpus.py --elaborate`: each of the 38
entries of the corpus given to the command three times (the source's
notation, Lean source, the signs of a keyboard), and the printed file
elaborated under `lake env lean -M 8000` with a deadline of 60 s that
ends the process group.

| | |
|---|---|
| by verdict | derivable 23, not derivable 15, flag 0 |
| by certificate | a tree of moves 23, a cyclic phase structure 14, a saturated set 1 |
| disagreeing with the recorded status, or the three texts answered differently | 0 |
| printed files not elaborated | 0 of 38 |

Beyond the corpus (the command under `--deadline=5` or 60; the file
under the same cap, deadline 150 s):

| the sequent | the answer | found in | the file elaborated |
|---|---|---|---|
| `chain 64`, 66 formulas | derivable, a tree | 0.03 s | 3.7 s |
| `fan 32` | derivable, a tree | 0.03 s | 1.9 s |
| `withTree 8` | derivable, a tree | 0.04 s | 1.5 s |
| `chainBad 64` | not derivable, a cyclic structure | 0.04 s | 1.4 s |
| `chainBad 10` and the converse of half-distributivity on other letters | not derivable, a cyclic structure | 0.03 s | 1.1 s |
| `chain 1` and the same, 5 formulas | not derivable, a set of 238 | 0.06 s | **no**: stopped at 8 GB after 36 s |
| `chain 2` and the same, 6 formulas | not derivable, a set of 947 | 0.91 s | not run |
| `chain 3` and the same, 7 formulas | not derivable, a set of 3 347 | 24.8 s; **flag** at 5 s and at the default 10 s | not run |
| `chain 10` and the same | flag at 5 s | | |

**The size of saturated set the kernel checks**, measured with two
families that grow and have no small cyclic countermodel: the converse
of half-distributivity with `n` formulas `⊥` beside it (`bots`), and
with `⅋ ⊥` added `n` times to its second formula (`plusbot`). Each
printed file under `lake env lean -M 8000`, deadline 180 s, the process
group ended at the deadline; the run stops a family at its second
failure.

| family | n | sequents in the set | found in | the printed file |
|---|---|---|---|---|
| bots | 0 | 17 | 0.03 s | checked, 1.2 s |
| bots | 1 | 34 | 0.03 s | checked, 1.3 s |
| bots | 2 | 51 | 0.03 s | checked, 2.0 s |
| bots | 3 | 68 | 0.03 s | checked, 3.6 s |
| bots | 4 | 85 | 0.03 s | checked, 7.0 s |
| bots | 5 | 102 | 0.04 s | checked, 16.7 s |
| bots | 6 | 119 | 0.06 s | **stopped at the 8 GB cap**, after 19.6 s |
| bots | 7 | 136 | 0.11 s | stopped at the cap, after 86.7 s |
| plusbot | 1 | 39 | 0.04 s | checked, 1.5 s |
| plusbot | 2 | 73 | 0.03 s | checked, 3.2 s |
| plusbot | 3 | 124 | 0.04 s | checked, 9.2 s |
| plusbot | 4 | 192 | 0.06 s | **stopped at the cap**, after 20.3 s |
| plusbot | 5 | 277 | 0.11 s | not checked, on two runs: refused after 104.8 s with a message of `decide` that the log cut short ("Tactic `decide` failed. The elaborator is able to red…"); then stopped at the cap after 19.7 s |

The largest set checked on both families is 102. The size is not the
whole of it: 124 was checked on one family and 119 was not on the other.
`mallrun prove` takes 102 as the bound (`kernelSeen`, `Main.lean`): above
it the first line reads "not derivable, by the compiled check only (a
set of N sequents; the kernel has checked sets of up to 102)", the exit
code staying 1, and the file says the same in a comment. Between 103 and
124 the line is therefore qualified for some files that would check.
What grows is memory, not time: the check is cut off by the cap well
before the deadline. Why the kernel's evaluation of `refutedBy` needs so
much memory was not looked into. (It was on 2026-11-27: "Why the kernel
could not check a set, and the check in numbers", below. The sets are
now written in numbers, and the bound is 11 110 sequents.)

So the answers the kernel checks are: every derivation tried; every
cyclic structure tried; a saturated set of up to 102 sequents (since
2026-11-27: every set tried, up to 11 110). A sequent with a derivable part
that has many ⊗ and a part with no small cyclic countermodel is where
the command prints a file that is not checked, or flags.

## Why the kernel could not check a set, and the check in numbers

Added 2026-11-27, by a task of the directing session. Every Lean run
below is one process group under a deadline, with
`lake env lean -M 4000` (megabytes), one at a time; "over the imports"
is less a file with the imports alone (0.9 to 1.1 s, about 1 210 MB).
The cap is not sharp: a run stopped at it has been seen to reach
5.8 GB first.

### The cause

**The parts of the printed file, apart** (`bots 3`, 68 sequents):

| the file has | time over the imports | memory over the imports |
|---|---|---|
| the set as a definition, nothing checked | 0.0 s | 18 MB |
| and `memP refutation sequent = true` | 0.2 s | 26 MB |
| and `saturated refutation = true` | 1.9 s | 691 MB |
| the whole check, `refutedBy` | 1.9 s | 694 MB |

So not the literal, and not membership of the sequent: saturation. At
`bots 5` (102 sequents) saturation alone was stopped at the cap after
22 s, the literal alone costing 23 MB.

**Not a recursion the kernel runs badly.** `#print` of `permB`,
`List.count`, `List.countP.go`, `memP`, `saturated`, `splits`, `picks`
and the derived `instDecidableEqForm.decEq`: each is by `brecOn`
(structural), none by well-founded recursion.

**What the check does**, counted by a copy of it that counts (run
compiled; the same order and the same early exits):

| family | n | sequents | formulas in a sequent, at most | questions of membership | sequents compared | formulas compared | divisions of a context |
|---|---|---|---|---|---|---|---|
| `bots` | 1 | 34 | 4 | 87 | 1 519 | 13 440 | 42 |
| `bots` | 3 | 68 | 6 | 386 | 13 396 | 166 326 | 210 |
| `bots` | 5 | 102 | 8 | 1 329 | 78 216 | 1 220 266 | 882 |
| `bots` | 7 | 136 | 10 | 4 644 | 366 467 | 6 918 489 | 3 570 |
| `parBots` | 1 | 39 | 4 | 96 | 2 025 | 16 929 | 42 |
| `parBots` | 3 | 124 | 6 | 624 | 42 751 | 477 588 | 322 |
| `parBots` | 5 | 277 | 8 | 2 620 | 395 619 | 5 470 328 | 1 610 |

The set grows by 17 sequents for each ⊥ added, and the comparisons of
formulas by 12, 7.3 and 5.7 times for each two. At 68 sequents the
kernel spent 691 MB on 166 326 comparisons: 4 KB and 11 µs each, on
average, most of them of pairs it had met before.

**What one comparison costs the kernel** (20 000 of them by
`List.count` over a list of 20 000 different formulas; less the cost of
making that list, 1.0 s and 414 MB):

| what is compared | each, time | each, memory |
|---|---|---|
| two letters, by the derived `DecidableEq` | 180 µs | 63 KB |
| the same with letters numbered in the thousands of millions | 190 µs | 65 KB |
| a letter and a negated letter (different constructors), derived | 55 µs | 17 KB |
| two letters, by a Boolean equality written by hand | 55 µs | 20 KB |
| two formulas of 7 connectives that differ in the last letter, by hand | 115 µs | 38 KB |
| the same, derived | stack overflow at 20 000 | past the cap |
| two numbers (`List.count` on `Nat`) | no more than making the list | |

So not letters with large numbers; and the derived equality is three
times one written by hand, but either is tens of kilobytes for each
pair not met before.

**The smallest inputs that show the growth**: three families that grow
in one thing each (`saturated D = true`, over the imports):

| the set | size | time | memory |
|---|---|---|---|
| `⊢ p⊥ ⊗ q⊥, ⊥ᵏ` with fewer ⊥, and `⊢ p⊥, ⊥ʲ`: 2k + 2 sequents | k = 6 | 0.3 s | 97 MB |
| | k = 8 | 1.1 s | 380 MB |
| | k = 10 | 5.3 s | 1 640 MB |
| | k = 12 | stopped at the cap, 36 s | |
| `⊢ aᵢ⊥ ⊕ bᵢ⊥`, `⊢ aᵢ⊥`, `⊢ bᵢ⊥`: 3N sequents of one formula | N = 50 | 2.7 s | 782 MB |
| | N = 100 | stopped at the cap, 23 s | |
| `⊢ ⊥, Γ` and `⊢ Γ`, `Γ` of m different negated letters: 2 sequents | m = 50 | 0.5 s | 202 MB |
| | m = 100 | 2.3 s | 792 MB |
| | m = 200 | stopped at the cap, 19 s | |

Three causes, each enough alone:

1. **The divisions of a context are listed with repetition**: `splits`
   gives `2ᵏ` pairs for `k` formulas, and beside `k` copies of one
   formula only `k + 1` are different. Memory doubles with each ⊥
   (four times for each two, in the first family): 26 sequents of at
   most 13 formulas are past 4 GB.
2. **Membership is a scan of the set**, once for each premise: the
   square of the number of sequents (the second family, which has no
   ⊗).
3. **Two sequents are compared by counting every formula of both in
   both** (`permB`): the square of the number of formulas in a sequent
   (the third family), each comparison by the derived equality.

And the kernel keeps what it has reduced until the theorem ends, so its
memory follows the number of steps; that is why the check ended at the
cap and not at the deadline.

**The compiled check has the first cause too.** It was "milliseconds" at
the sizes tried on 2026-11-26. One size beyond: 53 ms at 136 sequents,
277 ms at 170, 1.4 s at 204 (`bots 11`), five times for each two ⊥.

### The check in numbers

`MALL/Coded.lean` (S27): the formulas of the set listed once in a table;
a sequent one number, its digit in base `B` at a formula's place the
multiplicity; the set a search tree of those numbers; the divisions of a
context enumerated on the digits, each once. The kernel then compares
no two formulas of the set, and an addition or a comparison of numerals
costs it one step whatever their size.

**The base must not be a power of two.** Found by measuring one size
beyond (the file with the one theorem `codeRefutes … = true`, whole
run):

| family | n | sequents | base | the kernel | the compiled check |
|---|---|---|---|---|---|
| `bots` | 29 | 510 | 32 | 2.1 s | 1.4 ms |
| `bots` | 30 | 527 | 64 | 11.5 s | 5.2 ms |
| `bots` | 30 | 527 | 33 | 2.2 s | 1.6 ms |
| `bots` | 40 | 697 | 64 | 21.9 s | 9.0 ms |
| `bots` | 40 | 697 | 43 | 2.8 s | 6.8 ms |
| `bots` | 58 | 1 003 | 64 | 55.2 s | 17.0 ms |
| `bots` | 58 | 1 003 | 61 | 4.6 s | 16.8 ms |

With base 64 the numbers pass 2⁶⁴ (twelve digits of six bits). The
place of ⊥ is the highest, so the members that differ in the number of
⊥ differ only above bit 64. With an odd base a digit at any place
changes the low bits, and the time is back on its line; memory is the
same in both (2 090 MB at 1 003). The inference, which was not checked
in the kernel's source: its tables key a numeral by its low 64 bits, and
numerals that agree there share a bucket. `Encode.encode` takes the
least odd base that exceeds every multiplicity by 3. (The compiled
check's step from 1.4 to 5.2 ms is another thing: above 63 bits a
number is no longer held in a machine word.)

### Before and after

`Corpus/measure_sets.py`: `mallrun refute <family> <n>` for the producer
and the two compiled checks, then Lean on the fact written with the set
as lists (`noDerivableBySet.verdict`, before) and with the set in
numbers (`noDerivableByCode.verdict`, after, one theorem), each under
`-M 4000` with a deadline of 200 s for lists and 300 s for numbers. The
kernel's columns are time and memory over the imports (1.0 s,
1 214 MB). "Found" is the memoised search, which since this change
divides a context without repetition.

| family | n | sequents | found | as lists, compiled | in numbers, compiled | as lists, the kernel | in numbers, the kernel |
|---|---|---|---|---|---|---|---|
| `bots` | 1 | 34 | 0.1 ms | 0.2 ms | 0.05 ms | checked, 0.3 s, 102 MB | checked, 0.0 s, 25 MB |
| `bots` | 3 | 68 | 0.3 ms | 1.5 ms | 0.10 ms | checked, 2.4 s, 688 MB | checked, 0.1 s, 39 MB |
| `bots` | 4 | 85 | 0.4 ms | 3.8 ms | 0.12 ms | checked, 5.6 s, 1 536 MB | checked, 0.1 s, 47 MB |
| `bots` | 5 | 102 | 0.6 ms | 9.8 ms | 0.16 ms | **stopped at the cap**, 23.7 s | checked, 0.2 s, 56 MB |
| `bots` | 7 | 136 | 1.3 ms | 52.6 ms | 0.23 ms | stopped at the cap, 82.1 s | checked, 0.2 s, 73 MB |
| `bots` | 9 | 170 | 2.2 ms | 261 ms | 0.30 ms | cut off at 200 s | checked, 0.3 s, 91 MB |
| `bots` | 11 | 204 | 4.0 ms | 1 335 ms | 0.37 ms | cut off at 200 s | checked, 0.2 s, 111 MB |
| `bots` | 20 | 357 | 18 ms | not run | 0.91 ms | not run | checked, 0.7 s, 213 MB |
| `bots` | 40 | 697 | 165 ms | | 6.9 ms | | checked, 2.0 s, 513 MB |
| `bots` | 58 | 1 003 | 595 ms | | 17.7 ms | | checked, 3.6 s, 882 MB |
| `bots` | 80 | 1 377 | 1.9 s | | 31 ms | | checked, 6.5 s, 1 457 MB |
| `bots` | 100 | 1 717 | 3.8 s | | 47 ms | | checked, 8.3 s, 2 075 MB |
| `bots` | 120 | 2 057 | 8.6 s | | 71 ms | | **stopped at the cap**, 28.5 s |
| `bots` | 160 | 2 737 | 25.3 s | | 119 ms | | stopped at the cap, 40.5 s |
| `parBots` | 1 | 39 | 0.1 ms | 0.2 ms | 0.06 ms | checked, 0.3 s, 127 MB | checked, 0.1 s, 28 MB |
| `parBots` | 3 | 124 | 0.4 ms | 4.0 ms | 0.17 ms | checked, 6.7 s, 2 011 MB | checked, 0.2 s, 73 MB |
| `parBots` | 5 | 277 | 1.4 ms | 43 ms | 0.49 ms | **stopped at the cap**, 70.8 s | checked, 0.5 s, 172 MB |
| `parBots` | 7 | 498 | 3.7 ms | 335 ms | 1.9 ms | cut off at 200 s | checked, 1.2 s, 340 MB |
| `parBots` | 10 | 957 | 12 ms | not run | 8.3 ms | not run | checked, 2.8 s, 758 MB |
| `parBots` | 13 | 1 569 | 29 ms | | 18.6 ms | | checked, 5.4 s, 1 414 MB |
| `parBots` | 16 | 2 334 | 59 ms | | 34.6 ms | | checked, 8.8 s, 2 311 MB |
| `parBots` | 20 | 3 592 | 135 ms | | 70 ms | | **stopped at the cap**, 30.3 s |
| `chainBad` | 3 | 86 | 0.4 ms | 2.0 ms | 0.15 ms | checked, 3.7 s, 1 029 MB | checked, 0.2 s, 53 MB |
| `chainBad` | 4 | 305 | 3.0 ms | 62 ms | 0.92 ms | not run | checked, 0.7 s, 243 MB |
| `chainBad` | 5 | 1 015 | 22 ms | 1 543 ms | 5.4 ms | not run | checked, 4.5 s, 1 203 MB |
| `fanBad` | 6 | 129 | 0.2 ms | 1.2 ms | 0.16 ms | checked, 1.5 s, 514 MB | checked, 0.1 s, 73 MB |
| `fanBad` | 8 | 513 | 0.9 ms | 20.6 ms | 0.76 ms | not run | checked, 0.9 s, 305 MB |
| `fanBad` | 10 | 2 049 | 4.4 ms | 403 ms | 8.6 ms | not run | checked, 5.0 s, 1 408 MB |

`bots n` is the converse of half-distributivity beside `n` copies of ⊥;
`parBots n` the same with the copies joined to its second formula by ⅋
(called `plusbot` on 2026-11-26, which misnamed the connective); both
are in `MALL/Corpus/Basic.lean` now. `chainBad` and `fanBad` are the
families of "Refutations by a saturated set" above: the formulas beside
a ⊗ are all different there, so nothing is saved on the divisions, and
the gain is the other two causes.

Before, under 4 GB, the kernel checked 85 sequents on `bots` and 124 on
`parBots` (under 8 GB, 2026-11-26: 102 and 124). After, as one theorem:
1 717 on `bots`, 2 334 on `parBots`, 2 049 on `fanBad`, and it is
stopped at the cap at 2 057 on `bots` and at 3 592 on `parBots`. The
kernel takes 3.6 s for 1 003 sequents; the compiled check, 17.7 ms.

### The check stated in parts

The kernel keeps what it has reduced until a theorem ends. So above 600
sequents `mallrun prove` states the check as several theorems: one for
the sequent, one for each part of the tree (at most 150 numbers), one
for each number above the parts; `codeRefutes_of_parts` and
`Tree.all_node` put them together, and `set_option Elab.async false`
has them elaborated one after another. The printed file, whole run
(imports 0.9 s and 1 214 MB included), under `-M 4000`, deadline 400 s:

| the sequent | sequents in the set | found | parts | the printed file |
|---|---|---|---|---|
| `bots 58` | 1 003 | 0.6 s | 8 | checked, 3.6 s, peak 1 433 MB (as one theorem: 4.2 s, 2 113 MB) |
| `bots 120` | 2 057 | 7.8 s | 16 | checked, 11.2 s, peak 1 633 MB (one theorem: stopped at the cap) |
| `bots 160` | 2 737 | 23.2 s | 32 | checked, 19.8 s, peak 1 629 MB |
| `parBots 20` | 3 592 | 0.3 s | 32 | checked, 14.7 s, peak 1 509 MB (one theorem: stopped at the cap) |
| `parBots 30` | 7 927 | 1.3 s | 64 | checked, 46.7 s, peak 1 776 MB |
| `chain 1` and the converse of half-distributivity on other letters, 5 formulas | 238 | 0.02 s | one theorem | checked, 1.3 s, peak 1 366 MB (2026-11-26, as lists: stopped at 8 GB after 36 s) |
| `chain 2` and the same, 6 formulas | 947 | 0.04 s | one theorem (measured before the parts) | checked, 3.8 s, peak 2 040 MB |
| `chain 3` and the same, 7 formulas | 3 347 | 0.13 s (2026-11-26: 24.8 s, most of it the compiled check of the lists) | 32 | checked, 16.2 s, peak 1 604 MB (one theorem: stopped at the cap after 12 s) |
| `chain 4` and the same, 8 formulas | 11 110 | 0.8 s | 128 | checked, 101.6 s, peak 2 150 MB |

Nothing tried in parts failed. The largest set checked is 11 110
sequents, and `kernelSeen` (`Main.lean`) is that number: above it the
first line of `mallrun prove` is still qualified. What bounds the check
now is the kernel's time: about 9 ms a sequent at that size, where the
compiled check takes some tens of microseconds a sequent (17.7 ms for
1 003, in the table above).

**A fact through the certifier after a named check** cost the
elaborator part of the check again: at 697 sequents, each
`noDerivableByCode.verdict sequent refutation refuted` added 0.4 s and
180 MB to a check of 2.1 s. The printed file states its facts by the
soundness lemmas applied to the named check (`not_derivable_of_code
refuted`), which adds nothing.

**The corpus** by `mallrun prove` after the change
(`Corpus/prove_corpus.py --elaborate`): derivable 23, not derivable 15, flag 0; a tree of moves 23, a cyclic phase
structure 14, a saturated set 1; no disagreement; every one of the 38
printed files elaborated. `mallrun screen`: 45 998 altered certificates,
6 278 accepted, none of them decoding to a set that `refutedBy` refuses.


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
* **Since the closing page**: a saturated set of sequents (S20, S21) is
  a certificate for every sequent with no derivation, so nothing is left
  without an answer in principle. `halfDistribConv` is settled by one (17
  sequents). What is out of practical reach is unchanged in kind: a
  sequent with no derivation, many formulas with ⊗, and no small cyclic
  structure; there the set is too large for the kernel within a minute
  from about 300 sequents.
* **Since 2026-11-27**: the set is written in numbers (S27) and its
  check stated in parts. The kernel checks every set tried, up to 11 110
  sequents in 102 s (a sequent of eight formulas: `chain 4` and the
  converse of half-distributivity on other letters). What is out of
  practical reach is now a set of some tens of thousands of sequents:
  the kernel's time, about 9 ms a sequent at that size.
* The finite model property (S17) says a finite structure exists for
  every sequent with no derivation. It does not say a cyclic group, and
  the structure of its proof is too large to write down. So "a better
  producer of structures" is the open end of this stage.
