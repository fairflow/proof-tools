# DILL: the saturated sets, measured

Written 2026-11-26 15:48 GMT by agent H of stage 3 (brief
`campaign/brief-3-1.md`, section H), from runs of the same day, 15:38 to
15:47. Machine: Apple M4 Pro (14 cores, 48 GB), macOS 15.8.3, arm64; Lean
v4.31.0. The times are single runs, on a machine where other sessions
were building: read them for their order of magnitude. Every figure
below is pasted from the output of `Corpus/measure_sat.py`
(`Corpus/out/sat-report.md`, `Corpus/out/sat-decide-report.md`), or from
the run named beside it.

## What runs

| | what | where | trusted? |
|---|---|---|---|
| the check | `refutedBy D j`: `j` is a member of `D` (up to a permutation of the linear zone and the members of the unrestricted zone), and `D` is saturated | `DILL/Saturated.lean` | yes, through `not_cf_of_refutedBy` (S16) |
| against a derivation without cut | `noCFBySet : Certifier Seq (List Seq) (fun j => Nonempty (CF j) → False)` | `DILL/SatRun.lean` | yes; no semantics, no cut |
| against a derivation with the cuts | `noDerivableBySet : Certifier Seq (List Seq) (fun j => Derivable j → False)` | `DILL/SatRun.lean` | yes, through `cutElimination` (`DILL/Cut.lean`) |
| the producer | `refuteSet j : Option (List Seq)`; `Refute.outcome j` says why there is no set | `DILL/Refute.lean` | no: `partial`, not proved; its set is checked before it is handed on |
| the driver | one member of the family, the times of the producer's parts, the fact file | `Corpus/SatMain.lean`, compiled by `Corpus/measure_sat.py` into `Corpus/out/` | no |

The lints of `lean-certify`: R3 and R2 pass on `noCFBySet` and
`noDerivableBySet`; R1 reports nothing on `refuteSet`; R4 passes on the
seven facts of `DILL/SatTest.lean` it is run on; R3 passes on the fact
`pfenning60`.

## The facts and the negative tests (`DILL/SatTest.lean`)

Thirteen facts, each `noCFBySet.verdict j D` or
`noDerivableBySet.verdict j D` with `D` the producer's set, pasted: the
plan's known non-theorems with an empty unrestricted zone and no `!` in
a linear zone (`· ; · ⟹ 0`; `· ; p ⟹ 1`; `· ; p, q ⟹ p`;
`· ; p ⟹ p ⊗ p`; Pfenning's `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)`, a
set of 8; `· ; p ⟹ !p`; `· ; p ⊕ q ⟹ p`; `· ; p ⟹ p & q`), three of
them again against `Derivable`, and two with `!` on the left that have a
set all the same (`· ; !p ⊸ q ⟹ p ⊸ q`, a set of 5, which the plan
expected to be a flag; `· ; !p ⊕ q ⟹ r`).

Sixteen negative tests (R9), each `refutedBy … = false` by
`decide +kernel`: a member missing; a member that is an instance of
init, of 1R, of ⊤R, of 0L; a member with a derivation (twice); the
sequent not a member; the sequent with another unrestricted zone; one
division of ⊗R not covered (twice); one division of ⊸L not covered; a
formula in the unrestricted zone (the premise of copy missing, then the
next one missing); `!` in the linear zone (twice). Two positive ones
beside them (the linear zone in another order; a ⊗R with four divisions
covered).

The producer against the proved search of the fragment without `!`
(`Dec.searchCF`, `DILL/Decide.lean`), by `#guard`: on the 3615 sequents
`· ; Δ ⟹ C` with `Δ` of at most two and `C` one of fifteen small
formulas, the producer gives a set that the check accepts exactly where
the search finds no derivation (2557 of them), and never a set that the
check rejects. The file builds in 5.2 s, these guards included.

## The family: the chain with its last link missing

`· ; a₀, a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ⟹ aₙ`, with `n` formulas in the linear
zone. No derivation: `aₙ` occurs nowhere on the left. "choice" is the
producer's way to choose a premise where two would do (`first`, or the
one with the `shortest` linear zone).

Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Date: 2026-11-26 15:38 GMT.  The driver: compiled (leanc -O3).  Loading the imports of a fact: 1.04 s, taken off the last column.
Deadlines: the producer 60 s, the fact 120 s.  `flag`: cut off at the deadline, or not elaborated; the column stops there.

| n | formulas in the sequent | choice | settled by the search (of them "no") | the set: sequents, longest linear zone | search | cut to the set | compiled check | the fact: elaborated, and checked by the kernel |
|---|---|---|---|---|---|---|---|---|
| 1 | 2 | first | 1 (1) | 1, 1 | 0 ms | 0 ms | 0 ms | 0.04 s |
| 2 | 3 | first | 4 (3) | 3, 2 | 0 ms | 0 ms | 0 ms | 0.02 s |
| 3 | 4 | first | 12 (9) | 9, 3 | 0 ms | 0 ms | 0 ms | 0.00 s |
| 4 | 5 | first | 33 (27) | 27, 4 | 0 ms | 0 ms | 0 ms | 0.15 s |
| 5 | 6 | first | 86 (76) | 76, 5 | 0 ms | 1 ms | 0 ms | 1.77 s |
| 6 | 7 | first | 215 (200) | 200, 6 | 1 ms | 0 ms | 4 ms | 18.66 s |
| 7 | 8 | first | 520 (499) | 499, 7 | 3 ms | 4 ms | 38 ms | flag (> 120 s) |
| 8 | 9 | first | 1225 (1197) | 1197, 8 | 18 ms | 15 ms | 402 ms | not run |
| 9 | 10 | first | 2826 (2790) | 2790, 9 | 81 ms | 66 ms | 3664 ms | not run |
| 10 | 11 | first | 6411 (6366) | 6366, 10 | 354 ms | 270 ms | 31846 ms | not run |
| 11 | 12 | first | flag (> 60 s) | | | | | |
| 1 | 2 | shortest | 1 (1) | 1, 1 | 0 ms | 0 ms | 0 ms | 0.01 s |
| 2 | 3 | shortest | 4 (3) | 3, 2 | 0 ms | 0 ms | 0 ms | 0.00 s |
| 3 | 4 | shortest | 12 (9) | 9, 3 | 0 ms | 0 ms | 1 ms | 0.00 s |
| 4 | 5 | shortest | 33 (27) | 27, 4 | 0 ms | 0 ms | 0 ms | 0.11 s |
| 5 | 6 | shortest | 86 (76) | 76, 5 | 0 ms | 0 ms | 0 ms | 1.68 s |
| 6 | 7 | shortest | 215 (200) | 200, 6 | 1 ms | 1 ms | 4 ms | 18.00 s |
| 7 | 8 | shortest | 520 (499) | 499, 7 | 4 ms | 4 ms | 39 ms | flag (> 120 s) |
| 8 | 9 | shortest | 1225 (1197) | 1197, 8 | 18 ms | 15 ms | 403 ms | not run |
| 9 | 10 | shortest | 2826 (2790) | 2790, 9 | 82 ms | 64 ms | 3735 ms | not run |
| 10 | 11 | shortest | 6411 (6366) | 6366, 10 | 372 ms | 277 ms | 32912 ms | not run |
| 11 | 12 | shortest | flag (> 60 s) | | | | | |

## The comparison: the kernel running the proved search

The same family, stated as `¬ Nonempty (CF j)` and closed by
`decide +kernel` with the instance `Dec.decCF` (S15, the fragment
without `!`): no certificate is written.

Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Date: 2026-11-26 15:42 GMT.  Loading the imports: 0.92 s, taken off.  Deadline 120 s.

| n | formulas in the sequent | the kernel running the proved search (`decide +kernel`) |
|---|---|---|
| 1 | 2 | 0.01 s |
| 2 | 3 | 0.03 s |
| 3 | 4 | 0.12 s |
| 4 | 5 | 0.10 s |
| 5 | 6 | 0.20 s |
| 6 | 7 | 1.00 s |
| 7 | 8 | 5.99 s |
| 8 | 9 | 34.89 s |
| 9 | 10 | flag (> 120 s) |

## The frontier, and what the figures say

* **The kernel's check of the set**: settled to `n = 6` (7 formulas, a
  set of 200 sequents, 18.66 s); `n = 7` (8 formulas, a set of 499) is
  not settled in 120 s.
* **The producer**: settled to `n = 10` (a set of 6366); `n = 11` is not
  settled in 60 s. The time is the compiled check of its own set
  (31.8 s at `n = 10`), not the search (0.35 s) or the cut to the set
  (0.27 s).
* **The set is every sequent the search settled "no"**, at every `n`
  and with either choice: 1, 3, 9, 27, 76, 200, 499, 1197, 2790, 6366.
  The cut removes nothing here, and no choice can do much better: at
  the first sequent alone, each instance of ⊸L (one of the `n − 1`
  implications, with one of the `2ⁿ⁻¹` divisions of the rest) has two
  premises, no premise belongs to two instances, and the set must have
  one for each: at least `(n − 1)·2ⁿ⁻¹` members (384 of the 499 at
  `n = 7`). A saturated set for this family is exponential in `n`
  whatever the producer.
* **On this family the proved search is the cheaper route in the
  kernel from `n = 5` on** (0.20 s against 1.77 s at `n = 5`, 1.00 s
  against 18.66 s at `n = 6`), and goes two sizes further (`n = 8` in
  34.89 s; flag at `n = 9`). The check looks every premise up by a
  pass over the whole set, for every division at every member; the
  search meets a sequent, decides it, and goes on.
* **Where the set is the only route**: a sequent with `!` is outside
  the proved search's fragment. The facts `bang_right`, `bang_lolli`
  and `bang_in_plus` of `DILL/SatTest.lean` are checked by the kernel
  with sets of 1, 5 and 2 sequents.
* **What was tried on the check's constant** (scratch copies of the
  check, one run each on the set of `n = 6`, imports of about 1 s
  included): as it is, 20.10 s; with the lengths of the linear zones
  compared before `permB`, 16.83 s; with a Boolean equality of formulas
  written by hand, for the conclusions and for the counting, 14.67 s.
  None changes the order, and none was adopted.
* **What would change the order** (not done: the statements of S16 fix
  the certificate as `List Seq`): a certificate that says, for each
  rule instance at each member, where in the list its premise is
  (R8 of `lean-certify`: "add a witness"); the check is then one
  comparison for each instance, in place of a pass over the set.

## What the producer answers nothing for

`refuteSet` is `none` at once where the unrestricted zone is not empty,
and `none` where the search answers that the sequent is in no saturated
set: it has a derivation without cut (`Refute.outcome`: `derivable`), or
a sequent with `!` in its linear zone was set aside on the way
(`noSet`). No saturated set has a member with a non-empty unrestricted
zone or with `!A` in its linear zone: `Sat.unr_nil`, `Sat.no_bang`
(`DILL/Saturated.lean`), proved. So for `· ; !p ⟹ q`, which has no
derivation, there is no certificate of this kind: a flag, as the plan
says (level 2).
