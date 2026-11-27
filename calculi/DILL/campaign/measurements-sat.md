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

## The cost of the check: its cause, and the repair (2026-11-27)

By the owner session, on the directing session's task (method note 23).
The table above is of the definition's check (`refutedBy`), which the
certifiers ran until this date: 18.66 s at 200 sequents, no answer at
499, and compiled 31.8 s at 6366. The certifiers now run `refutedFast`
(`DILL/SatFast.lean`, statement S20). Each run of Lean below: one at a
time, a cap on memory, a deadline on the process group; "peak" is the
process's, the 1.3 GB of the imports included.

### What the kernel was doing

**The count.** The definition asks, for each premise that a rule needs
at a member, every member in turn whether it is that premise
(`memS`: a scan), and compares two sequents by counting every formula
of both zones (`permB`). Counted by a copy of the check that counts
(`#eval`, on the sets of the family):

| the set: sequents | longest zone | divisions of a zone | questions "is this premise a member" | pairs of sequents compared | zones compared by counting | the kernel, the definition's check |
|---|---|---|---|---|---|---|
| 27 | 4 | 80 | 88 | 1 567 | 477 | 0.11 s |
| 76 | 5 | 416 | 439 | 19 311 | 5 133 | 1.37 s |
| 200 | 6 | 1 990 | 2 057 | 214 663 | 49 726 | 16.0 s, peak 5 705 MB (`-M 8000`) |
| 499 | 7 | 8 866 | 9 053 | 2 186 805 | 442 402 | not settled in 120 s (2026-11-26) |
| 1197 | 8 | 37 308 | 37 802 | 20 797 755 | 3 702 090 | not run |

The kernel's time follows the fifth column: 69, 71 and 75 µs a pair.
The questions grow as the set to the power 1.6; the pairs, as the
questions times half the set: the power 2.4 to 2.6. So the growth is
the scan, and it is in the compiled check too (4 ms, 38 ms, 402 ms,
3.7 s, 31.8 s from 200 to 6366 in the table above), where it was read
as the producer's time. The smallest input that shows it is the step
from 27 sequents to 76: 2.8 times the sequents, 12 times the time.

**What a step costs the kernel.** Measured on lists made for it
(`decide +kernel`, the profiler's "type checking"):

| | the kernel |
|---|---|
| 20 000 elements of a list walked, one comparison of numbers at each | 0.60 s: 30 µs an element |
| an arithmetic operation on small numbers (`+ * % /`), among 20 000 × 6 | 3.5 µs |
| a shift of a number of 600 000 bits, among 5 000 | 30 µs |
| a term already reduced, asked again (20 000 times) | 3 µs |
| two different formulas compared by the derived `DecidableEq`, while a zone of 128 is searched | 180 µs a formula |
| the same with an equality written by hand | 99 µs |
| the same with the numbers of the formulas compared first (`eqH`) | 40 µs |

So a step of a recursion over a list is some 10 µs, and nothing that
goes through a list a member at a time is cheap; a term the kernel has
met is cheap; arithmetic is the cheapest work there is.

**The 8 GB, and the two statements of one Boolean** (note 22, point 4).
The two statements cost the kernel the same: alone in a file, on the
set of 200,

| the statement of `checked` | the kernel | peak (`-M 8000`) |
|---|---|---|
| `noCFBySet.check sequent saturated = true` | 16.0 s | 5 705 MB |
| `refutedBy saturated sequent = true` | 16.5 s | 5 705 MB |

The difference was in the two facts that use `checked`. Each is
`K.verdict _ saturated checked`, and Lean has to find the type of
`checked` equal to `K.check sequent saturated = true`. Where `checked`
is stated through the certifier the two are the same text. Where it is
stated of `refutedBy`, the elaborator unfolds the side that is not a
projection, and goes on to compute the whole check itself, outside the
kernel, once for each fact, while the kernel runs it too. On the set of
76 (`Elab.async false`, the profiler):

| `checked` stated | the kernel, for `checked` | elaboration of `notCutFree` | elaboration of `notDerivable` | the file | peak |
|---|---|---|---|---|---|
| of `refutedBy` | 1.36 s | 3.59 s | 3.55 s | 10.4 s | 1 861 MB |
| through the certifier | 1.39 s | under 0.05 s | under 0.05 s | 2.4 s | 1 765 MB |

At 200 sequents that is the kernel's 5.7 GB and two computations by the
elaborator, each slower than the kernel's and in threads of their own:
past 8 GB. The kernel was not unfolding anything differently.

### The repair

`refutedFast` (S20) asks the same questions of a set that answers
without a scan: zones in one order, members in a binary tree at the
leaf that a number computed from the sequent leads to, a premise looked
for at its leaf and compared there formula by formula. Proved sound for
the definition; the definition is unchanged. Three forms were tried,
each measured in the kernel at 200 sequents before any proof:

| form | the kernel at 200 |
|---|---|
| the definition | 16.0 s |
| the tree, descended by `if k % 2 == 0` (instances unfolded at each level) | 1.88 to 2.18 s |
| the tree, descended by `bif Nat.beq (k % 2) 0`, lists compared by a function of their own | 1.38 to 1.6 s |
| the same with a shallower tree (leaves of 4, 16, 64 members) | 1.5 s, 2.0 s, 4.1 s |
| the one built, through the certifier | 1.25 to 1.6 s |

Of the 1.4 s: 0.2 s is the divisions and the premises built, 0.15 s the
numbers of the premises, 0.45 s the descent of the tree, 0.55 s the
comparison at the leaf. Each question now costs 0.7 to 1.0 ms and
about 190 KB of the kernel's memory, whatever the size of the set.

**In parts.** The kernel keeps what it has reduced until the theorem is
done, so a set of 1197 (37 802 questions) passed 4 GB in one run. The
check is `headOk D j && restOk D (D.map canon)`, and `restOk` holds of
a list where it holds of its first `c` and of the rest
(`Sat.restOk_step`): `dillrun prove` states a set of more than some
6000 questions as theorems of 6000 each, one after another, and joins
them.

### Before and after

`python3 -I Corpus/measure_checks.py sets`. The family is the table's
above ("the chain with its last link missing"). The last column is the
check as it was: the same printed file with `checked` stated of the
definition, `refutedBy saturated sequent = true`.

Machine: arm64, macOS-15.8.3-arm64-arm-64bit; Lean v4.31.0.  Date: 2026-11-27 11:06 GMT.  Each run of Lean: `-M 4000`, a deadline of 300 s on the process group, one at a time.  Loading the imports: 1.06 s, taken off the times; the peaks of memory include it (about 1300 MB).

| n | formulas in the sequent | the set: sequents | the compiled check that is run (`refutedFast`) | the compiled check of the definition (`refutedBy`) | `dillrun prove`, the whole process | the printed file: parts | the printed file, elaborated: the kernel checks the set | the definition's check, run by the kernel |
|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 1 | 0.0 ms | 0.0 ms | 0.03 s | 1 | 0.02 s, 1290 MB | 0.03 s, 1288 MB |
| 2 | 3 | 3 | 0.0 ms | 0.0 ms | 0.03 s | 1 | 0.04 s, 1292 MB | 0.01 s, 1290 MB |
| 3 | 4 | 9 | 0.0 ms | 0.0 ms | 0.03 s | 1 | 0.03 s, 1296 MB | 0.04 s, 1296 MB |
| 4 | 5 | 27 | 0.1 ms | 0.1 ms | 0.03 s | 1 | 0.06 s, 1313 MB | 0.18 s, 1342 MB |
| 5 | 6 | 76 | 0.2 ms | 0.5 ms | 0.03 s | 1 | 0.66 s, 1391 MB | 1.86 s, 1766 MB |
| 6 | 7 | 200 | 0.9 ms | 4.1 ms | 0.03 s | 1 | 1.60 s, 1710 MB | refused: stopped at the cap on memory (after 72 s, 7395 MB; see below) |
| 7 | 8 | 499 | 4.2 ms | 40.9 ms | 0.04 s | 2 | 8.06 s, 2362 MB | not run |
| 8 | 9 | 1197 | 17.4 ms | 406.4 ms | 0.08 s | 8 | 38.50 s, 2762 MB | not run |
| 9 | 10 | 2790 | 80.7 ms | 3777.4 ms | 0.27 s | 28 | 198.44 s, 3521 MB | not run |
| 10 | 11 | 6366 | 297.5 ms | 31122.7 ms | 1.00 s | 106 | refused: stopped at the cap on memory (after 22 s, 4195 MB) | not run |
| 11 | 12 | 14293 | 1249.6 ms | not run | 4.09 s | 404 | not run | not run |

What the table says:

* **The kernel now checks the set of 200 in 1.6 s (16.0 s), that of 499
  in 8.1 s, of 1197 in 38.5 s and of 2790 in 198 s**, each within the
  cap of 4000 MB. The time is now the number of questions: 0.78 ms a
  question at 200, 0.89 ms at 499, 1.02 ms at 1197; at 2790 the tree is
  built again in each of 28 parts.
* **The definition's check, in the kernel, does not fit the cap at
  200** (alone under `-M 8000` it took 16.0 s and 5 705 MB, above). In
  a first run of this table it was stopped after 12 s at 4 195 MB. In
  the run shown the process went on for 72 s and reached 7 395 MB under
  `-M 4000` before it stopped. The likely cause, not isolated: when the
  kernel refuses, `decide +kernel` computes the instance again in the
  elaborator in order to say why (its message, seen on 2026-11-26: "the
  elaborator is able to reduce the `Decidable` instance, but the kernel
  fails with …"), and the cap did not stop that at once. The script no
  longer runs this column past 76 sequents.
* **The set of 6366 is not checked.** Its file has 106 parts, and the
  first stopped at the cap after 22 s: a part holds the whole set (the
  list, each zone in order, the tree) as well as its own questions, and
  at 6366 that alone passes 4 GB. The largest size the kernel has
  checked on this family is 2790. No second family was measured.
* **Compiled, the check that is run is 4.6 to 105 times faster than the
  definition's**, and the more the larger the set: 0.9 ms against
  4.1 ms at 200, 81 ms against 3.8 s at 2790, 0.30 s against 31.1 s at
  6366. The producer, which checks its own set before it hands it on,
  now settles `n = 11` (a set of 14 293) in 4 s; on 2026-11-26 it did
  not in 60 s. (A first run of the table, with the numbers of the
  formulas compared first in compiled code as well, had 1.7 ms, 157 ms
  and 0.64 s in that column: `eqH` is the plain equality for compiled
  code since, `eqH_csimp`.)
* **Against compiled code the kernel is some four orders of magnitude
  slower on the same check** (0.9 ms and 1.6 s at 200; 81 ms and 198 s
  at 2790). That is the price of a step in the kernel, not the scan.

### Not repaired

* A question still costs the kernel about 0.7 ms where compiled code
  takes a microsecond: the check goes through lists a member at a time,
  and that is what the kernel is slow at. A check by arithmetic alone
  (formulas as numbers, a zone as one number, the set as a table inside
  one number) would ask the same questions in a few operations each; it
  needs the codes proved injective, and was not attempted.
* The number of questions is the definition's: every division of a zone
  at every implication, `2ᵐ` for a zone of `m`. It grows as the set to
  the power 1.6 on this family.
* `refutedFast` is proved sound, not equal to the definition (S20).

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

(As measured 2026-11-26, of the definition's check. Superseded for the
kernel and for the compiled check by "The cost of the check" above:
the kernel now checks the set of 2790; the producer settles `n = 11`.)

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
