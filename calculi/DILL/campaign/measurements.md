# DILL: what runs on the "yes" side, and how fast

Written 2026-11-26 16:26 GMT by agent G of the Run stage (`campaign/brief-3-1.md`,
section G). Machine: Apple M4 Pro, 48 GB, macOS 15.8.3, arm64; Lean
v4.31.0. Every figure below is pasted from a run, and each table says
which run. The times are single runs (the least of three where a fact
took under 5 s). The measuring was **stopped by the operator at 16:21
GMT**: where a column was not taken to its frontier, that is said, and
the largest size settled is a lower bound on the frontier, not the
frontier. The side against a derivation is `campaign/measurements-sat.md`.

## What runs

| | what | where | trusted? |
|---|---|---|---|
| trees and scripts, checked | `treeCert`, `scriptCert : Certify.Certifier Seq _ (Fam true)`: `Cert.check` and `derives` run `step` | `DILL/Run.lean` | yes, through S1 (`step_sound`) |
| the search | `Lazy.prove j n : Option (Cert S)`: without cut; input and output zones at ⊗R and ⊸L, a flag for ⊤R and 0L; the invertible rules first; `n` is the number of copies allowed along a branch | `DILL/Lazy.lean` | no: `partial`, not proved |
| its two modes | "chained" (`focus := true`, the default): the left rules on one formula down to an atom, which must be the conclusion (backward chaining). "As in the figure" (`focus := false`): ⊸L and &L as CCP's Figure 2 has them, any rule after | `DILL/Lazy.lean`, `Cfg` | no |
| the producer | `Run.proveLazy` (a tree, checked before it is handed on), `Run.produce : Seq → Nat → Certify.Verdict (Script S) Unit` (`pass` or `flag`, never `fail`) | `DILL/Run.lean` | no |
| the driver | `dillrun status`, `facts`, `tree`, `run`, `cert`, `fuzz` | `Main.lean` | no |

The lints of `lean-certify`: R3 and R2 pass on `treeCert` and
`scriptCert` (for the script, with the library's note on `Nat.repr`);
R1 reports nothing on `produce` and `produceTree`; R4 passes on the
eight facts of `DILL/RunTest.lean`. The file `DILL/Run.lean` ends with
`#axioms_within_file [propext, Quot.sound]`.

A failure of the search is a **flag**, never a "no". Two kinds are told
apart in the tables: "nothing, and no copy refused" (the search ended
without ever wanting a copy that the budget refused: a larger budget
changes nothing) and "nothing to budget `n`" (copies were refused). That
the first kind means there is no derivation would need the completeness
of the search, which is not proved; the kernel never sees a failure.

## The corpus

56 sequents of known status (`DILL/Corpus/Basic.lean`): 39 derivable, 17
not. The status is from CCP pp. 16-18, the plan's Q4 (the laws of `!`)
and the plan's "Known non-theorems" where they say so, and otherwise
ours, with the reason in the file.

**From the run** `dillrun status 4 200000` of 2026-11-26 15:41 GMT (the
driver compiled from these sources; budgets 0 to 4 tried in turn, a cap
of 200000 calls at each; the whole run 0.63 s). It ended with "56
entries; 0 where a producer disagrees with the status". The operator's
run of `dillrun status 3` after the restart gave "agrees" on every
entry. What the columns are: **budget**, the least number of copies
along a branch at which the chained search finds a tree that the
compiled checker accepts (the search as in the figure found each entry
at the same budget, with a tree of the same number of moves and the
same nesting); **moves** and **nesting**, the number of nodes of that
tree and its height; **calls**, the calls of `solve` summed over the
budgets tried, chained and then as in the figure; **the decision**,
what the proved search of `DILL/Decide.lean` answers where it applies
(an empty unrestricted zone, no `!`, at most 14 signs).

The 39 derivable entries: each found, each tree accepted.

| entry | sequent | budget | moves | nesting | calls, chained | calls, as in the figure | the decision without `!` |
|---|---|---|---|---|---|---|---|
| init | `· ; p ⟹ p` | 0 | 1 | 1 | 1 | 1 | a derivation |
| copyInit | `p ; · ⟹ p` | 1 | 2 | 2 | 2 | 2 | not applicable |
| modusPonens | `· ; p, p ⊸ q ⟹ q` | 0 | 3 | 2 | 2 | 3 | a derivation |
| withFst | `· ; p & q ⟹ p` | 0 | 2 | 2 | 1 | 2 | a derivation |
| withSnd | `· ; p & q ⟹ q` | 0 | 2 | 2 | 1 | 3 | a derivation |
| lolliSelf | `· ; p ⊸ q ⟹ p ⊸ q` | 0 | 1 | 1 | 1 | 1 | a derivation |
| bangDerelict | `· ; !p ⟹ p` | 1 | 3 | 3 | 2 | 2 | not applicable |
| bangDig | `· ; !p ⟹ !!p` | 1 | 5 | 5 | 6 | 6 | not applicable |
| bangContract | `· ; !p ⟹ !p ⊗ !p` | 1 | 8 | 5 | 8 | 8 | not applicable |
| bangWeaken | `· ; !p ⟹ 1` | 0 | 2 | 2 | 1 | 1 | not applicable |
| bangWithTensor | `· ; !(p & q) ⟹ !p ⊗ !q` | 1 | 10 | 6 | 8 | 11 | not applicable |
| bangTensorWith | `· ; !p ⊗ !q ⟹ !(p & q)` | 1 | 9 | 7 | 7 | 7 | not applicable |
| bangMap | `· ; !p, !(p ⊸ q) ⟹ !q` | 2 | 8 | 7 | 8 | 11 | not applicable |
| tensorComm | `· ; p ⊗ q ⟹ q ⊗ p` | 0 | 4 | 3 | 3 | 3 | a derivation |
| tensorAssoc | `· ; (p ⊗ q) ⊗ r ⟹ p ⊗ (q ⊗ r)` | 0 | 7 | 5 | 5 | 5 | a derivation |
| unitL | `· ; 1 ⊗ p ⟹ p` | 0 | 3 | 3 | 1 | 1 | a derivation |
| unitR | `· ; p ⟹ p ⊗ 1` | 0 | 3 | 2 | 3 | 3 | a derivation |
| curry | `· ; (p ⊗ q) ⊸ r ⟹ p ⊸ (q ⊸ r)` | 0 | 7 | 5 | 6 | 7 | a derivation |
| uncurry | `· ; p ⊸ (q ⊸ r) ⟹ (p ⊗ q) ⊸ r` | 0 | 7 | 5 | 4 | 6 | a derivation |
| distrib | `· ; p ⊗ (q ⊕ r) ⟹ (p ⊗ q) ⊕ (p ⊗ r)` | 0 | 10 | 5 | 11 | 11 | a derivation |
| distrib' | `· ; (p ⊗ q) ⊕ (p ⊗ r) ⟹ p ⊗ (q ⊕ r)` | 0 | 11 | 5 | 9 | 9 | a derivation |
| withPair | `· ; (p ⊸ q) & (p ⊸ r) ⟹ p ⊸ (q & r)` | 0 | 10 | 5 | 6 | 13 | a derivation |
| plusCase | `· ; (p ⊸ r) & (q ⊸ r) ⟹ (p ⊕ q) ⊸ r` | 0 | 10 | 5 | 6 | 11 | a derivation |
| plusComm | `· ; p ⊕ q ⟹ q ⊕ p` | 0 | 5 | 3 | 5 | 5 | a derivation |
| withComm | `· ; p & q ⟹ q & p` | 0 | 5 | 3 | 3 | 6 | a derivation |
| topSlack | `· ; p, q, r ⟹ p ⊗ ⊤` | 0 | 3 | 2 | 3 | 3 | a derivation |
| topSplit | `· ; p, q ⟹ ⊤ ⊗ ⊤` | 0 | 3 | 2 | 3 | 3 | a derivation |
| zeroL | `· ; 0, p ⟹ q` | 0 | 1 | 1 | 0 | 0 | a derivation |
| zeroSlack | `· ; p, q ⊸ 0, q ⟹ r ⊗ s` | 0 | 3 | 2 | 5 | 5 | a derivation |
| bangK | `· ; !(p ⊸ q) ⟹ !p ⊸ !q` | 2 | 9 | 8 | 11 | 13 | not applicable |
| bangTensor | `· ; !p, !q ⟹ !(p ⊗ q)` | 1 | 8 | 6 | 7 | 7 | not applicable |
| bangPlus | `· ; !p ⊕ !q ⟹ !(p ⊕ q)` | 1 | 11 | 6 | 11 | 11 | not applicable |
| validBang | `p ; · ⟹ !p` | 1 | 3 | 3 | 4 | 4 | not applicable |
| copyTwice | `p ; · ⟹ p ⊗ p` | 1 | 5 | 3 | 5 | 5 | not applicable |
| copyTensor | `p ⊗ q ; · ⟹ q ⊗ p` | 1 | 5 | 4 | 8 | 8 | not applicable |
| copyBang | `!p ; · ⟹ p` | 2 | 4 | 4 | 5 | 5 | not applicable |
| copyChain | `p ⊸ q, q ⊸ r ; p ⟹ r` | 2 | 7 | 5 | 6 | 11 | not applicable |
| bangLoopFree | `· ; !(p ⊸ p), p ⟹ p` | 0 | 2 | 2 | 1 | 1 | not applicable |
| bangDouble | `· ; !(p ⊸ (p ⊗ p)), p ⟹ p ⊗ p` | 1 | 8 | 6 | 12 | 13 | not applicable |

Budget 0: 23 entries. Budget 1: 12. Budget 2: 4 (`bangMap`, `bangK`,
`copyBang`, `copyChain`).

The 17 entries with no derivation: each a flag, as it must be.

| entry | sequent | chained | as in the figure | the decision without `!` |
|---|---|---|---|---|
| zeroGoal | `· ; · ⟹ 0` | nothing, and no copy refused (1 calls) | nothing, and no copy refused (1 calls) | none |
| weakenOne | `· ; p ⟹ 1` | nothing, and no copy refused (1 calls) | nothing, and no copy refused (1 calls) | none |
| weakenInit | `· ; p, q ⟹ p` | nothing, and no copy refused (1 calls) | nothing, and no copy refused (1 calls) | none |
| contract | `· ; p ⟹ p ⊗ p` | nothing, and no copy refused (3 calls) | nothing, and no copy refused (3 calls) | none |
| pfenning60 | `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)` | nothing, and no copy refused (7 calls) | nothing, and no copy refused (6 calls) | none |
| noPromote | `· ; p ⟹ !p` | nothing, and no copy refused (2 calls) | nothing, and no copy refused (2 calls) | not applicable |
| plusProj | `· ; p ⊕ q ⟹ p` | nothing, and no copy refused (2 calls) | nothing, and no copy refused (2 calls) | none |
| withIntro | `· ; p ⟹ p & q` | nothing, and no copy refused (3 calls) | nothing, and no copy refused (3 calls) | none |
| bangLolli | `· ; !p ⊸ q ⟹ p ⊸ q` | nothing, and no copy refused (4 calls) | nothing, and no copy refused (4 calls) | not applicable |
| ccp18a | `· ; · ⟹ p` | nothing, and no copy refused (1 calls) | nothing, and no copy refused (1 calls) | none |
| ccp18b | `· ; q ⟹ p ⊸ q` | nothing, and no copy refused (2 calls) | nothing, and no copy refused (2 calls) | none |
| withTensor | `· ; p & q ⟹ p ⊗ q` | nothing, and no copy refused (3 calls) | nothing, and no copy refused (10 calls) | none |
| tensorWith | `· ; p ⊗ q ⟹ p & q` | nothing, and no copy refused (3 calls) | nothing, and no copy refused (3 calls) | none |
| loop | `· ; !(p ⊸ p) ⟹ p` | nothing to budget 4 (15 calls, 1 copies refused at 4) | nothing to budget 4 (15 calls, 1 copies refused at 4) | not applicable |
| loopU | `p ⊸ p ; · ⟹ p` | nothing to budget 4 (15 calls, 1 copies refused at 4) | nothing to budget 4 (15 calls, 1 copies refused at 4) | not applicable |
| pump | `· ; !(p ⊸ (p ⊗ p)), p ⟹ q` | nothing to budget 4 (15 calls, 1 copies refused at 4) | nothing to budget 4 (57 calls, 16 copies refused at 4) | not applicable |
| bangPlusNo | `· ; !(p ⊕ q) ⟹ !p ⊕ !q` | nothing to budget 4 (318 calls, 83 copies refused at 4) | nothing to budget 4 (318 calls, 83 copies refused at 4) | not applicable |

So 13 are flagged with no copy refused, and 4 (`loop`, `loopU`, `pump`,
`bangPlusNo`) at the budget: these are the ones where a copy can always
be made, and no budget ends the search.

**The facts.** `dillrun facts 4 200000` wrote a file of 39 derivations
(`def <entry> : Fam true (<sequent>) := treeCert.verdict _ (<tree>)`)
and 17 comments, ending with `#axioms_within_file [propext, Quot.sound]`;
`lake env lean` elaborated it with no message in 1.34 s, imports
included (run of 15:43 GMT, into `Corpus/out/run/Facts.lean`, which is
not kept: the brief does not list a facts file among this agent's; the
operator may write it with `dillrun facts > DILL/Corpus/Facts.lean`).

**The search against a derivation by hand.** For the 11 derivations of
`DILL/Source.lean` at letters, the number of rule instances and the
height (counted by a function on `Fam`, in a scratch file, 15:48 GMT)
are those of the search's tree in the table above, entry by entry:
copyInit 2 and 2, modusPonens 3 and 2, withFst 2 and 2, withSnd 2 and
2, bangDerelict 3 and 3, bangDig 5 and 5, bangContract 8 and 5,
bangWeaken 2 and 2, bangWithTensor 10 and 6, bangTensorWith 9 and 7,
bangMap 8 and 7. The search has nothing to learn from them.

## Negative tests (R9)

`DILL/RunTest.lean`, each `… = false := by decide +kernel`; the file
builds (`lake build DILL.RunTest`).

| test | the certificate refused |
|---|---|
| `bad_division_rejected` | ⊸L that gives nothing to its first premise, at `· ; p, p ⊸ q ⟹ q` |
| `contraction_rejected` | ⊗R at `· ; p ⟹ p ⊗ p` with `p` for the first premise and init for both |
| `weakening_rejected` | init at `· ; p, q ⟹ p` |
| `bad_copy_rejected` | a copy of `p` at `q ; · ⟹ p` |
| `bad_bangR_rejected` | !R at `· ; p ⟹ !p` |
| `wrong_move_rejected` | &L₂ where the derivation of `· ; !(p & q) ⟹ !p ⊗ !q` has &L₁ |
| `short_tree_rejected` | a tree that stops early: ⊸L with one tree for two premises |
| `missing_copy_rejected` | the tree of `chainU 3` with one copy left out |
| `bad_script_rejected` | a script with a wrong division on its second line |
| `short_script_rejected` | a script that stops one line early |

Beside them, by `#guard` (compiled): the search returns the pasted tree
for each of the seven facts; `bangMap` at budget 1 and `chainU 3` at
budget 2 give nothing; `produce` answers `pass` or `flag`; and on the
whole corpus `(proveLazy e.seq 2).isSome == e.derivable`.

## The families

`chain n`: `· ; a₀, a₀ ⊸ a₁, …, aₙ₋₁ ⊸ aₙ ⟹ aₙ`. `chainU n`: the same
with the implications in the unrestricted zone, `a₀ ⊸ a₁, … ; a₀ ⟹ aₙ`,
which needs `n` copies along a branch. `fan n`: `· ; aₙ, …, a₁ ⟹ a₁ ⊗
(a₂ ⊗ … ⊗ aₙ)`. `chainBad n`: `chain` with its last link missing, `· ;
a₀, a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ⟹ aₙ`, no derivation. `chainUBad n`: the same
with the implications in the unrestricted zone.

**From the run** `python3 -I Corpus/measure.py` of 16:05 to 16:15 GMT,
one case at a time, each run of Lean with `-M 8000`, the sizes listed in
the script and none above 1024. What each column measures:

* *the search, left rules chained*: `dillrun cert focus`, compiled: the
  tree's number of moves, its nesting, the copies on its longest
  branch; the calls of `solve`; the time of the search alone;
* *the compiled check of its tree*: `Cert.check`, compiled, on that tree;
* *the search, left rules as in the figure*: `dillrun run plain`, the
  same search with `focus := false`;
* *the fact with the tree*: `lake env lean -M 8000` on a file with
  `def fact : Fam true (Corpus.<family> n) := treeCert.verdict _ (<tree>)`,
  under `set_option maxRecDepth 100000`: parsing, elaboration and the
  kernel's check, one figure, less the time to load the imports. It is
  the kernel's time in all but name: with Lean's profiler on `chain 64`
  (15:49 GMT) "type checking" took 11.4 s of the 13.5 s of the run;
* *the fact with the script*: the same with `scriptCert.verdict` and the
  script of the same derivation;
* *the kernel running the proved search*: `example : Nonempty (CF …) :=
  by decide +kernel` (or its negation) with the instance of
  `DILL/Decide.lean`, no certificate; where that file applies.

Machine: arm64, macOS-15.8.3-arm64-arm-64bit.  Date: 2026-11-26 16:05 GMT.  Loading the imports: 0.88 s (0.86 s for the last column), taken off the times of the last three columns.
Deadlines: each run of the driver 20 s (search and compiled check together), each fact 60 s.  `flag`: cut off at the deadline, or not elaborated; the column stops there.

| family | n | formulas in the sequent | budget (copies along a branch) | status | the search, left rules chained: its answer, calls, time | the compiled check of its tree | the search, left rules as in the figure: its answer, calls, time | the fact with the tree: elaborated, and checked by the kernel | the fact with the script | the kernel running the proved search (`decide +kernel`) |
|---|---|---|---|---|---|---|---|---|---|---|
| chain | 2 | 4 | 0 | derivable | a tree of 5 moves, nesting 3, 0 copies; 3 calls, 0.0 ms | 0.0 ms | a tree of 5 moves; 5 calls, 0.0 ms | 0.03 s | 0.02 s | 0.02 s |
| chain | 4 | 6 | 0 | derivable | a tree of 9 moves, nesting 5, 0 copies; 5 calls, 0.0 ms | 0.0 ms | a tree of 9 moves; 9 calls, 0.0 ms | 0.03 s | 0.03 s | 0.06 s |
| chain | 8 | 10 | 0 | derivable | a tree of 17 moves, nesting 9, 0 copies; 9 calls, 0.0 ms | 0.0 ms | a tree of 17 moves; 17 calls, 0.0 ms | 0.08 s | 0.10 s | flag: not elaborated (deterministic timeout) |
| chain | 16 | 18 | 0 | derivable | a tree of 33 moves, nesting 17, 0 copies; 17 calls, 0.0 ms | 0.1 ms | a tree of 33 moves; 33 calls, 0.0 ms | 0.32 s | 0.38 s | not run |
| chain | 32 | 34 | 0 | derivable | a tree of 65 moves, nesting 33, 0 copies; 33 calls, 0.0 ms | 0.2 ms | a tree of 65 moves; 65 calls, 0.1 ms | 1.46 s | 1.43 s | not run |
| chain | 64 | 66 | 0 | derivable | a tree of 129 moves, nesting 65, 0 copies; 65 calls, 0.1 ms | 1.3 ms | a tree of 129 moves; 129 calls, 0.4 ms | 8.14 s | 8.54 s | not run |
| chain | 96 | 98 | 0 | derivable | a tree of 193 moves, nesting 97, 0 copies; 97 calls, 0.1 ms | 4.4 ms | a tree of 193 moves; 193 calls, 1.2 ms | flag: not elaborated (deterministic timeout) | flag: not elaborated (deterministic timeout) | not run |
| chain | 128 | 130 | 0 | derivable | a tree of 257 moves, nesting 129, 0 copies; 129 calls, 0.2 ms | 9.7 ms | a tree of 257 moves; 257 calls, 2.7 ms | not run | not run | not run |
| chain | 256 | 258 | 0 | derivable | a tree of 513 moves, nesting 257, 0 copies; 257 calls, 0.4 ms | 77.9 ms | a tree of 513 moves; 513 calls, 18.3 ms | not run | not run | not run |
| chain | 512 | 514 | 0 | derivable | a tree of 1025 moves, nesting 513, 0 copies; 513 calls, 1.6 ms | 606.2 ms | a tree of 1025 moves; 1025 calls, 143.2 ms | not run | not run | not run |
| chain | 1024 | 1026 | 0 | derivable | a tree of 2049 moves, nesting 1025, 0 copies; 1025 calls, 6.9 ms | 4716.0 ms | a tree of 2049 moves; 2049 calls, 1164.9 ms | not run | not run | not run |
| chainU | 2 | 4 | 2 | derivable | a tree of 7 moves, nesting 5, 2 copies; 3 calls, 0.0 ms | 0.0 ms | a tree of 7 moves; 6 calls, 0.0 ms | 0.00 s | 0.01 s | not applicable |
| chainU | 4 | 6 | 4 | derivable | a tree of 13 moves, nesting 9, 4 copies; 5 calls, 0.0 ms | 0.0 ms | a tree of 13 moves; 61 calls, 0.0 ms | 0.01 s | 0.02 s | not applicable |
| chainU | 8 | 10 | 8 | derivable | a tree of 25 moves, nesting 17, 8 copies; 9 calls, 0.0 ms | 0.0 ms | a tree of 25 moves; 17970048 calls, 2362.8 ms | 0.02 s | 0.05 s | not applicable |
| chainU | 16 | 18 | 16 | derivable | a tree of 49 moves, nesting 33, 16 copies; 17 calls, 0.0 ms | 0.0 ms | flag (> 20 s) | 0.05 s | 0.14 s | not applicable |
| chainU | 32 | 34 | 32 | derivable | a tree of 97 moves, nesting 65, 32 copies; 33 calls, 0.0 ms | 0.0 ms | not run | 0.17 s | 0.31 s | not applicable |
| chainU | 64 | 66 | 64 | derivable | a tree of 193 moves, nesting 129, 64 copies; 65 calls, 0.1 ms | 0.0 ms | not run | 0.51 s | 0.74 s | not applicable |
| chainU | 96 | 98 | 96 | derivable | a tree of 289 moves, nesting 193, 96 copies; 97 calls, 0.1 ms | 0.1 ms | not run | 1.08 s | 1.47 s | not applicable |
| chainU | 128 | 130 | 128 | derivable | a tree of 385 moves, nesting 257, 128 copies; 129 calls, 0.2 ms | 0.1 ms | not run | 1.89 s | 2.29 s | not applicable |
| chainU | 256 | 258 | 256 | derivable | a tree of 769 moves, nesting 513, 256 copies; 257 calls, 0.6 ms | 0.4 ms | not run | 7.34 s | 8.25 s | not applicable |
| chainU | 512 | 514 | 512 | derivable | a tree of 1537 moves, nesting 1025, 512 copies; 513 calls, 2.3 ms | 1.6 ms | not run | flag: not elaborated (deterministic timeout) | flag: not elaborated (deterministic timeout) | not applicable |
| chainU | 1024 | 1026 | 1024 | derivable | a tree of 3073 moves, nesting 2049, 1024 copies; 1025 calls, 8.2 ms | 5.8 ms | not run | not run | not run | not applicable |
| fan | 2 | 3 | 0 | derivable | a tree of 3 moves, nesting 2, 0 copies; 3 calls, 0.0 ms | 0.0 ms | a tree of 3 moves; 3 calls, 0.0 ms | 0.00 s | 0.00 s | 0.00 s |
| fan | 4 | 5 | 0 | derivable | a tree of 7 moves, nesting 4, 0 copies; 7 calls, 0.0 ms | 0.0 ms | a tree of 7 moves; 7 calls, 0.0 ms | 0.00 s | 0.01 s | 0.00 s |
| fan | 8 | 9 | 0 | derivable | a tree of 15 moves, nesting 8, 0 copies; 15 calls, 0.0 ms | 0.0 ms | a tree of 15 moves; 15 calls, 0.0 ms | 0.02 s | 0.06 s | 0.36 s |
| fan | 16 | 17 | 0 | derivable | a tree of 31 moves, nesting 16, 0 copies; 31 calls, 0.0 ms | 0.0 ms | a tree of 31 moves; 31 calls, 0.0 ms | 0.16 s | 0.25 s | flag: not elaborated (deterministic timeout) |
| fan | 32 | 33 | 0 | derivable | a tree of 63 moves, nesting 32, 0 copies; 63 calls, 0.0 ms | 0.2 ms | a tree of 63 moves; 63 calls, 0.0 ms | 0.73 s | 0.84 s | not run |
| fan | 64 | 65 | 0 | derivable | a tree of 127 moves, nesting 64, 0 copies; 127 calls, 0.1 ms | 0.8 ms | a tree of 127 moves; 127 calls, 0.1 ms | 4.66 s | 4.75 s | not run |
| fan | 96 | 97 | 0 | derivable | a tree of 191 moves, nesting 96, 0 copies; 191 calls, 0.2 ms | 2.6 ms | a tree of 191 moves; 191 calls, 0.2 ms | 13.14 s | 13.52 s | not run |
| fan | 128 | 129 | 0 | derivable | a tree of 255 moves, nesting 128, 0 copies; 255 calls, 0.2 ms | 5.7 ms | a tree of 255 moves; 255 calls, 0.2 ms | flag: not elaborated (deterministic timeout) | flag: not elaborated (deterministic timeout) | not run |
| fan | 256 | 257 | 0 | derivable | a tree of 511 moves, nesting 256, 0 copies; 511 calls, 0.8 ms | 41.8 ms | a tree of 511 moves; 511 calls, 0.8 ms | not run | not run | not run |
| fan | 512 | 513 | 0 | derivable | a tree of 1023 moves, nesting 512, 0 copies; 1023 calls, 3.4 ms | 321.0 ms | a tree of 1023 moves; 1023 calls, 3.2 ms | not run | not run | not run |
| fan | 1024 | 1025 | 0 | derivable | a tree of 2047 moves, nesting 1024, 0 copies; 2047 calls, 12.7 ms | 2515.8 ms | a tree of 2047 moves; 2047 calls, 12.9 ms | not run | not run | not run |
| chainBad | 2 | 3 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (3 calls, 0 copies refused), 0.0 ms | no tree | no tree | 0.08 s |
| chainBad | 4 | 5 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (39 calls, 0 copies refused), 0.0 ms | no tree | no tree | 0.08 s |
| chainBad | 6 | 7 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (929 calls, 0 copies refused), 0.1 ms | no tree | no tree | 0.94 s |
| chainBad | 8 | 9 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (39039 calls, 0 copies refused), 4.3 ms | no tree | no tree | flag: not elaborated (deterministic timeout) |
| chainBad | 10 | 11 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (2752377 calls, 0 copies refused), 306.5 ms | no tree | no tree | not run |
| chainBad | 12 | 13 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | flag (> 20 s) | no tree | no tree | not run |
| chainBad | 14 | 15 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 16 | 17 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 32 | 33 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 64 | 65 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 128 | 129 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 256 | 257 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 512 | 513 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainBad | 1024 | 1025 | 0 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not run |
| chainUBad | 2 | 3 | 2 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (6 calls, 3 copies refused), 0.0 ms | no tree | no tree | not applicable |
| chainUBad | 3 | 4 | 3 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (52 calls, 34 copies refused), 0.0 ms | no tree | no tree | not applicable |
| chainUBad | 4 | 5 | 4 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (714 calls, 525 copies refused), 0.1 ms | no tree | no tree | not applicable |
| chainUBad | 5 | 6 | 5 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (15063 calls, 11828 copies refused), 1.7 ms | no tree | no tree | not applicable |
| chainUBad | 6 | 7 | 6 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (467045 calls, 382905 copies refused), 52.1 ms | no tree | no tree | not applicable |
| chainUBad | 7 | 8 | 7 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | nothing (20191955 calls, 17071278 copies refused), 2400.0 ms | no tree | no tree | not applicable |
| chainUBad | 8 | 9 | 8 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | flag (> 20 s) | no tree | no tree | not applicable |
| chainUBad | 16 | 17 | 16 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 32 | 33 | 32 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 64 | 65 | 64 | not derivable | nothing (1 calls, 0 copies refused), 0.0 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 128 | 129 | 128 | not derivable | nothing (1 calls, 0 copies refused), 0.1 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 256 | 257 | 256 | not derivable | nothing (1 calls, 0 copies refused), 0.2 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 512 | 513 | 512 | not derivable | nothing (1 calls, 0 copies refused), 0.9 ms | no tree | not run | no tree | no tree | not applicable |
| chainUBad | 1024 | 1025 | 1024 | not derivable | nothing (1 calls, 0 copies refused), 3.1 ms | no tree | not run | no tree | no tree | not applicable |

## The frontier

(As measured 2026-11-26, with `step` as it was. The rows of the compiled
check of a tree and of the fact with the tree are superseded by "The
cost of the check of a tree" below: `chain` and `fan` are now settled to
256 in the kernel.)

The smallest input not settled, for each column (in bold); and where a
column was not taken that far, the largest settled, as a lower bound.

| | chain | chainU | fan |
|---|---|---|---|
| the chained search | settled at 1024 (2049 moves, 6.9 ms). Not taken further: stopped at 1024 by the cap on sizes; a lower bound | settled at 1024 (3073 moves, 1024 copies, 8.2 ms). Not taken further; a lower bound | settled at 1024 (2047 moves, 12.7 ms). Not taken further; a lower bound |
| the compiled check of the tree | 4716.0 ms at 1024, after 606.2 ms at 512 and 77.9 ms at 256. Not taken further | 5.8 ms at 1024. Not taken further | 2515.8 ms at 1024, after 321.0 ms at 512. Not taken further |
| the search as in the figure | settled at 1024 (1164.9 ms). Not taken further | **16**: flag (> 20 s), after 17970048 calls and 2362.8 ms at 8 | settled at 1024 (12.9 ms). Not taken further |
| the fact with the tree | **96** (193 moves): flag, after 8.14 s at 64 (129 moves) | **512** (1537 moves, nesting 1025): flag, after 7.34 s at 256 (769 moves, nesting 513) | **128** (255 moves): flag, after 13.14 s at 96 (191 moves) |
| the fact with the script | **96**: flag, after 8.54 s at 64 | **512**: flag, after 8.25 s at 256 | **128**: flag, after 13.52 s at 96 |
| the kernel running the proved search | **8**: flag, after 0.06 s at 4 | not applicable | **16**: flag, after 0.36 s at 8 |

On the two families with no derivation: the chained search answers
"nothing, and no copy refused" after one call at every size to 1024
(no implication has the conclusion for its head), which is a flag. The
search as in the figure: `chainBad` **12** (flag, > 20 s; 2752377 calls
and 306.5 ms at 10); `chainUBad` **8** (flag, > 20 s; 20191955 calls and
2400.0 ms at 7). The kernel running the proved search on `chainBad`:
**8** (flag; 0.94 s at 6).

**What the flags of the facts are.** Each is "not elaborated": Lean
stopped at its own limit of 200000 heartbeats, not at the script's 60 s.
Three single runs after the table, to name the limit (16:17 and 16:19
GMT, `-M 8000`, a deadline of 90 and 100 s):

* `chain 96`, as written by the driver: "(deterministic) timeout at
  `whnf`, maximum number of heartbeats (200000) has been reached", after
  30.9 s;
* `chain 96` with `set_option maxHeartbeats 0`: "(kernel) excessive
  memory consumption detected", after 53.5 s. So with the heartbeats
  lifted the kernel's check of a tree of 193 moves over a linear zone of
  97 formulas passes 8000 MB. **The frontier of the fact for `chain` is
  the kernel's memory**: raising Lean's limit does not move it past 96
  within the cap;
* `chain 8` by the proved search (`decide +kernel`): the heartbeat
  message, and then "(kernel) excessive memory consumption detected",
  after 30.4 s.

The same question for `chainU 512` was begun and stopped at the
operator's word before it answered: not settled. For `fan 128` it was
not asked.

**Where the kernel's time goes.** The compiled checker takes 1.3 ms on
the tree of `chain 64`, and the fact 8.14 s. At each ⊗R and ⊸L the
check of the division in `Move.rule` is `permB j.lin (Δ ++ sub j.lin
Δ)`: for every formula of the zone it counts that formula in both lists,
so it is quadratic in the zone whatever the size of the part `Δ` named,
and a derivation over a zone of `n` formulas has `n` such nodes. In
`chainU` the linear zone has one formula throughout, and the fact is
settled four times further (256 against 64). A check of the division in
one pass (take each formula of `Δ` out of the zone, or fail) would cost
`|Δ|` times the zone at each node. That is a change to
`DILL/Proof.lean`, which is not this agent's file: named here, not made,
and its effect not measured.

**The tree against the script**, same derivation, in the 22 rows where
both were settled: the script is the slower in 18, the same in 2
(`chain 4`, `fan 2`), the faster in 2 (`chain 2`, `chain 32`). At the
largest size settled: 8.54 s against 8.14 s (`chain 64`), 8.25 s against
7.34 s (`chainU 256`), 13.52 s against 13.14 s (`fan 96`). The ratio is
greatest in `chainU` at small sizes (0.14 s against 0.05 s at 49 moves).

## The search, tested against itself

`dillrun fuzz <count> <size> <seed> [<budget>]` makes sequents at random
(letters `p q`, every connective, an unrestricted zone of one formula in
some), searches each in both modes at budgets 0 to 3 under a cap of
20000 calls, and where `DILL/Decide.lean` applies compares with its
decision. It prints a line for: a tree that the checker refuses; a tree
for a sequent decided not derivable; "nothing, and no copy refused" for
a sequent decided derivable, or for one where the other mode finds a
tree; and budgets that differ between the modes. Runs of 15:45 to 15:47
GMT (the driver compiled in a scratch folder from these sources):

| run | sequents | derived (chained) | nothing, no copy refused | flagged at the budget or the cap | decided by `Decide.lean` | lines printed |
|---|---|---|---|---|---|---|
| `fuzz 3000 8 1 3` | 3000 | 694 | 2168 | 138 | 1723 | 0 |
| `fuzz 20000 10 7 3` | 20000 | 4863 | 13210 | 1927 | 6878 | 1 |
| `fuzz 20000 13 11 3` | 20000 | 5031 | 11888 | 3081 | 1811 | 5 |
| `fuzz 5000 18 5 3` | 5000 | 1231 | 2666 | 1103 | 129 | 4 |

No tree was refused by the checker, no tree was found for a sequent
decided not derivable, and neither mode missed a sequent that the
decision or the other mode derives. All 10 lines are of one kind: **the
chained search needs a larger budget than the search as in the figure**,
by one in nine of them (for instance `p ⊸ q ; p, !⊤, q ⊸ p ⟹ q & p`:
chained 2, as in the figure 1) and by two in one (`!!(q ⊸ p) ; (!q & 1)
⊸ q, !!q & p ⟹ p & ((q ⊗ p) ⊕ p)`: chained 5, as in the figure 3, seen
when the last batch was rerun with budgets to 6; at budgets to 3 its
line read "not found to the budget, where figure finds a tree").
Chaining puts in one branch two copies that a derivation of the figure
can put in two. So "the least budget" in the corpus table is the
chained search's; on the corpus the two modes agree.

## The cost of the check of a tree: its cause, and the repair (2026-11-27)

By the owner session, on the directing session's task (method note 23).
The family table above, and "The frontier" below, are of `step` as it
was until this date: the fact with the tree of `chain 64` in 8.14 s,
`chain 96` not settled within 8 GB. `step` now runs `Move.ruleF`
(statement S19), proved equal to `Move.rule`. Each run of Lean below:
one at a time, `-M 4000`, a deadline on the process group.

**The first cause: the division counted.** At ⊗R, ⊸L and cut the rule
checked the part named by `permB l (Δ ++ sub l Δ)`, which counts every
formula of the zone in both lists: for a zone of `m` formulas, `4m²`
comparisons of formulas, whatever `Δ` is. Measured before the change:

| `chain n` | the kernel, the fact | peak | one `permB` at the zone of the root, alone |
|---|---|---|---|
| 16 | 0.22 s | 1 398 MB | under 0.1 s |
| 32 | 1.10 s | 1 793 MB | 0.17 s |
| 48 | 3.40 s | 2 624 MB | 0.39 s |
| 64 | 8.14 s (2026-11-26) | | |

One test is the square of the zone (2.4 times from 33 formulas to 49),
and there is one at each of the `n` nodes: the cube. The smallest input
that shows it is `chain 16` to `chain 32`: twice the formulas, five
times the time.

**The repair of it, and what it left.** `subAll l Δ`: each formula of
`Δ` in turn is in what is left of `l`; proved to be the same test
(`subAll_eq_permB`). With it alone:

| `chain n` | the kernel | peak |
|---|---|---|
| 32 | 0.23 s | 1 411 MB |
| 64 | 0.95 s | 1 781 MB |
| 96 | 2.29 s | 2 362 MB |
| 128 | 4.04 s | 3 191 MB |

Still the square of `n`. Not the order in which the part is named (the
search names it in the reverse of the zone's order; named in the zone's
order, `chain 64` took 1.06 s against 0.94 s, and `chain 128` 4.37 s
against 4.04 s).

**The second cause: a formula looked for with the derived equality.**
At each node the rule looks for its principal formula in the zone and
takes it out (`decide (X ∈ l)`, `l.erase X`). The search takes the last
implication of the chain first, so the zone is gone through to its end
at every node, and each formula met is compared with one that it is not
equal to. That comparison, by the derived `DecidableEq`, costs the
kernel 180 µs (a zone of 128 searched 32 times for a late formula:
0.65 s; with an equality written by hand 0.36 s; with the numbers of
the two formulas compared first 0.15 s). The kernel keeps the number of
a formula it has met, so the last is a comparison of two numbers.

**The repair of that.** `eqH`, `memH`, `eraseH`, `subH`, `subAllH`
(`DILL/Perm.lean`), each proved equal to what it replaces, and
`Move.ruleF` built from them.

### Before and after

`python3 -I Corpus/measure_checks.py trees`. `chain n` is the family
the cost was found on; `fan n` (`· ; aₙ, …, a₁ ⟹ a₁ ⊗ (a₂ ⊗ …)`) is the
second family, made against what could make the first fast: each ⊗R
names one formula, and it is the last of the zone. The times of the
kernel's column are of the whole file, the tree elaborated as well as
checked. Before, from the family table above (2026-11-26, the same
machine): the fact with the tree of `chain 64` 8.14 s and of `chain 96`
not elaborated; of `fan 64` 4.66 s and of `fan 96` 13.14 s; the
compiled check 1.3 ms at `chain 64`, 9.7 ms at `chain 128`, 0.8 ms at
`fan 64`, 2.6 ms at `fan 96`.

Machine: arm64, macOS-15.8.3-arm64-arm-64bit; Lean v4.31.0.  Date: 2026-11-27 11:03 GMT.  Each run of Lean: `-M 4000`, a deadline of 300 s on the process group, one at a time.  Loading the imports: 1.08 s, taken off the times; the peaks of memory include it (about 1300 MB).

| family | n | formulas in the sequent | the tree: moves | the search | the compiled check of the tree | the fact with the tree, elaborated: the kernel checks the tree |
|---|---|---|---|---|---|---|
| chain | 8 | 9 | 17 | 0.0 ms | 0.0 ms | 0.05 s, 1289 MB |
| chain | 16 | 17 | 33 | 0.0 ms | 0.0 ms | 0.08 s, 1299 MB |
| chain | 32 | 33 | 65 | 0.0 ms | 0.0 ms | 0.26 s, 1332 MB |
| chain | 64 | 65 | 129 | 0.1 ms | 0.1 ms | 0.92 s, 1459 MB |
| chain | 96 | 97 | 193 | 0.1 ms | 0.2 ms | 2.15 s, 1659 MB |
| chain | 128 | 129 | 257 | 0.2 ms | 0.3 ms | 3.95 s, 1907 MB |
| chain | 192 | 193 | 385 | 0.3 ms | 0.7 ms | 9.02 s, 2648 MB |
| chain | 256 | 257 | 513 | 0.5 ms | 1.2 ms | 16.35 s, 3612 MB |
| fan | 8 | 9 | 15 | 0.0 ms | 0.0 ms | 0.02 s, 1285 MB |
| fan | 16 | 17 | 31 | 0.0 ms | 0.0 ms | 0.04 s, 1295 MB |
| fan | 32 | 33 | 63 | 0.0 ms | 0.0 ms | 0.13 s, 1318 MB |
| fan | 64 | 65 | 127 | 0.2 ms | 0.1 ms | 0.48 s, 1400 MB |
| fan | 96 | 97 | 191 | 0.2 ms | 0.1 ms | 1.17 s, 1516 MB |
| fan | 128 | 129 | 255 | 0.3 ms | 0.2 ms | 2.10 s, 1630 MB |
| fan | 192 | 193 | 383 | 0.5 ms | 0.5 ms | 4.82 s, 1975 MB |
| fan | 256 | 257 | 511 | 0.9 ms | 0.8 ms | 8.57 s, 2447 MB |

What the table says:

* **`chain 64`: 8.14 s to 0.9 s. `chain 96`, not settled within 8 GB,
  in 2.2 s; `chain 256` in 16 s within 3.6 GB. `fan 64`: 4.66 s to
  0.5 s; `fan 96`: 13.14 s to 1.2 s; `fan 256` in 8.6 s.** The frontier
  is no longer between 64 and 96: both families are settled to 256, the
  largest size tried.
* **The growth is the square of `n` on both families** (4.1 to 4.4
  times for twice the size from 64 on), where it was the cube. On
  `chain` the tree is itself the square of `n` ("Not repaired", below).
  On `fan` the tree is of the size of `n`, and the square is the zone
  gone through at each node for a formula at its end.
* **Compiled, the check is 13 to 30 times faster than it was**: 0.1 ms
  at `chain 64` (1.3 ms), 0.3 ms at `chain 128` (9.7 ms), 0.1 ms at
  `fan 96` (2.6 ms). One form on the way was slower compiled than the
  check it replaced: with the numbers of the formulas compared first in
  compiled code too, the compiled check of `chain 64` took 2.6 ms, since
  compiled code keeps no number and computes both at every comparison.
  `eqH` is therefore the plain equality for compiled code
  (`@[csimp] eqH_csimp`, `DILL/Perm.lean`), and the kernel reduces the
  definition. The table is of that form; the kernel's column is the
  same either way (a run before it: `chain 256` 14.8 s, `fan 256`
  7.2 s).
* Further, compiled only (`dillrun run focus <family> <n> 0`): the check
  of the tree of `chain 256`, `512`, `1024` takes 1.2 ms, 4.9 ms,
  19.3 ms, where "The frontier" above has 77.9 ms, 606.2 ms, 4716.0 ms;
  of `fan 1024`, 14.4 ms (2515.8 ms). Four times for twice the size, where it was
  eight.
* The kernel is still four orders of magnitude from compiled code
  (0.3 ms and 3.95 s at `chain 128`).

### Not repaired

* The tree of `chain n` is itself the square of `n`: each ⊸L names the
  part of the zone that goes to its first premise, and the search takes
  the last implication first, so the part named is the rest of the
  zone (1.16 MB of source at 256, and 7.6 s for Lean to elaborate it
  before the kernel sees it). The check is now a pass over what it is
  given. A search that took the first implication first would write a
  tree of the size of `n`; the search was not changed.
* The equality of two formulas that are equal is still the derived one.

## The command on the corpus

Added 2026-11-26, after the campaign closed, by the owner session
(method note 22). `dillrun prove` on each of the 56 entries, by
`python3 -I Corpus/prove_corpus.py --elaborate` (three runs, as the
printed file changed, with the same counts; the last ended at 22:34 GMT,
after the build of 116 jobs, and is the one below).
Each entry is given three times: in the source's notation, as Lean
source, with the signs of a keyboard.

| | |
|---|---|
| `derivable` (exit code 0) | 39, each recorded derivable |
| `not derivable` (1), with a saturated set | 13, each recorded not derivable |
| `flag` (3) | 4: `loop`, `loopU`, `pump`, `bangPlusNo`, each recorded not derivable |
| against the recorded status | 0 |
| the three texts of an entry answered differently | 0 |
| printed files elaborated (`lake env lean -M 8000`, the kernel checking each certificate) | 56 of 56; none needed the options that lift Lean's limits |
| a text that is not a sequent (`p, => q`; `p -o`) | each refused: exit code 2, the mark under character 4 and 5, nothing on the standard output |
| the deadline (`--deadline=1`, 24 equal atoms against 25) | `flag`, exit code 3, after 1.0 s |
| altered: the tree of `copyInit` replaced by `.mk .init []` | refused by Lean (`could not synthesize default value for parameter 'h'`) |
| altered: the set of `contract` without its first member | refused by Lean ("Tactic `decide` proved that the proposition … is false", at `checked`) |

A flag agrees with either status, so the script fails only where an
answer is against the status. The four flags are the corpus's sequents
with no derivation and a formula under `!` to the left (or a formula
already in the unrestricted zone): no saturated set exists for them
(`measurements-sat.md`). A search that came to flag more would pass the
script: the list above is the record to compare with.

**Where Lean's own limits stop a printed file**, and so what "a large
answer" is. Each file elaborated as printed and again with the two
`set_option` lines taken out (`-M 8000`, a deadline of 150 s on the
process group; single runs, 22:21 to 22:28 GMT, with another session's
builds running).

| the sequent | the certificate | as printed | without the options |
|---|---|---|---|
| `a4, a4 ⊸ a5, …, ⟹ a44` (a chain of 40) | a tree of 81 moves | 2.7 s | 2.7 s |
| `!p ⟹ p ⊗ … ⊗ p`, 60 | 180 moves, nested 61 | 1.4 s | 1.3 s |
| the same, 100 | 300 moves, nested 101 | 1.7 s | 1.8 s |
| the same, 130 | 390 moves, nested 131 | not run | refused: "maximum recursion depth has been reached" |
| the same, 200 | 600 moves, nested 201 | 4.0 s | refused, the same |
| the same, 400 | 1200 moves, nested 401 | 13.1 s | refused, the same |
| the same, 800 | 2400 moves, nested 801 | 61.9 s | refused, the same |
| a chain of 4 with the wrong conclusion | a set of 76 sequents | 4.7 s | 4.8 s |
| a chain of 5 with the wrong conclusion | a set of 200 sequents | 41.3 s | 40.3 s |

So the limit that is met first is the depth of recursion, between a
tree nested 101 deep and one nested 131 deep; the command writes both
options from a nesting of 41, a tree of 151 moves, a set of 61 sequents
or of 1500 signs, or a sequent of 151 signs, which leaves a margin of
more than two. No limit on heartbeats was met at these sizes; the option is written
all the same, as the skill asks. The 41 s for a set of 200 sequents was two
kernel checks of the one set, one for each of the two facts. The file
now states the check once (`checked`) and both facts from it: 20.0 s.
How the check is stated matters to the kernel:

| `checked`, for the set of 200 sequents | the file elaborated |
|---|---|
| no such theorem: a `verdict` for each fact | 41.3 s (39.3 s in a second run) |
| `refutedBy saturated sequent = true := by decide +kernel` | refused after 83.5 s (81.3 s in a second run): "(kernel) excessive memory consumption detected", at the cap of 8000 MB |
| `noCFBySet.check sequent saturated = true := by decide +kernel` | 20.0 s |

The second and the third state the same Boolean (`noCFBySet.check j D`
is `refutedBy D j` by definition). Why the kernel's run differs was not
looked for. The printed file has the third.

**The search for a set has no bound of its own.** On `p, …, p ⟹ p ⊗ …
⊗ p` with `n` atoms against `n + 1` the command (first line only) took
0.06 s at 12, 0.13 s at 14, 0.54 s at 16, 2.5 s at 18, 11.3 s at 20, and
at 24 did not end in the 100 s it was given. The search for a derivation
makes 41 calls on the sequent at 20 and 81 at 40, so the time is the
search for a set (`Refute.search`); what in it grows was not looked
for. Hence the deadline of the command (10 s where none is given).
Not repaired: the search itself.

## What went wrong in the measuring

* **The deadline of `Corpus/measure.py` killed `lake` and not Lean.**
  `lake env lean` starts Lean as a child; until 16:25 GMT the script's
  deadline (and the `perl -e 'alarm …'` used for single runs) ended
  `lake` alone, and the Lean under it ran on with nothing to stop it.
  In the first measuring run (15:44 GMT, no cap on memory) the two facts
  of `chain 128` were cut at 60 s in this way. With what the runs after
  the restart show (the kernel past 8000 MB on `chain 96`), those two
  processes, and the proved search on `chain 8` in the run started at
  15:50, were probably among the causes of the restart of 15:51. The
  script now starts each run in a process group of its own and kills
  the group; this was tested with a shell command (the child is gone
  after the cut), and **not with Lean**: no measuring run has been made
  since the change.
* The single runs of 16:19 were started although the look at the
  machine showed one `lean` and one `lake` of another project running:
  against the rule of one builder at a time. At 16:22 the machine showed
  19 GB of swap in use.
* The figures from before the restart (the corpus table, the profile,
  the facts file, the counts for `Source.lean`, the random tests) were
  made while other builds ran; the family table is from the run after
  it, on a quiet machine.
