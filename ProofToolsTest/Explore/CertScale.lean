/-
The cost, in the kernel, of the check of a tree of moves against the check
of its script: the same derivation in its two writings
(`ProofTools.Explore.Cert`, `ProofTools.Explore.Certify`), on the tests'
two systems.  Each theorem is one kernel check.

* `swap`, `distr`: the two derivations of the example calculus that the
  other tests use (5 and 11 moves).
* `chain n` (`Count.lean`): `n + 1` moves, one under another; a step costs
  next to nothing, so this is the cost of the two checkers themselves.
* `conj k`: the conjunction of `2 ^ k` atoms as a balanced tree, derived
  from those atoms as hypotheses: `2 ^ (k + 1) - 1` moves, and at each leaf
  `step` looks the atom up among `2 ^ k` hypotheses, so here the steps
  cost, the more the larger `k`.

Measured 2026-11-22, Lean v4.31.0, Apple silicon, `lean -DElab.async=false
-Dprofiler=true -Dprofiler.threshold=0` ("type checking" is the kernel
check of the theorem), each the least of three runs:

| derivation | moves | the tree, `Cert.check` | the script, `derives` | script / tree |
|---|---|---|---|---|
| `swap` | 5 | 1.4 ms | 4.9 ms | 3.4 |
| `distr` | 11 | 2.3 ms | 10.0 ms | 4.3 |
| `chain 300` | 301 | 44 ms | 264 ms | 6.1 |
| `chain 1000` | 1,001 | 157 ms | 970 ms | 6.2 |
| `conj 4` | 31 | 10 ms | 37 ms | 3.5 |
| `conj 6` | 127 | 140 ms | 269 ms | 1.9 |
| `conj 7` | 255 | 591 ms | 917 ms | 1.6 |

(`conj 8`, 511 moves, is not in the file, to keep its build short: 2.66 s
against 3.53 s, a factor of 1.3, by `Lean.Kernel.whnf` timed in a scratch
file.)

So here the tree is checked 1.3 to 6.2 times faster than the script.  The gain is the checker's own
work: the script's check keeps a position and builds the attempt as it
goes, the tree's check builds nothing.  It is largest where a step costs
least, and falls towards 1 as the steps come to dominate.

**What the rose tree costs.**  A tree of moves is a rose tree of the library
with nothing on its edges, so each child is a pair `((), c)`, and the
recursion of `Cert.check` has a layer for the pair.  A tree type with no
edges (`node (m) (cs : List _)`), checked by the same recursion, was tried
beside it in a scratch file and not kept: `chain 1000` 96 ms against 157 ms
(a factor of 1.6, where a step costs next to nothing), `conj 4` 9.3 against
10.2 ms, `conj 6` 137 against 142 ms (a factor of 1.04, where the steps
cost).
-/
import ProofToolsTest.Explore.Cert
import ProofToolsTest.Explore.Count
import ProofToolsTest.Explore.Run

namespace ProofToolsTest.Explore.CertScale

open ProofTools ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.CertTest
open ProofToolsTest.Explore.MapOutTest (p q)
open Count

/-! ## The example calculus: two small derivations -/

theorem swap_tree : Cert.check swapSeq swapCert = true := by decide +kernel
theorem swap_script : derives IPC swapSeq swapScript = true := by decide +kernel

/-- The tree of moves of `distr`, `⊢ (p ∧ (q ∨ r)) → ((p ∧ q) ∨ (p ∧ r))`. -/
def distrCert : Cert IPC :=
  .mk .impR [.mk (.andL p (q ⋎ RunTest.r)) [.mk (.orL q RunTest.r)
    [.mk .orR1 [.mk .andR [.mk .ax [], .mk .ax []]], .mk .orR2 [.mk .andR [.mk .ax [], .mk .ax []]]]]]

-- it is the tree of the derivation its script builds
#guard (Der.ofScript RunTest.distr RunTest.distrScript (by decide +kernel)).cert == distrCert

theorem distr_tree : Cert.check RunTest.distr distrCert = true := by decide +kernel
theorem distr_script : derives IPC RunTest.distr RunTest.distrScript = true := by decide +kernel

/-! ## Deep: a chain -/

/-- The tree of the chain from `n`. -/
def chainCert : Nat → Cert Count
  | 0 => .node .done []
  | n + 1 => .node (.split 1) [((), chainCert n)]

#guard Cert.check (S := Count) 2000 (chainCert 2000)
#guard !Cert.check (S := Count) 2001 (chainCert 2000)

theorem chain300_tree : Cert.check (S := Count) 300 (chainCert 300) = true := by decide +kernel
theorem chain300_script : derives Count 300 (chain 300) = true := by decide +kernel

set_option maxRecDepth 4000 in
theorem chain1000_tree : Cert.check (S := Count) 1000 (chainCert 1000) = true := by decide +kernel
set_option maxRecDepth 4000 in
theorem chain1000_script : derives Count 1000 (chain 1000) = true := by decide +kernel

/-! ## Wide: a balanced conjunction -/

/-- The conjunction of the atoms `lo`, …, `lo + 2 ^ k - 1`, balanced. -/
def conj : Nat → Nat → Form
  | 0, lo => .atom lo
  | k + 1, lo => .and (conj k lo) (conj k (lo + 2 ^ k))

/-- The atoms `0`, …, `2 ^ k - 1`, as hypotheses. -/
def atoms (k : Nat) : List Form := (List.range (2 ^ k)).map Form.atom

/-- The tree of moves: `andR` down to the atoms, then `ax`. -/
def conjCert : Nat → Cert IPC
  | 0 => .node .ax []
  | k + 1 => .node .andR [((), conjCert k), ((), conjCert k)]

/-- Its script: the leftmost goal first. -/
def conjScript : Nat → Script IPC
  | 0 => [⟨0, .ax⟩]
  | k + 1 => ⟨0, .andR⟩ :: (conjScript k ++ conjScript k)

#guard Cert.check (atoms 6 ⊢ conj 6 0) (conjCert 6)
#guard derives IPC (atoms 6 ⊢ conj 6 0) (conjScript 6)
#guard !Cert.check (atoms 6 ⊢ conj 6 1) (conjCert 6)

theorem conj4_tree : Cert.check (atoms 4 ⊢ conj 4 0) (conjCert 4) = true := by decide +kernel
theorem conj4_script : derives IPC (atoms 4 ⊢ conj 4 0) (conjScript 4) = true := by decide +kernel

theorem conj6_tree : Cert.check (atoms 6 ⊢ conj 6 0) (conjCert 6) = true := by decide +kernel
theorem conj6_script : derives IPC (atoms 6 ⊢ conj 6 0) (conjScript 6) = true := by decide +kernel

theorem conj7_tree : Cert.check (atoms 7 ⊢ conj 7 0) (conjCert 7) = true := by decide +kernel
theorem conj7_script : derives IPC (atoms 7 ⊢ conj 7 0) (conjScript 7) = true := by decide +kernel

end ProofToolsTest.Explore.CertScale
