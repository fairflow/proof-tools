/-
What runs, on the "yes" side: the certifiers of derivations of DILL, and
the producer of the Run stage with its answer checked.

The pattern is that of the skill `lean-certify`: the theory says what
holds; a producer that is not trusted computes a certificate; a checker
proved sound certifies it in the kernel.

* **What holds**: `Fam true j`, the family of derivations with the two
  cuts (the plan's choice).  It is a type: a verdict is a derivation.
* **The certificate**: a tree of moves (`treeCert`, the certificate of
  record), or a script (`scriptCert`).  The checkers are the library's
  `Cert.check` and `derives`, which run `step`; their soundness is S1
  (`step_sound`).  The moves `tensorR A B Δ` and `lolliL A B Δ` name the
  part of the linear zone that goes to the first premise: the checker
  sees every division.
* **The producer**: the search of `DILL/Lazy.lean`, without cut, with a
  budget on the uses of copy along a branch.  What it returns is checked
  before it is handed on.  It answers `pass` or `flag`, never `fail`:
  with `!` derivability is not decidable, and a search that found
  nothing at a budget has shown nothing.  The side against a derivation
  is `DILL/SatRun.lean`; the two are joined in an engine elsewhere.

Theory file: it ends with its bound on axioms.
-/
import DILL.Proof
import DILL.Lazy
import LeanCertify

namespace DILL

open ProofTools ProofTools.Explore

/-! ## The certifiers -/

/-- **Trees of moves, checked**: a tree that `Cert.check` accepts for `j`
gives a derivation of `j`. -/
def treeCert : Certify.Certifier Seq (Cert S) (Fam true) := Cert.certifier step_sound

/-- **Scripts, checked**: a script that runs to the end from `j` gives a
derivation of `j`. -/
def scriptCert : Certify.Certifier Seq (Script S) (Fam true) := certifier step_sound

#certify_structural DILL.treeCert
#certify_statement DILL.treeCert
#certify_structural DILL.scriptCert
#certify_statement DILL.scriptCert

namespace Run

/-! ## The producer -/

/-- **A tree of moves from the search, checked**: at the budget `n` of
copies along a branch.  `none` is "nothing found at this budget", and is
never "no derivation". -/
def proveLazy (j : Seq) (n : Nat) : Option (Cert S) :=
  match Lazy.prove j n with
  | some c => if Cert.check j c then some c else none
  | none => none

/-- The same with the search run as `cfg` says (the left rules chained or
not, a cap on its calls), and what the run did.  The last component says
whether the search returned a tree that the checker refused: a defect of
the search, never an answer. -/
def proveLazyWith (cfg : Lazy.Cfg) (j : Seq) (n : Nat) : Option (Cert S) × Lazy.Stats × Bool :=
  match Lazy.proveWith cfg j n with
  | (some c, st) => if Cert.check j c then (some c, st, false) else (none, st, true)
  | (none, st) => (none, st, false)

/-- **The producer of the "yes" side**: `pass` with the script of the
derivation that the checked tree is; `flag` where the search found
nothing at the budget `n`, or returned a tree that does not check.
Never `fail`: there is no certificate against a derivation here. -/
def produce (j : Seq) (n : Nat) : Certify.Verdict (Script S) Unit :=
  match Lazy.prove j n with
  | some c => if h : Cert.check j c = true then .pass (Der.ofCert j c h).script else .flag
  | none => .flag

/-- The producer whose certificate is the tree itself. -/
def produceTree (j : Seq) (n : Nat) : Certify.Verdict (Cert S) Unit :=
  match proveLazy j n with
  | some c => .pass c
  | none => .flag

#certify_domain DILL.Run.produce
#certify_domain DILL.Run.produceTree

end Run

end DILL

#axioms_within_file [propext, Quot.sound]
