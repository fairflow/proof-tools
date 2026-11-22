/-
# `ProofTools.Explore.Certify`: both checkers, as certifiers of `LeanCertify`

The first checker is `derives`: run the script from the open goal, and ask
that no line failed and no goal is left.  With the soundness of the moves
for a family `T` it is a `Certify.Certifier` whose certificate is a script
(`certifier`).  `T` is into any sort: with a proposition the certifier
proves it; with a type of derivations it builds the derivation, as
`Der.mapOut` of the derivation the script builds (`Der.ofScript`).

    derives S j ls = true → S.Sound D → D j                        (derives_sound)
    derives S j d.script = true          for d : Der S j           (derives_script)

The second gives every derivation a certificate: scripts are complete for
derivations.

**The refutation side is optional**, and comes in levels; an instance stops
where its mathematics stops.

| level | the instance has | it gets |
|---|---|---|
| 1 | moves and their soundness | `certifier`: scripts checked |
| 2 | also a notion of model with a sound check (`Evaluator`) | `engine`; its producer may answer `flag`, and nothing says a model is ever found |
| 3 | also a theorem that one side always answers | `Certify.Engine.Complete`, or the instance's own statement |

The library says nothing about where a model comes from: `produce` is the
instance's, and is not trusted.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import LeanCertify.Certifier
import ProofTools.Explore.Run

namespace ProofTools.Explore

universe u

variable {S : ProofSystem} {D : S.Judg → Prop} {T : S.Judg → Sort u}

/-- **The first checker**: the script runs without a failing line and
leaves no goal. -/
def derives (S : ProofSystem) (j : S.Judg) (ls : Script S) : Bool :=
  let r := run S j ls
  r.failed.isNone && r.att.goals.isEmpty

/-- The derivation a script builds, if `derives` accepts it. -/
def Der.ofScript (j : S.Judg) (ls : Script S) (h : derives S j ls = true) : Der S j :=
  (run S j ls).att.toDer (by
    simp only [derives, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2)

/-- **A script that `derives` accepts shows that its judgment holds.** -/
theorem derives_sound (hS : S.Sound D) {j : S.Judg} {ls : Script S}
    (h : derives S j ls = true) : D j :=
  Der.sound hS (Der.ofScript j ls h)

/-- **Every derivation has a script that `derives` accepts**: its own. -/
theorem derives_script {j : S.Judg} (d : Der S j) : derives S j (Att.script d) = true := by
  simp [derives, run_script]

/-- **Level 1: scripts, checked.**  The certifier of a proof system whose
moves are sound for `T`, into any sort.  With `T` a proposition, a script
that `derives` accepts proves it; with `T` a type of derivations, it builds
the derivation.  (From `hS : S.Sound D`, by membership: `certifier
hS.soundT`.) -/
def certifier (hS : S.SoundT T) : Certify.Certifier S.Judg (Script S) T where
  check := derives S
  sound j ls h := Der.mapOut hS (Der.ofScript j ls h)

/-- **A notion of model with a sound check**: what refutes a judgment shows
that it does not hold. -/
structure Evaluator (S : ProofSystem) (D : S.Judg → Prop) where
  /-- The models. -/
  Model : Type
  /-- Does the model refute the judgment? -/
  refutes : Model → S.Judg → Bool
  /-- What is refuted does not hold. -/
  sound : ∀ M j, refutes M j = true → D j → False

/-- The second checker, as a certifier whose certificate is a model. -/
def Evaluator.certifier (E : Evaluator S D) :
    Certify.Certifier S.Judg E.Model (fun j => D j → False) where
  check j M := E.refutes M j
  sound j M h := E.sound M j h

/-- **Level 2: both checkers, as one engine.**  The producer is not
trusted; it may answer `flag`. -/
def engine (hS : S.Sound D) (E : Evaluator S D)
    (produce : S.Judg → Nat → Certify.Verdict (Script S) E.Model) :
    Certify.Engine S.Judg (Script S) E.Model D where
  yes := certifier hS.soundT
  no := E.certifier
  produce := produce

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
