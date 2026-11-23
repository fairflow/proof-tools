/-
# `ProofTools.Explore.Certify`: the checkers, as certifiers of `LeanCertify`

A derivation has two writings as a certificate, each with its checker, and
with the soundness of the moves for a family `T` each is a
`Certify.Certifier` for `T`:

| certificate | checker | certifier | keeps |
|---|---|---|---|
| a script | `derives`: run it from the open goal; no line failed, no goal is left | `certifier` | the order of the work; it can be continued and composed |
| a tree of moves (`ProofTools.Explore.Cert`) | `Cert.check`: `step` at the root, then each child at its premise | `Cert.certifier` | the shape; it builds nothing as it checks |

`T` is into any sort: with a proposition a certifier proves it; with a type
of derivations it builds the derivation, as `Der.mapOut` of the derivation
the certificate is (`Der.ofScript`, `Der.ofCert`).

    derives S j ls = true → S.Sound D → D j                        (derives_sound)
    derives S j d.script = true          for d : Der S j           (derives_script)
    Cert.check j d.cert = true           for d : Der S j           (Att.check_cert)

The last two give every derivation a certificate of each kind: scripts, and
trees of moves, are complete for derivations.

**The refutation side is optional**, and comes in levels; an instance stops
where its mathematics stops.

| level | the instance has | it gets |
|---|---|---|
| 1 | moves and their soundness | `certifier`, `Cert.certifier`: scripts and trees checked |
| 2 | also a certifier against what holds: a notion of model with a sound check | `engine`; its producer may answer `flag`, and nothing says a model is ever found |
| 3 | also a theorem that one side always answers | `Certify.Engine.Complete`, or the instance's own statement |

A certifier against what holds is a `Certify.Certifier S.Judg Model (fun j =>
D j → False)` of `LeanCertify`, as it stands; bundled with its type of
models, a name and a producer it is a `Certify.Disprover`.  The explorer has
no structure of its own for it.  The library says nothing about where a
model comes from: `produce` is the instance's, and is not trusted.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import LeanCertify.Certifier
import ProofTools.Explore.Run
import ProofTools.Explore.Cert

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

/-- **Level 1: trees of moves, checked.**  The certifier of a proof system
whose moves are sound for `T`, into any sort, its certificate a tree of
moves: with `T` a proposition, a tree that `Cert.check` accepts proves it;
with `T` a type of derivations, it builds the derivation. -/
def Cert.certifier (hS : S.SoundT T) : Certify.Certifier S.Judg (Cert S) T where
  check := Cert.check
  sound j c h := Der.mapOut hS (Der.ofCert j c h)

/-- **Level 2: both sides, as one engine.**  The yes side is the certifier
of scripts.  The no side is a certifier against `D`: a notion of model with
a sound check (of a `Certify.Disprover`, its field `certifier`).  The
producer is not trusted; it may answer `flag`. -/
def engine (hS : S.Sound D) {Model : Type}
    (no : Certify.Certifier S.Judg Model (fun j => D j → False))
    (produce : S.Judg → Nat → Certify.Verdict (Script S) Model) :
    Certify.Engine S.Judg (Script S) Model D where
  yes := certifier hS.soundT
  no := no
  produce := produce

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
