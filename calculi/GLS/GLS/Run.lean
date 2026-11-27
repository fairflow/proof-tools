/-
What runs: the certifiers of GLS, the producer, and that one of the two
sides always answers.

The pattern is that of the skill `lean-certify`: the theory says what
holds; a producer that is not trusted computes a certificate; a checker
proved sound certifies it in the kernel.

* **For a derivation**: the certificate is a tree of moves; the checker
  replays it with each side of a sequent kept by counts
  (`Seq.countCheck`, `GLS/Counts.lean`), which is the library's
  `Cert.check`, running `step`, by S27 (`countCheck_eq`); the soundness of
  the moves is S1 (`step_sound`).  `treeCert.verdict s c : Fam s`.
* **Against validity, and against derivability**: the certificate is a
  finite tree; the checker computes that the sequent is false at its
  root, one formula at a time over all the worlds (`Seq.refutedT`,
  `GLS/Table.lean`), which is `Seq.refutedAt` by S26 (`Seq.refutedT_eq`).
  `noValid.verdict s t : Valid s → False`.

Each check is the algorithm one would run, and the kernel and compiled
code run the same one.  The definitions they are proved equal to are
exponential where a formula has many nested boxes, run as they are
written: `Form.holds` asks again for what it has computed, and
`Cert.check` writes out sequents that GLR doubles
(`campaign/measurements.md`, "The two checks").
* **The producer** is the search of `GLS/Search.lean`, compiled.  It is
  proved to end and to be right, but nothing here rests on that: what it
  returns is checked.

Theory file: it ends with its bound on axioms.
-/
import GLS.Completeness
import GLS.Proof
import GLS.Table
import GLS.Counts
import LeanCertify

namespace GLS

open ProofTools ProofTools.Explore

/-! ## The certifiers -/

/-- **Trees of moves, checked**: a tree that the replay by counts accepts
for `s` gives a derivation of `s` in GLS.  The replay by counts is
`Cert.check` (S27), and a tree that `Cert.check` accepts is a derivation
of the proof system, mapped out by the soundness of the moves. -/
def treeCert : Certify.Certifier Seq (Cert S) Fam where
  check s c := s.countCheck c
  sound s c h := (Cert.certifier step_sound).sound s c ((countCheck_eq s c).symm.trans h)

/-- The check of `treeCert` is the library's check of a tree of moves. -/
theorem treeCert_check (s : Seq) (c : Cert S) : treeCert.check s c = Cert.check s c :=
  countCheck_eq s c

/-- **Scripts, checked**: a script that runs to the end from `s` gives a
derivation of `s` in GLS. -/
def scriptCert : Certify.Certifier Seq (Script S) Fam := certifier step_sound

/-- **Finite trees, checked against validity**: if `s` is computed false
at the root of `t`, then `s` is not valid. -/
def noValid : Certify.Certifier Seq Tree (fun s => Valid s → False) where
  check s t := s.refutedT t
  sound s t h hv := not_satSeq_of_refutedAt ((Seq.refutedT_eq s t).symm.trans h)
    (hv treeModel treeModel_GL treeModel_twoValued t)

/-- The check of `noValid`, and of `noDerivable`, is the definition
`Seq.refutedAt`. -/
theorem noValid_check (s : Seq) (t : Tree) : noValid.check s t = s.refutedAt t :=
  Seq.refutedT_eq s t

/-- The same against derivability: by soundness, what is not valid has no
derivation. -/
def noDerivable : Certify.Certifier Seq Tree (fun s => Derivable s → False) where
  check s t := s.refutedT t
  sound s t h := fun ⟨d⟩ => noValid.sound s t h (soundness s d)

#certify_structural GLS.treeCert
#certify_statement GLS.treeCert
#certify_structural GLS.noValid
#certify_statement GLS.noValid
#certify_structural GLS.noDerivable
#certify_statement GLS.noDerivable

/-! ## From a derivation to its tree of moves -/

/-- The tree of moves of a derivation: at each rule instance, the move
with what the constructor carries. -/
def Fam.toCert : {s : Seq} → Fam s → Cert S
  | _, .idP p _ _ => .mk (.idP p) []
  | _, .botL _ => .mk .botL []
  | _, .impR A B _ d => .mk (.impR A B) [d.toCert]
  | _, .impL A B _ d₁ d₂ => .mk (.impL A B) [d₁.toCert, d₂.toCert]
  | _, .glr A _ d => .mk (.glr A) [d.toCert]

/-- The tree of moves of a derivation checks. -/
theorem Fam.check_toCert {s : Seq} (d : Fam s) : Cert.check s d.toCert = true := by
  induction d with
  | @idP Γ Δ p hΓ hΔ =>
    have h : S.step (.idP p) (Γ ⇒ Δ) = .ok [] := step_of (by simp [Move.rule, hΓ, hΔ])
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    rfl
  | @botL Γ Δ hb =>
    have h : S.step .botL (Γ ⇒ Δ) = .ok [] := step_of (by simp [Move.rule, hb])
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    rfl
  | @impR Γ Δ A B hm _ ih =>
    have h : S.step (.impR A B) (Γ ⇒ Δ) = .ok [A :: Γ ⇒ B :: Δ.erase (A ⟶ B)] :=
      step_of (by simp [Move.rule, hm])
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih]
  | @impL Γ Δ A B hm _ _ ih₁ ih₂ =>
    have h : S.step (.impL A B) (Γ ⇒ Δ) =
        .ok [Γ.erase (A ⟶ B) ⇒ A :: Δ, B :: Γ.erase (A ⟶ B) ⇒ Δ] :=
      step_of (by simp [Move.rule, hm])
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih₁, ih₂]
  | @glr Γ Δ A hm _ ih =>
    have h : S.step (.glr A) (Γ ⇒ Δ) = .ok [xbox Γ ++ [□A] ⇒ [A]] :=
      step_of (by simp [Move.rule, hm])
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih]

/-! ## The producers -/

/-- A tree of moves for `s`, where the search finds a derivation. -/
def prove? (s : Seq) : Option (Cert S) :=
  match proofOrRef s with
  | .inl d => some d.toCert
  | .inr _ => none

/-- A tree that refutes `s`, where the search finds one. -/
def refute? (s : Seq) : Option Tree :=
  match proofOrRef s with
  | .inl _ => none
  | .inr r => some r.1

/-- **The producer**: the search, with what it returns checked before it
is handed on.  A script for a derivation, a tree against one, or `flag`
if the check fails, which would be a defect of this file and not an
answer.  The number is not used: the search ends by itself. -/
def produce (s : Seq) (_ : Nat) : Certify.Verdict (Script S) Tree :=
  match proofOrRef s with
  | .inl d =>
    if h : treeCert.check s d.toCert = true then
      .pass (Der.ofCert s d.toCert ((treeCert_check s _).symm.trans h)).script
    else .flag
  | .inr r => if noDerivable.check s r.1 then .fail r.1 else .flag

/-- **Both sides and the producer, as one engine.** -/
def glsEngine : Certify.Engine Seq (Script S) Tree Derivable :=
  engine step_sound_derivable noDerivable produce

#certify_domain GLS.produce

/-! ## One side always answers -/

/-- **Level 3**: for every sequent there is a tree of moves that checks,
or a finite tree that the check against validity accepts. -/
theorem decided (s : Seq) :
    (∃ c, treeCert.check s c = true) ∨ (∃ t, noValid.check s t = true) := by
  rcases proofOrRef s with d | r
  · exact .inl ⟨d.toCert, (treeCert_check s _).trans d.check_toCert⟩
  · exact .inr ⟨r.1, (noValid_check s _).trans r.2⟩

/-- The producer answers `pass` for every sequent that has a derivation. -/
theorem glsEngine_complete : glsEngine.Complete := by
  rintro s ⟨d₀⟩
  refine ⟨0, ?_⟩
  show ∃ c, produce s 0 = .pass c
  unfold produce
  cases hs : proofOrRef s with
  | inl d =>
    refine ⟨(Der.ofCert s d.toCert d.check_toCert).script, ?_⟩
    simp [(treeCert_check s _).trans d.check_toCert]
  | inr r => exact absurd ⟨d₀⟩ (noDerivable.sound s r.1 ((noValid_check s _).trans r.2))

end GLS

#axioms_within_file [propext, Quot.sound]
