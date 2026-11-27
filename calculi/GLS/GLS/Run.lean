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
  root, one subformula at a time over all the worlds, each different
  subformula once (`Seq.refutedM`, `GLS/Table.lean`), which is
  `Seq.refutedAt` by S30 (`Seq.refutedM_eq`).
  `noValid.verdict s t : Valid s → False`.

Each check is the algorithm one would run, and the kernel and compiled
code run the same one.  The definitions they are proved equal to are
exponential where a formula has many nested boxes, run as they are
written: `Form.holds` asks again for what it has computed, and
`Cert.check` writes out sequents that GLR doubles
(`campaign/measurements.md`, "The two checks").
* **For a script**: the checker runs it with the goals kept by counts
  (`Seq.scriptCheck`, `GLS/Scripts.lean`), which is the library's
  `derives` by S29.
* **The producer** is the search of `GLS/Decide.lean`, compiled: at
  sequents without repeated formulas, so that it writes no sequent of GLS
  out.  It is proved to end and to be right (S28).  (Until 2026-11-27 it
  was the search of `GLS/Search.lean`, which returns a derivation of GLS
  as a term and so builds every sequent of it.)

Theory file: it ends with its bound on axioms.
-/
import GLS.Completeness
import GLS.Proof
import GLS.Table
import GLS.Counts
import GLS.Decide
import GLS.Scripts
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
derivation of `s` in GLS.  The check runs the script with its goals kept
by counts (`Seq.scriptCheck`, `GLS/Scripts.lean`), which is the library's
`derives` by S29. -/
def scriptCert : Certify.Certifier Seq (Script S) Fam where
  check s ls := s.scriptCheck ls
  sound s ls h := (certifier step_sound).sound s ls ((scriptCheck_eq s ls).symm.trans h)

/-- The check of `scriptCert` is the library's check of a script. -/
theorem scriptCert_check (s : Seq) (ls : Script S) : scriptCert.check s ls = derives S s ls :=
  scriptCheck_eq s ls

/-- **Finite trees, checked against validity**: if `s` is computed false
at the root of `t`, then `s` is not valid. -/
def noValid : Certify.Certifier Seq Tree (fun s => Valid s → False) where
  check s t := s.refutedM t
  sound s t h hv := not_satSeq_of_refutedAt ((Seq.refutedM_eq s t).symm.trans h)
    (hv treeModel treeModel_GL treeModel_twoValued t)

/-- The check of `noValid`, and of `noDerivable`, is the definition
`Seq.refutedAt`. -/
theorem noValid_check (s : Seq) (t : Tree) : noValid.check s t = s.refutedAt t :=
  Seq.refutedM_eq s t

/-- The same against derivability: by soundness, what is not valid has no
derivation. -/
def noDerivable : Certify.Certifier Seq Tree (fun s => Derivable s → False) where
  check s t := s.refutedM t
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

/-- A tree of moves for `s`, where there is a derivation. -/
def prove? (s : Seq) : Option (Cert S) :=
  match certOrRef s with
  | .inl c => some c.1
  | .inr _ => none

/-- A tree that refutes `s`, where there is one. -/
def refute? (s : Seq) : Option Tree :=
  match certOrRef s with
  | .inl _ => none
  | .inr r => some r.1

mutual
  /-- **The script of a tree of moves**: each move at the first open goal,
  a node before its children and the children from the left.  It is the
  script of the derivation that the tree is, without the derivation being
  built: `Der.ofCert` writes every sequent out.  (That the two scripts
  are one is not proved; `GLS/RunTest.lean` compares them.) -/
  def certScript : Cert S → Script S
    | .node m cs => ⟨0, m⟩ :: certScriptL cs
  /-- `certScript` on a list. -/
  def certScriptL : List (Unit × Cert S) → Script S
    | [] => []
    | (_, c) :: cs => certScript c ++ certScriptL cs
end

/-- **The producer**: the search.  A script for a derivation, or a tree
against one.  It never answers `flag`, and the number is not used: the
search ends by itself. -/
def produce (s : Seq) (_ : Nat) : Certify.Verdict (Script S) Tree :=
  match certOrRef s with
  | .inl c => .pass (certScript c.1)
  | .inr r => .fail r.1

/-- **Both sides and the producer, as one engine.** -/
def glsEngine : Certify.Engine Seq (Script S) Tree Derivable where
  yes :=
    { check := fun s ls => s.scriptCheck ls
      sound := fun s ls h =>
        derives_sound step_sound_derivable ((scriptCheck_eq s ls).symm.trans h) }
  no := noDerivable
  produce := produce

#certify_domain GLS.produce

/-! ## One side always answers -/

/-- **Level 3**: for every sequent there is a tree of moves that checks,
or a finite tree that the check against validity accepts. -/
theorem decided (s : Seq) :
    (∃ c, treeCert.check s c = true) ∨ (∃ t, noValid.check s t = true) := by
  rcases certOrRef s with c | r
  · exact .inl ⟨c.1, (treeCert_check s _).trans c.2⟩
  · exact .inr ⟨r.1, (noValid_check s _).trans r.2⟩

/-- **Derivability in GLS is decidable, by the search over sets**: a tree
of moves that replays gives a derivation, and a tree at whose root the
sequent is false shows there is none. -/
@[reducible] def derivableDecidableFast : DerivableDecidable := fun s =>
  match certOrRef s with
  | .inl c => isTrue ⟨(Cert.certifier step_sound).sound s c.1 c.2⟩
  | .inr r => isFalse (noDerivable.sound s r.1 ((noValid_check s r.1).trans r.2))

/-- **Validity is decidable, by the search over sets**, in the same way. -/
@[reducible] def validDecidableFast : ValidDecidable := fun s =>
  match certOrRef s with
  | .inl c => isTrue (soundness s ((Cert.certifier step_sound).sound s c.1 c.2))
  | .inr r => isFalse (noValid.sound s r.1 ((noValid_check s r.1).trans r.2))

/-- The producer answers `pass` for every sequent that has a derivation. -/
theorem glsEngine_complete : glsEngine.Complete := by
  rintro s ⟨d₀⟩
  refine ⟨0, ?_⟩
  show ∃ c, produce s 0 = .pass c
  unfold produce
  cases hs : certOrRef s with
  | inl c => exact ⟨_, rfl⟩
  | inr r => exact absurd ⟨d₀⟩ (noDerivable.sound s r.1 ((noValid_check s _).trans r.2))

end GLS

#axioms_within_file [propext, Quot.sound]
