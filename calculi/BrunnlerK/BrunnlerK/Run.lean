/-
What runs: the certifiers of system K, the producer, and that one of the
two sides always answers.

The pattern is that of the skill `lean-certify`: the theory says what
holds; a producer that is not trusted computes a certificate; a checker
proved sound certifies it in the kernel.

* **For a proof**: the certificate is a tree of moves; the checker is the
  library's `Cert.check`, which runs `step`; its soundness is S1
  (`step_sound`).  `treeCert.verdict Γ c : K Γ`.
* **Against validity**: the certificate is a finite tree; the checker
  computes that the corresponding formula is not true at its root
  (`Form.holds`).  `noValid.verdict Γ t : Valid Γ → False`.
* **The producer** is the search of `BrunnlerK/Search.lean`, compiled.
  It is proved to end and to be right, but nothing here rests on that:
  what it returns is checked.  The kernel then checks a tree; it does not
  run the search.

Theory file: it ends with its bound on axioms.
-/
import BrunnlerK.Completeness
import BrunnlerK.Proof
import LeanCertify

namespace BrunnlerK

open ProofTools ProofTools.Explore

/-! ## The certifiers -/

/-- **Trees of moves, checked**: a tree that `Cert.check` accepts for `Γ`
gives a proof of `Γ` in system K. -/
def treeCert : Certify.Certifier NSeq (Cert S) K := Cert.certifier step_sound

/-- **Scripts, checked**: a script that runs to the end from `Γ` gives a
proof of `Γ` in system K. -/
def scriptCert : Certify.Certifier NSeq (Script S) K := certifier step_sound

/-- **Finite trees, checked against validity**: if the corresponding
formula of `Γ` is computed not true at the root of `t`, then `Γ` is not
valid. -/
def noValid : Certify.Certifier NSeq Tree (fun Γ => Valid Γ → False) where
  check Γ t := !Γ.form.holds t
  sound Γ t h hv := by
    have h₁ := (holds_iff Γ.form t).mp (hv treeModel treeModel_twoValued t)
    rw [h₁] at h
    cases h

/-- The same against derivability: by soundness, what is not valid has no
proof. -/
def noDerivable : Certify.Certifier NSeq Tree (fun Γ => Derivable Γ → False) where
  check Γ t := !Γ.form.holds t
  sound Γ t h := fun ⟨d⟩ => noValid.sound Γ t h (soundness Γ d)

#certify_structural BrunnlerK.treeCert
#certify_statement BrunnlerK.treeCert
#certify_structural BrunnlerK.noValid
#certify_statement BrunnlerK.noValid
#certify_structural BrunnlerK.noDerivable
#certify_statement BrunnlerK.noDerivable

/-! ## From a proof to its tree of moves -/

/-- The tree of moves of a proof: at each rule instance, the move with
what the constructor carries.  (`cut` has no move; a proof in system K
has no `cut`.) -/
def Fam.toCert {c : Bool} : {Γ : NSeq} → Fam c Γ → Cert S
  | _, .ax a p _ _ _ => .mk (.ax a p) []
  | _, .and a A B _ _ d₁ d₂ => .mk (.and a A B) [d₁.toCert, d₂.toCert]
  | _, .or a A B _ _ d => .mk (.or a A B) [d.toCert]
  | _, .box a A _ _ d => .mk (.box a A) [d.toCert]
  | _, .dia a i A _ _ _ d => .mk (.dia a i A) [d.toCert]
  | _, .cut _ _ _ _ _ _ => .mk (.ax [] 0) []

/-- The tree of moves of a proof in system K checks. -/
theorem Fam.check_toCert {c : Bool} {Γ : NSeq} (d : Fam c Γ) (hc : c = false) :
    Cert.check Γ d.toCert = true := by
  induction d with
  | @ax Γ Θ a p hΘ hp hn =>
    have h : S.step (.ax a p) Γ = .ok [] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hp, hn]
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    rfl
  | @and Γ Θ a A B hΘ hA _ _ ih₁ ih₂ =>
    have h : S.step (.and a A B) Γ = .ok [Γ.setNode a ((Θ.erase (A ⋏ B)).add A),
        Γ.setNode a ((Θ.erase (A ⋏ B)).add B)] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih₁, ih₂]
  | @or Γ Θ a A B hΘ hA _ ih =>
    have h : S.step (.or a A B) Γ = .ok [Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A)] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih]
  | @box Γ Θ a A hΘ hA _ ih =>
    have h : S.step (.box a A) Γ = .ok [Γ.setNode a ((Θ.erase (□A)).addBox (.leaf [A]))] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih]
  | @dia Γ Θ Δ a i A hΘ hA hΔ _ ih =>
    have h : S.step (.dia a i A) Γ = .ok [Γ.setNode a (Θ.setBox i (Δ.add A))] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hΔ, diaRule, hA]
    rw [Fam.toCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, ih]
  | cut _ _ hc' => exact absurd (hc ▸ hc') (by decide)

/-! ## The producers -/

/-- A tree of moves for `Γ`, where the search finds a proof. -/
def prove? (Γ : NSeq) : Option (Cert S) :=
  match search Γ with
  | .inl d => some d.toCert
  | .inr _ => none

/-- A tree that refutes `Γ`, where the search finds one. -/
def refute? (Γ : NSeq) : Option Tree :=
  match search Γ with
  | .inl _ => none
  | .inr r => some r.tree

/-- **The producer**: the search, with what it returns checked before it
is handed on.  A script for a proof, a tree against one, or `flag` if the
check fails, which would be a defect of this file and not an answer.  The
number is not used: the search ends by itself. -/
def produce (Γ : NSeq) (_ : Nat) : Certify.Verdict (Script S) Tree :=
  match search Γ with
  | .inl d =>
    if h : Cert.check Γ d.toCert = true then .pass (Der.ofCert Γ d.toCert h).script
    else .flag
  | .inr r => if noDerivable.check Γ r.tree then .fail r.tree else .flag

/-- **Both sides and the producer, as one engine.** -/
def kEngine : Certify.Engine NSeq (Script S) Tree Derivable :=
  engine step_sound_derivable noDerivable produce

#certify_domain BrunnlerK.produce

/-! ## One side always answers -/

/-- **Level 3**: for every sequent there is a tree of moves that checks,
or a finite tree that the check against validity accepts. -/
theorem decided (Γ : NSeq) :
    (∃ c, treeCert.check Γ c = true) ∨ (∃ t, noValid.check Γ t = true) := by
  rcases search Γ with d | r
  · exact .inl ⟨d.toCert, d.check_toCert rfl⟩
  · refine .inr ⟨r.tree, ?_⟩
    show (!Γ.form.holds r.tree) = true
    have h := r.refutes
    rw [holds_iff] at h
    cases hh : Γ.form.holds r.tree
    · rfl
    · exact absurd hh h

/-- The producer answers `pass` for every sequent that has a proof. -/
theorem kEngine_complete : kEngine.Complete := by
  rintro Γ ⟨d₀⟩
  refine ⟨0, ?_⟩
  show ∃ c, produce Γ 0 = .pass c
  unfold produce
  cases hs : search Γ with
  | inl d =>
    refine ⟨(Der.ofCert Γ d.toCert (d.check_toCert rfl)).script, ?_⟩
    simp [d.check_toCert rfl]
  | inr r =>
    exact absurd ((holds_iff Γ.form r.tree).mpr
      ((holds_iff Γ.form r.tree).mp ((soundness Γ d₀) treeModel treeModel_twoValued r.tree)))
      r.refutes

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
