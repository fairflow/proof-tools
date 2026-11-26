/-
What runs: the certifiers of MALL, the two producers, and that one of the
two sides always answers.

The pattern is that of the skill `lean-certify`: the theory says what
holds; a producer that is not trusted computes a certificate; a checker
proved sound certifies it in the kernel.

* **For a derivation**: the certificate is a tree of moves; the checker is
  the library's `Cert.check`, which runs `step`; its soundness is S1
  (`step_sound`).  `treeCert.verdict Γ c : Fam Γ`.  The ⊗ and cut moves of
  the tree name the context of their first premise: the checker sees every
  split.
* **Against derivability**: there is no certificate to write.  The search
  for a derivation without cut is proved complete and is structural, so
  the kernel runs it: `noDerivable.verdict Γ () : ¬ Derivable Γ`, which is
  `by decide +kernel` under another name.
* **The producers**: the proved search (`searchCF`), which tries every
  split of a context at ⊗; and the search by lazy splitting
  (`MALL/Lazy.lean`), which is not proved.  What either returns is checked
  before it is handed on.

Theory file: it ends with its bound on axioms.
-/
import MALL.Results
import MALL.Proof
import MALL.Lazy
import LeanCertify

namespace MALL

open ProofTools ProofTools.Explore

/-! ## The certifiers -/

/-- **Trees of moves, checked**: a tree that `Cert.check` accepts for `Γ`
gives a derivation of `Γ`. -/
def treeCert : Certify.Certifier (List Form) (Cert S) Fam := Cert.certifier step_sound

/-- **Scripts, checked**: a script that runs to the end from `Γ` gives a
derivation of `Γ`. -/
def scriptCert : Certify.Certifier (List Form) (Script S) Fam := certifier step_sound

/-- **Against derivability**: the check is the decision procedure, and the
certificate carries nothing. -/
def noDerivable : Certify.Certifier (List Form) Unit (fun Γ => Derivable Γ → False) where
  check Γ _ := !decide (Derivable Γ)
  sound Γ _ h := fun hd => by
    rw [decide_eq_true hd] at h
    cases h

/-- **Against validity**: the same, by soundness and completeness. -/
def noValid : Certify.Certifier (List Form) Unit (fun Γ => Valid Γ → False) where
  check Γ _ := !decide (Derivable Γ)
  sound Γ _ h := fun hv => noDerivable.sound Γ () h ((valid_iff_derivable Γ).1 hv)

#certify_structural MALL.treeCert
#certify_statement MALL.treeCert
#certify_structural MALL.noDerivable
#certify_statement MALL.noDerivable
#certify_structural MALL.noValid
#certify_statement MALL.noValid

/-! ## From a derivation without cut to its tree of moves -/

/-- The tree of moves of a derivation without cut: at each rule instance,
the move with what the constructor carries.  (The premises `step` computes
are those of the constructor up to a permutation, so that this tree checks
is not by definition; the producers check it.) -/
def CF.toCert : {Γ : List Form} → CF Γ → Cert S
  | _, .ax A _ => .mk (.ax A) []
  | _, .top _ _ => .mk .top []
  | _, .wth A B _ _ d₁ d₂ => .mk (.wth A B) [d₁.toCert, d₂.toCert]
  | _, .plus₁ A B _ _ d => .mk (.plus₁ A B) [d.toCert]
  | _, .plus₂ A B _ _ d => .mk (.plus₂ A B) [d.toCert]
  | _, .one _ => .mk .one []
  | _, .bot _ _ d => .mk .bot [d.toCert]
  | _, .tensor A B Γ _ _ d₁ d₂ => .mk (.tensor A B Γ) [d₁.toCert, d₂.toCert]
  | _, .par A B _ _ d => .mk (.par A B) [d.toCert]

/-! ## The producers -/

/-- A tree of moves from the proved search, checked. -/
def proveSearch (Γ : List Form) : Option (Cert S) :=
  match searchCF Γ with
  | some d => if Cert.check Γ d.toCert then some d.toCert else none
  | none => none

/-- A tree of moves from the search by lazy splitting, checked. -/
def proveLazy (Γ : List Form) : Option (Cert S) :=
  match Lazy.prove Γ with
  | some c => if Cert.check Γ c then some c else none
  | none => none

/-- **The producer**: the lazy search, with what it returns checked before
it is handed on; where it finds nothing, the decision procedure.  A script
for a derivation, `fail` where the sequent is decided not derivable, and
`flag` where the two disagree, which would be a defect of the lazy search
and not an answer.  The number is not used: both searches end by
themselves. -/
def produce (Γ : List Form) (_ : Nat) : Certify.Verdict (Script S) Unit :=
  match Lazy.prove Γ with
  | some c =>
    if h : Cert.check Γ c = true then .pass (Der.ofCert Γ c h).script else .flag
  | none => if noDerivable.check Γ () then .fail () else .flag

/-- **Both sides and the producer, as one engine.** -/
def mallEngine : Certify.Engine (List Form) (Script S) Unit Derivable :=
  engine step_sound_derivable noDerivable produce

#certify_domain MALL.produce

/-! ## One side always answers -/

/-- **Level 3**: for every sequent there is a tree of moves that checks,
or the check against derivability accepts. -/
theorem decided (Γ : List Form) :
    (∃ c, treeCert.check Γ c = true) ∨ noDerivable.check Γ () = true := by
  by_cases h : Derivable Γ
  · obtain ⟨d⟩ := h
    obtain ⟨der⟩ := famToDer Γ d
    exact .inl ⟨der.cert, Att.check_cert der⟩
  · exact .inr (by show (!decide (Derivable Γ)) = true; rw [decide_eq_false h]; rfl)

end MALL

#axioms_within_file [propext, Quot.sound]
