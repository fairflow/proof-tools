/-
The calculus GLS, and its version for proof search PSGLS, as the source
states them: two inductive families, one constructor for each rule.

Source: the Coq file `GL/GLS_PSGLS_calcs.v` of `ianshil/CE_GLS`, commit
`3dd8619`: the rule schemes at l. 264-300, `GLS_rules` at l. 306,
`PSGLS_rules` at l. 314.  Theory file: it ends with its bound on axioms.

How a rule of the source reads here (the divergences of representation
are in `campaign/rule-table.md`).  The source writes the principal
formula of a rule at a place in a list, `Γ0 ++ A :: Γ1`.  Here the
conclusion of every rule is `Γ ⇒ Δ` for two lists; the principal formula
is asked for by membership; and a premise removes one occurrence of it
(`List.erase`) and puts what the rule adds at the head.
-/
import GLS.Form

namespace GLS

/-- **GLS** (the Coq file, l. 306, `GLS_rules`).  Into `Type`: a
derivation is data. -/
inductive Fam : Seq → Type where
  /-- IdP (l. 264): `Γ0, #P, Γ1 ⇒ Δ0, #P, Δ1`. -/
  | idP {Γ Δ : List Form} (p : Nat) (hΓ : Form.var p ∈ Γ) (hΔ : Form.var p ∈ Δ) : Fam (Γ ⇒ Δ)
  /-- BotL (l. 274): `Γ0, ⊥, Γ1 ⇒ Δ`. -/
  | botL {Γ Δ : List Form} (h : ⊥ ∈ Γ) : Fam (Γ ⇒ Δ)
  /-- ImpR (l. 279): from `Γ0, A, Γ1 ⇒ Δ0, B, Δ1` to
  `Γ0, Γ1 ⇒ Δ0, A → B, Δ1`. -/
  | impR {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Δ)
      (d : Fam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B))) : Fam (Γ ⇒ Δ)
  /-- ImpL (l. 285): from `Γ0, Γ1 ⇒ Δ0, A, Δ1` and `Γ0, B, Γ1 ⇒ Δ0, Δ1`
  to `Γ0, A → B, Γ1 ⇒ Δ0, Δ1`. -/
  | impL {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Γ)
      (d₁ : Fam (Γ.erase (A ⟶ B) ⇒ A :: Δ)) (d₂ : Fam (B :: Γ.erase (A ⟶ B) ⇒ Δ)) : Fam (Γ ⇒ Δ)
  /-- GLR (l. 297): from `XBoxed_list BΓ, Box A ⇒ A` to
  `Γ0 ⇒ Δ0, Box A, Δ1`, where `BΓ` is the boxed formulas of `Γ0`. -/
  | glr {Γ Δ : List Form} (A : Form) (h : □A ∈ Δ) (d : Fam (xbox Γ ++ [□A] ⇒ [A])) : Fam (Γ ⇒ Δ)

/-- The sequent is an instance of IdP: a variable on both sides. -/
def Seq.IsIdP (s : Seq) : Prop := ∃ p, Form.var p ∈ s.ant ∧ Form.var p ∈ s.suc

/-- The sequent is an instance of IdB: a boxed formula on both sides. -/
def Seq.IsIdB (s : Seq) : Prop := ∃ A, □A ∈ s.ant ∧ □A ∈ s.suc

/-- The sequent is an instance of BotL: `⊥` in the antecedent. -/
def Seq.IsBotL (s : Seq) : Prop := ⊥ ∈ s.ant

/-- **PSGLS** (the Coq file, l. 314, `PSGLS_rules`): "a proof-search
oriented version" of GLS (l. 35).  The rules of GLS, the axiom IdB, and
GLR only where the conclusion is no instance of IdP, IdB or BotL. -/
inductive PSFam : Seq → Type where
  /-- PSIdP (l. 315). -/
  | idP {Γ Δ : List Form} (p : Nat) (hΓ : Form.var p ∈ Γ) (hΔ : Form.var p ∈ Δ) : PSFam (Γ ⇒ Δ)
  /-- PSIdB (l. 316; the scheme IdB, l. 269): `Γ0, Box A, Γ1 ⇒ Δ0, Box A, Δ1`. -/
  | idB {Γ Δ : List Form} (A : Form) (hΓ : □A ∈ Γ) (hΔ : □A ∈ Δ) : PSFam (Γ ⇒ Δ)
  /-- PSBotL (l. 317). -/
  | botL {Γ Δ : List Form} (h : ⊥ ∈ Γ) : PSFam (Γ ⇒ Δ)
  /-- PSImpR (l. 318). -/
  | impR {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Δ)
      (d : PSFam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B))) : PSFam (Γ ⇒ Δ)
  /-- PSImpL (l. 320). -/
  | impL {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Γ)
      (d₁ : PSFam (Γ.erase (A ⟶ B) ⇒ A :: Δ)) (d₂ : PSFam (B :: Γ.erase (A ⟶ B) ⇒ Δ)) :
      PSFam (Γ ⇒ Δ)
  /-- PSGLR (l. 322): GLR, where the conclusion is an instance of none of
  IdP, IdB, BotL. -/
  | glr {Γ Δ : List Form} (A : Form) (nP : ¬ (Γ ⇒ Δ).IsIdP) (nB : ¬ (Γ ⇒ Δ).IsIdB)
      (nBot : ¬ (Γ ⇒ Δ).IsBotL) (h : □A ∈ Δ) (d : PSFam (xbox Γ ++ [□A] ⇒ [A])) : PSFam (Γ ⇒ Δ)

/-- A control for `#slime`: no computed index. -/
inductive CleanControl : List Nat → Prop where
  | nil : CleanControl []
  | cons {n : Nat} {ns : List Nat} (h : CleanControl ns) : CleanControl (n :: ns)

/-- A control for `#slime`: a computed index in a conclusion. -/
inductive SlimedControl : List Nat → Prop where
  | nil : SlimedControl []
  | app {ms ns : List Nat} (h₁ : SlimedControl ms) (h₂ : SlimedControl ns) :
      SlimedControl (ms ++ ns)

#rules GLS.Fam
#rules GLS.PSFam
#slime GLS.CleanControl GLS.SlimedControl
#slime GLS.Fam
#slime GLS.PSFam

/-- **The height of a derivation** (the Coq files, `general/dd_fc.v`
l. 131, `derrec_height`): an instance of a rule with no premise has height
1, and an instance with premises one more than the highest of them. -/
def Fam.height : {s : Seq} → Fam s → Nat
  | _, .idP _ _ _ => 1
  | _, .botL _ => 1
  | _, .impR _ _ _ d => d.height + 1
  | _, .impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .glr _ _ d => d.height + 1

end GLS

#axioms_within_file [propext, Quot.sound]
