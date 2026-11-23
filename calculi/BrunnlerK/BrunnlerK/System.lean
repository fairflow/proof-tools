/-
System K, and K with cut, as one inductive family.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, §2.1.1:
Figure 2.3 (label `fig:kx`, p. 10) for the axiom and the rules `∧`, `∨`,
`□`, `◇k_c`; Figure 2.4 (label `fig:admissible`, p. 10) for `cut`.
"System K is the set of rules {∧, ∨, □, ◇k_c}" (p. 9).  Theory file: it
ends with its bound on axioms.
-/
import BrunnlerK.Sequent

namespace BrunnlerK

/-- **Proofs in system K** (`Fam false`) **and in K + cut** (`Fam true`).

One constructor for the axiom, one for each rule of system K, and one for
`cut`, which asks that the parameter is `true`.

Every rule of the source is stated for a context `Γ{ }`.  Here the
conclusion of every constructor is a variable `Γ`; the place of the hole
is a path `a`; the sequent at that place, all of it, is `Θ`
(`Γ.node? a = some Θ`); and each premise is `Γ` with `Θ` replaced
(`Γ.setNode a …`).  A formula that the rule acts on is asked for by
membership, at any position among the formulas of `Θ`.  The letters `Γ`,
`Δ`, `A`, `B`, `p` are the figure's; `Θ`, `a` and `i` are not in it. -/
inductive Fam (c : Bool) : NSeq → Type where
  /-- The axiom `Γ{p, p̄}`, Figure 2.3: "a proof … is a derivation … where
  all premises are instances of the axiom" (p. 9).  For propositions `p`
  only. -/
  | ax {Γ Θ : NSeq} (a : Path) (p : Nat)
      (hΘ : Γ.node? a = some Θ)
      (hp : Form.atom p ∈ Θ.forms) (hn : Form.natom p ∈ Θ.forms) :
      Fam c Γ
  /-- The rule `∧`, Figure 2.3: from `Γ{A}` and `Γ{B}`, `Γ{A ∧ B}`. -/
  | and {Γ Θ : NSeq} (a : Path) (A B : Form)
      (hΘ : Γ.node? a = some Θ) (hA : A ⋏ B ∈ Θ.forms)
      (d₁ : Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add A)))
      (d₂ : Fam c (Γ.setNode a ((Θ.erase (A ⋏ B)).add B))) :
      Fam c Γ
  /-- The rule `∨`, Figure 2.3: from `Γ{A, B}`, `Γ{A ∨ B}`. -/
  | or {Γ Θ : NSeq} (a : Path) (A B : Form)
      (hΘ : Γ.node? a = some Θ) (hA : A ⋎ B ∈ Θ.forms)
      (d : Fam c (Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A))) :
      Fam c Γ
  /-- The rule `□`, Figure 2.3: from `Γ{[A]}`, `Γ{□A}`. -/
  | box {Γ Θ : NSeq} (a : Path) (A : Form)
      (hΘ : Γ.node? a = some Θ) (hA : □A ∈ Θ.forms)
      (d : Fam c (Γ.setNode a ((Θ.erase (□A)).addBox (.leaf [A])))) :
      Fam c Γ
  /-- The rule `◇k_c`, Figure 2.3: from `Γ{◇A, [Δ, A]}`, `Γ{◇A, [Δ]}`.
  The box `[Δ]` is the one at position `i` of the node. -/
  | dia {Γ Θ Δ : NSeq} (a : Path) (i : Nat) (A : Form)
      (hΘ : Γ.node? a = some Θ) (hA : ◇A ∈ Θ.forms)
      (hΔ : Θ.box? i = some Δ)
      (d : Fam c (Γ.setNode a (Θ.setBox i (Δ.add A)))) :
      Fam c Γ
  /-- The rule `cut`, Figure 2.4: from `Γ{A}` and `Γ{Ā}`, `Γ{∅}`.  Not a
  rule of system K: allowed only where the parameter is `true`. -/
  | cut {Γ Θ : NSeq} (a : Path) (A : Form)
      (hc : c = true)
      (hΘ : Γ.node? a = some Θ)
      (d₁ : Fam c (Γ.setNode a (Θ.add A)))
      (d₂ : Fam c (Γ.setNode a (Θ.add ∼A))) :
      Fam c Γ

/-- Proofs in system K: `K ⊢ Γ` is `Nonempty (K Γ)`. -/
abbrev K : NSeq → Type := Fam false

/-- Proofs in system K with cut. -/
abbrev Kcut : NSeq → Type := Fam true

/-- A control for `#slime`: no computed index. -/
inductive CleanControl : List Nat → Prop where
  | nil : CleanControl []
  | cons {n : Nat} {ns : List Nat} (h : CleanControl ns) : CleanControl (n :: ns)

/-- A control for `#slime`: a computed index in a conclusion. -/
inductive SlimedControl : List Nat → Prop where
  | nil : SlimedControl []
  | app {ms ns : List Nat} (h₁ : SlimedControl ms) (h₂ : SlimedControl ns) :
      SlimedControl (ms ++ ns)

-- Compared with Figures 2.3 and 2.4 line by line in `campaign/rule-table.md`.
#rules BrunnlerK.Fam
-- `#slime` must pass the first control and warn of the second.
#slime BrunnlerK.CleanControl BrunnlerK.SlimedControl
#slime BrunnlerK.Fam

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
