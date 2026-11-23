/-
System K°: the rules of K that keep their main formula, with the provisos
that make proof search end.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, §2.1.3,
pp. 14–15: the display after Definition 2.13 and the paragraph that
follows it.  The source has no figure for these rules.  Read at `X = ∅`:
the systems `(K + ◇X_c)°` with `X` empty.  Theory file: it ends with its
bound on axioms.
-/
import BrunnlerK.Sequent

namespace BrunnlerK

/-- **Proofs in system K°.**

"For each rule ρ we define a rule ρ° which keeps the main formula from
the conclusion.  For most rules ρ = ρ°" (p. 14): `∧°`, `∨°` and `□°` are
displayed, and `◇k_c` keeps its main formula already.  "In addition, each
rule ρ° carries the proviso that for all of its premises the set sequent
is different from the set sequent of the conclusion": the fields `hs`,
`hs₁`, `hs₂`.  The axiom is not a rule, and has no proviso.

The conclusion of every constructor is a variable, and the place a rule
acts at is a path, as in `Fam`. -/
inductive FamO : NSeq → Type where
  /-- The axiom `Γ{p, p̄}`, as in system K. -/
  | ax {Γ Θ : NSeq} (a : Path) (p : Nat)
      (hΘ : Γ.node? a = some Θ)
      (hp : Form.atom p ∈ Θ.forms) (hn : Form.natom p ∈ Θ.forms) :
      FamO Γ
  /-- The rule `∧°`, p. 14: from `Γ{A ∧ B, A}` and `Γ{A ∧ B, B}`,
  `Γ{A ∧ B}`. -/
  | and {Γ Θ : NSeq} (a : Path) (A B : Form)
      (hΘ : Γ.node? a = some Θ) (hA : A ⋏ B ∈ Θ.forms)
      (hs₁ : (Γ.setNode a (Θ.add A)).sameSet Γ = false)
      (hs₂ : (Γ.setNode a (Θ.add B)).sameSet Γ = false)
      (d₁ : FamO (Γ.setNode a (Θ.add A)))
      (d₂ : FamO (Γ.setNode a (Θ.add B))) :
      FamO Γ
  /-- The rule `∨°`, p. 14: from `Γ{A ∨ B, A, B}`, `Γ{A ∨ B}`. -/
  | or {Γ Θ : NSeq} (a : Path) (A B : Form)
      (hΘ : Γ.node? a = some Θ) (hA : A ⋎ B ∈ Θ.forms)
      (hs : (Γ.setNode a ((Θ.add B).add A)).sameSet Γ = false)
      (d : FamO (Γ.setNode a ((Θ.add B).add A))) :
      FamO Γ
  /-- The rule `□°`, p. 14: from `Γ{□A, [A]}`, `Γ{□A}`, "where in the
  conclusion the node of the active formula does not have a child node
  which contains `A`": the field `hch`. -/
  | box {Γ Θ : NSeq} (a : Path) (A : Form)
      (hΘ : Γ.node? a = some Θ) (hA : □A ∈ Θ.forms)
      (hch : ∀ Δ ∈ Θ.boxes, A ∉ Δ.forms)
      (hs : (Γ.setNode a (Θ.addBox (.leaf [A]))).sameSet Γ = false)
      (d : FamO (Γ.setNode a (Θ.addBox (.leaf [A])))) :
      FamO Γ
  /-- The rule `◇k_c°`, which is `◇k_c` (Figure 2.3) with the proviso:
  from `Γ{◇A, [Δ, A]}`, `Γ{◇A, [Δ]}`.  The box `[Δ]` is the one at
  position `i` of the node. -/
  | dia {Γ Θ Δ : NSeq} (a : Path) (i : Nat) (A : Form)
      (hΘ : Γ.node? a = some Θ) (hA : ◇A ∈ Θ.forms)
      (hΔ : Θ.box? i = some Δ)
      (hs : (Γ.setNode a (Θ.setBox i (Δ.add A))).sameSet Γ = false)
      (d : FamO (Γ.setNode a (Θ.setBox i (Δ.add A)))) :
      FamO Γ

-- Compared with the source's display line by line in
-- `campaign/rule-table.md`.  The controls for `#slime` are in
-- `BrunnlerK/System.lean`.
#rules BrunnlerK.FamO
#slime BrunnlerK.FamO

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
