/-
Finite phase structures as data, and their check against a sequent: a
certificate that a sequent is not valid, and so not derivable.

The structures are those on a cyclic group: the phases are the numbers
`0, …, k` under addition modulo `k + 1`, with any set of antiphases and
any set for each letter (its closure `G⊥⊥` is taken as the letter's fact,
so that every certificate is a phase structure).  A set of phases is a
list of Booleans.  The check computes the interpretation of the sequent,
by the clauses of Definition 1.14, and asks that the unit, 0, be not in
it.

Cyclic groups are a choice: they are the smallest structures that refute
the sequents of the corpus.  The finite model property
(`MALL/FiniteModel.lean`) says that every sequent with no derivation is
refuted by some finite phase structure; it does not say by a cyclic
group.

Theory file: it ends with its bound on axioms.
-/
import MALL.Soundness

namespace MALL

open PhaseSpace

/-- **A phase structure on ℤ/(k+1), as data.** -/
structure ZModel where
  /-- The group is ℤ/(k+1). -/
  k : Nat
  /-- The antiphases: `bot[i]` says whether `i` is one. -/
  bot : List Bool
  /-- A set of phases for each letter, by its number; the letter's fact is
  the closure of the set. -/
  val : List (List Bool)
  deriving DecidableEq, Repr, Lean.ToExpr

namespace ZModel

variable (z : ZModel)

/-- The phases. -/
abbrev Ph : Type := Fin (z.k + 1)

/-- Membership in a set given as a list. -/
def look (G : List Bool) (i : z.Ph) : Bool := G.getD i.val false

/-- The list of a set given as a function. -/
def tab (f : z.Ph → Bool) : List Bool := List.ofFn f

theorem look_tab (f : z.Ph → Bool) (i : z.Ph) : z.look (z.tab f) i = f i := by
  unfold look tab
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

/-- `f` holds of every phase. -/
def every (f : z.Ph → Bool) : Bool := (List.finRange (z.k + 1)).all f

/-- `f` holds of some phase. -/
def some (f : z.Ph → Bool) : Bool := (List.finRange (z.k + 1)).any f

theorem every_iff (f : z.Ph → Bool) : z.every f = true ↔ ∀ i, f i = true := by
  unfold every
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

theorem some_iff (f : z.Ph → Bool) : z.some f = true ↔ ∃ i, f i = true := by
  unfold some
  rw [List.any_eq_true]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, List.mem_finRange i, h⟩⟩

/-- The dual of a set (Definition 1.2), computed. -/
def dualL (G : List Bool) : List Bool :=
  z.tab fun p => z.every fun q => !z.look G q || z.look z.bot (p + q)

/-- The product of two sets (Definition 1.8), computed. -/
def prodL (G H : List Bool) : List Bool :=
  z.tab fun r => z.some fun p => z.some fun q => z.look G p && z.look H q && decide (r = p + q)

/-- The interpretation of a proposition (Definition 1.14(ii)), computed:
the clauses of `PhaseStructure.interp`. -/
def interpL : Form → List Bool
  | .atom a => z.dualL (z.dualL (z.val.getD a []))
  | .natom a => z.dualL (z.dualL (z.dualL (z.val.getD a [])))
  | .one => z.dualL z.bot
  | .bot => z.bot
  | .top => z.tab fun _ => true
  | .zero => z.dualL (z.tab fun _ => true)
  | .tensor A B => z.dualL (z.dualL (z.prodL (interpL A) (interpL B)))
  | .par A B => z.dualL (z.prodL (z.dualL (interpL A)) (z.dualL (interpL B)))
  | .wth A B => z.tab fun p => z.look (interpL A) p && z.look (interpL B) p
  | .plus A B => z.dualL (z.dualL (z.tab fun p => z.look (interpL A) p || z.look (interpL B) p))

/-- **The check**: the unit phase is not in the interpretation of the
sequent. -/
def refutes (Γ : List Form) : Bool := !z.look (z.interpL (parAll Γ)) 0

/-! ## The structure the data stands for -/

/-- The set of phases a list stands for. -/
def Pr (G : List Bool) : z.Ph → Prop := fun i => z.look G i = true

theorem add_comm' (a b : z.Ph) : a + b = b + a := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.add_comm]

theorem add_assoc' (a b c : z.Ph) : a + b + c = a + (b + c) := by
  apply Fin.ext
  simp only [Fin.val_add]
  rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-- The phase space: ℤ/(k+1), with the antiphases of the data. -/
def space : PhaseSpace where
  M := z.Ph
  mul := fun a b => a + b
  one := 0
  one_mul := Fin.zero_add
  mul_one := Fin.add_zero
  mul_comm := z.add_comm'
  mul_assoc := z.add_assoc'
  bot := z.Pr z.bot

theorem pr_dualL (G : List Bool) : z.Pr (z.dualL G) = z.space.dual (z.Pr G) :=
  funext fun p => propext (by
    show z.look (z.tab _) p = true ↔ ∀ q, z.look G q = true → z.look z.bot (p + q) = true
    rw [look_tab, every_iff]
    constructor
    · intro h q hq
      have := h q
      rw [hq] at this
      exact this
    · intro h q
      cases hG : z.look G q with
      | false => rfl
      | true => exact h q hG)

theorem pr_prodL (G H : List Bool) : z.Pr (z.prodL G H) = z.space.prod (z.Pr G) (z.Pr H) :=
  funext fun r => propext (by
    show z.look (z.tab _) r = true ↔
      ∃ p q, z.look G p = true ∧ z.look H q = true ∧ r = p + q
    rw [look_tab, some_iff]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := (z.some_iff _).1 hp
      rw [Bool.and_eq_true, Bool.and_eq_true] at hq
      exact ⟨p, q, hq.1.1, hq.1.2, of_decide_eq_true hq.2⟩
    · rintro ⟨p, q, hG, hH, e⟩
      refine ⟨p, (z.some_iff _).2 ⟨q, ?_⟩⟩
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨hG, hH⟩, decide_eq_true e⟩)

theorem pr_univ : z.Pr (z.tab fun _ => true) = fun _ => True :=
  funext fun p => propext ⟨fun _ => trivial, fun _ => z.look_tab _ p⟩

/-- **The phase structure of the data.** -/
def str : PhaseStructure where
  toPhaseSpace := z.space
  val := fun a => z.Pr (z.dualL (z.dualL (z.val.getD a [])))
  val_fact := fun a => by
    rw [pr_dualL]
    exact isFact_dual _

/-- The computed interpretation is the interpretation in that
structure. -/
theorem interp_eq : ∀ A : Form, z.str.interp A = z.Pr (z.interpL A)
  | .atom _ => rfl
  | .natom _ => (z.pr_dualL _).symm
  | .one => (z.pr_dualL z.bot).symm
  | .bot => rfl
  | .top => z.pr_univ.symm
  | .zero => by
    show z.space.dual (fun _ => True) = z.Pr (z.dualL (z.tab fun _ => true))
    rw [pr_dualL, pr_univ]
    rfl
  | .tensor A B => by
    show z.space.dual (z.space.dual (z.space.prod (z.str.interp A) (z.str.interp B))) = _
    rw [interp_eq A, interp_eq B, ← pr_prodL, ← pr_dualL, ← pr_dualL]
    rfl
  | .par A B => by
    show z.space.dual (z.space.prod (z.space.dual (z.str.interp A))
      (z.space.dual (z.str.interp B))) = _
    rw [interp_eq A, interp_eq B, ← pr_dualL, ← pr_dualL, ← pr_prodL, ← pr_dualL]
    rfl
  | .wth A B => by
    show (fun p => z.str.interp A p ∧ z.str.interp B p) = _
    rw [interp_eq A, interp_eq B]
    refine funext fun p => propext ?_
    show _ ↔ z.look (z.tab _) p = true
    rw [look_tab, Bool.and_eq_true]
    exact Iff.rfl
  | .plus A B => by
    show z.space.dual (z.space.dual (fun p => z.str.interp A p ∨ z.str.interp B p)) = _
    rw [interp_eq A, interp_eq B]
    have h : (fun p => z.Pr (z.interpL A) p ∨ z.Pr (z.interpL B) p) =
        z.Pr (z.tab fun p => z.look (z.interpL A) p || z.look (z.interpL B) p) :=
      funext fun p => propext (by
        show _ ↔ z.look (z.tab _) p = true
        rw [look_tab, Bool.or_eq_true]
        exact Iff.rfl)
    refine (congrArg (fun G => z.space.dual (z.space.dual G)) h).trans ?_
    rw [← pr_dualL, ← pr_dualL]
    rfl

/-- **What the check accepts is not valid.** -/
theorem not_valid_of_refutes {Γ : List Form} (h : z.refutes Γ = true) : ¬ Valid Γ := fun hv => by
  have hs : z.str.interp (parAll Γ) z.str.one := hv z.str
  rw [interp_eq] at hs
  have hl : z.look (z.interpL (parAll Γ)) 0 = true := hs
  unfold refutes at h
  rw [hl] at h
  cases h

/-- Nor derivable, by soundness. -/
theorem not_derivable_of_refutes {Γ : List Form} (h : z.refutes Γ = true) : ¬ Derivable Γ :=
  fun hd => z.not_valid_of_refutes h (soundness Γ hd)

end ZModel

end MALL

#axioms_within_file [propext, Quot.sound]
