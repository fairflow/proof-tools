/-
The corpus of the Run stage: sequents of known status, and families that
grow.  Code and data, not theory.

The status of each entry is from the source where it says so:
* CCP (Chang, Chaudhuri, Pfenning, CMU-CS-03-131R), pp. 16-18, the
  derivations that `DILL/Source.lean` writes with the family's
  constructors;
* the plan's Q4 (`campaign/plan.md`): the laws of `!`, which the sources
  assert and do not draw (also in `DILL/Source.lean`);
* the plan's "Known non-theorems";
and otherwise it is the writer's of this file ("ours"), with the reason.
A reason "the collapse" is: read ⊗ and & as "and", ⊕ as "or", ⊸ as
"implies", 1 and ⊤ as true, 0 as false, and drop `!`; every rule of the
figure then keeps classical truth, so a sequent that is classically
false at some values of its letters has no derivation.

Nothing rests on a status.  A derivation is a fact only when the kernel
has checked its tree (`dillrun facts` writes them), and `dillrun status`
reports where the search disagrees.  For a sequent that the search does
not derive it says `flag`, whatever the status: the "no" side is
`DILL/SatRun.lean`.
-/
import DILL.Run
import DILL.Tactic

namespace DILL.Corpus

open DILL ProofTools ProofTools.Explore

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-! ## Printing, as Lean source -/

/-- A sequent as Lean source, with the notations of `DILL.Form` and the
letters `p q r s`. -/
def seqSrc (j : Seq) : String :=
  srcForms j.unr ++ " ⨾ " ++ srcForms j.lin ++ " ⟹ " ++ j.goal.src

/-- A tree of moves as Lean source: `.mk <move> [<trees>]`. -/
partial def certSrc : Cert S → String
  | .node m cs =>
    let ms := m.src
    let ms := if ms.any (· == ' ') then "(." ++ ms ++ ")" else "." ++ ms
    ".mk " ++ ms ++ " [" ++ ", ".intercalate (cs.map fun x => certSrc x.2) ++ "]"

/-- The number of moves of a tree of moves. -/
partial def certSize : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certSize x.2).sum

/-- The nesting of a tree of moves. -/
partial def certDepth : Cert S → Nat
  | .node _ cs => 1 + (cs.map fun x => certDepth x.2).foldl max 0

/-- The number of copy moves along the branch that has most. -/
partial def certCopies : Cert S → Nat
  | .node m cs =>
    (match m with | .copy _ => 1 | _ => 0) + (cs.map fun x => certCopies x.2).foldl max 0

/-! ## The entries -/

/-- An entry of the corpus. -/
structure Entry where
  name : String
  seq : Seq
  /-- The sequent as Lean source. -/
  src : String
  /-- Its status: there is a derivation. -/
  derivable : Bool
  /-- Where the status is from. -/
  why : String

def entry (name : String) (j : Seq) (derivable : Bool) (why : String) : Entry :=
  ⟨name, j, seqSrc j, derivable, why⟩

/-- **The corpus.** -/
def entries : List Entry := [
  -- the derivations of the source
  entry "init" ([] ⨾ [p] ⟹ p) true "the rule init, CCP Figure 2",
  entry "copyInit" ([p] ⨾ [] ⟹ p) true "CCP p. 16; Source.copyInit",
  entry "modusPonens" ([] ⨾ [p, p ⊸ q] ⟹ q) true "CCP p. 16; Source.modusPonens",
  entry "withFst" ([] ⨾ [p & q] ⟹ p) true "CCP p. 17; Source.withFst",
  entry "withSnd" ([] ⨾ [p & q] ⟹ q) true "CCP p. 17; Source.withSnd",
  entry "lolliSelf" ([] ⨾ [p ⊸ q] ⟹ p ⊸ q) true
    "CCP p. 18, the sequent whose ⊸L is discussed: by init, or by ⊸R and ⊸L",
  -- the laws of `!` (the plan's Q4)
  entry "bangDerelict" ([] ⨾ [!p] ⟹ p) true "the plan's Q4; Source.bangDerelict",
  entry "bangDig" ([] ⨾ [!p] ⟹ !(!p)) true "the plan's Q4; Source.bangDig",
  entry "bangContract" ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) true "the plan's Q4; Source.bangContract",
  entry "bangWeaken" ([] ⨾ [!p] ⟹ 𝟏) true "the plan's Q4; Source.bangWeaken",
  entry "bangWithTensor" ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) true
    "the plan's Q4; Source.bangWithTensor",
  entry "bangTensorWith" ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) true
    "the plan's Q4; Source.bangTensorWith",
  entry "bangMap" ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) true "the plan's Q4; Source.bangMap",
  -- ours: the multiplicatives and the additives
  entry "tensorComm" ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) true "ours: ⊗ is commutative",
  entry "tensorAssoc" ([] ⨾ [(p ⊗ q) ⊗ r] ⟹ p ⊗ (q ⊗ r)) true "ours: ⊗ is associative",
  entry "unitL" ([] ⨾ [𝟏 ⊗ p] ⟹ p) true "ours: 1 is the unit of ⊗",
  entry "unitR" ([] ⨾ [p] ⟹ p ⊗ 𝟏) true "ours: 1 is the unit of ⊗",
  entry "curry" ([] ⨾ [(p ⊗ q) ⊸ r] ⟹ p ⊸ q ⊸ r) true "ours: ⊸ is the adjoint of ⊗",
  entry "uncurry" ([] ⨾ [p ⊸ q ⊸ r] ⟹ (p ⊗ q) ⊸ r) true "ours: the converse",
  entry "distrib" ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r)) true "ours: ⊗ over ⊕",
  entry "distrib'" ([] ⨾ [(p ⊗ q) ⊕ (p ⊗ r)] ⟹ p ⊗ (q ⊕ r)) true "ours: the converse",
  entry "withPair" ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r)) true "ours: & is a product",
  entry "plusCase" ([] ⨾ [(p ⊸ r) & (q ⊸ r)] ⟹ (p ⊕ q) ⊸ r) true "ours: ⊕ is a sum",
  entry "plusComm" ([] ⨾ [p ⊕ q] ⟹ q ⊕ p) true "ours: ⊕ is commutative",
  entry "withComm" ([] ⨾ [p & q] ⟹ q & p) true "ours: & is commutative",
  entry "topSlack" ([] ⨾ [p, q, r] ⟹ p ⊗ ⊤) true "ours: ⊤R takes what is left",
  entry "topSplit" ([] ⨾ [p, q] ⟹ ⊤ ⊗ ⊤) true "ours: ⊤R on either side of a ⊗",
  entry "zeroL" ([] ⨾ [𝟎, p] ⟹ q) true "the rule 0L, CCP Figure 2",
  entry "zeroSlack" ([] ⨾ [p, q ⊸ 𝟎, q] ⟹ r ⊗ s) true
    "ours: ⊸L, and 0L takes what is left",
  -- ours: `!` and the unrestricted zone
  entry "bangK" ([] ⨾ [!(p ⊸ q)] ⟹ (!p) ⊸ (!q)) true "ours: ! is a functor",
  entry "bangTensor" ([] ⨾ [!p, !q] ⟹ !(p ⊗ q)) true "ours: !R after two !L",
  entry "bangPlus" ([] ⨾ [(!p) ⊕ (!q)] ⟹ !(p ⊕ q)) true "ours: ⊕L, !L, !R",
  entry "validBang" ([p] ⨾ [] ⟹ !p) true
    "Barber Lemma 2.3, one half: a valid hypothesis gives !",
  entry "copyTwice" ([p] ⨾ [] ⟹ p ⊗ p) true "ours: a copy in each premise of ⊗R",
  entry "copyTensor" ([p ⊗ q] ⨾ [] ⟹ q ⊗ p) true
    "ours: the copy of a formula whose left rule is invertible",
  entry "copyBang" ([!p] ⨾ [] ⟹ p) true "ours: copy, !L, copy, init",
  entry "copyChain" ([p ⊸ q, q ⊸ r] ⨾ [p] ⟹ r) true "ours: two copies along a branch",
  entry "bangLoopFree" ([] ⨾ [!(p ⊸ p), p] ⟹ p) true
    "ours: init, with a valid hypothesis that could be copied for ever",
  entry "bangDouble" ([] ⨾ [!(p ⊸ (p ⊗ p)), p] ⟹ p ⊗ p) true "ours: one copy, ⊸L, ⊗L",
  -- the plan's known non-theorems
  entry "zeroGoal" ([] ⨾ [] ⟹ 𝟎) false "the plan: Pfenning 3.11",
  entry "weakenOne" ([] ⨾ [p] ⟹ 𝟏) false "the plan: no linear weakening",
  entry "weakenInit" ([] ⨾ [p, q] ⟹ p) false "the plan: no linear weakening",
  entry "contract" ([] ⨾ [p] ⟹ p ⊗ p) false "the plan: no linear contraction",
  entry "pfenning60" ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) false
    "the plan: Pfenning p. 60",
  entry "noPromote" ([] ⨾ [p] ⟹ !p) false "the plan: !R needs an empty linear zone",
  entry "plusProj" ([] ⨾ [p ⊕ q] ⟹ p) false "the plan: the additives",
  entry "withIntro" ([] ⨾ [p] ⟹ p & q) false "the plan: the additives",
  entry "bangLolli" ([] ⨾ [(!p) ⊸ q] ⟹ p ⊸ q) false "the plan: ! on the left",
  -- CCP p. 18, and ours
  entry "ccp18a" ([] ⨾ [] ⟹ p) false
    "CCP p. 18: the first premise of ⊸L at · ; A ⊸ B ⟹ A ⊸ B",
  entry "ccp18b" ([] ⨾ [q] ⟹ p ⊸ q) false "CCP p. 18: the second premise; no linear weakening",
  entry "withTensor" ([] ⨾ [p & q] ⟹ p ⊗ q) false "ours: & does not give ⊗",
  entry "tensorWith" ([] ⨾ [p ⊗ q] ⟹ p & q) false "ours: nor ⊗, &",
  entry "loop" ([] ⨾ [!(p ⊸ p)] ⟹ p) false
    "ours: the collapse; a copy can always be made",
  entry "loopU" ([p ⊸ p] ⨾ [] ⟹ p) false "ours: the same, from the unrestricted zone",
  entry "pump" ([] ⨾ [!(p ⊸ (p ⊗ p)), p] ⟹ q) false
    "ours: the collapse; each copy leaves more to use",
  entry "bangPlusNo" ([] ⨾ [!(p ⊕ q)] ⟹ (!p) ⊕ (!q)) false
    "ours: ! does not distribute over ⊕"]

/-! ## Families that grow -/

/-- The letter numbered `n`. -/
def ltr (n : Nat) : Form := .atom n

/-- The implications `a₀ ⊸ a₁, …, aₙ₋₁ ⊸ aₙ`. -/
def links (n : Nat) : List Form := (List.range n).map fun i => ltr i ⊸ ltr (i + 1)

/-- `· ; a₀, a₀ ⊸ a₁, …, aₙ₋₁ ⊸ aₙ ⟹ aₙ`: `n` uses of ⊸L, each of which
divides the linear zone in the one right way.  Derivable. -/
def chain (n : Nat) : Seq := [] ⨾ ltr 0 :: links n ⟹ ltr n

/-- `a₀ ⊸ a₁, …, aₙ₋₁ ⊸ aₙ ; a₀ ⟹ aₙ`: the implications in the
unrestricted zone.  Derivable, with `n` copies. -/
def chainU (n : Nat) : Seq := links n ⨾ [ltr 0] ⟹ ltr n

/-- `A₁ ⊗ (A₂ ⊗ … ⊗ Aₙ)`, and 1 for no formula. -/
def tensorOf : List Form → Form
  | [] => 𝟏
  | [A] => A
  | A :: Γ => A ⊗ tensorOf Γ

/-- `· ; aₙ, …, a₁ ⟹ a₁ ⊗ (a₂ ⊗ … ⊗ aₙ)`: one nest of tensors and its
`n` letters, the first of which is last in the zone.  Derivable. -/
def fan (n : Nat) : Seq :=
  [] ⨾ (List.range n).reverse.map (fun i => ltr (i + 1)) ⟹
    tensorOf ((List.range n).map fun i => ltr (i + 1))

/-- `· ; a₀, a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ⟹ aₙ`: the chain with its last link
missing.  For `n ≥ 1` there is no derivation (the collapse: every letter
true but `aₙ`). -/
def chainBad (n : Nat) : Seq := [] ⨾ ltr 0 :: links (n - 1) ⟹ ltr n

/-- `a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ; a₀ ⟹ aₙ`: the same with the implications
in the unrestricted zone.  For `n ≥ 1` there is no derivation. -/
def chainUBad (n : Nat) : Seq := links (n - 1) ⨾ [ltr 0] ⟹ ltr n

/-- A family by its name: the sequent, and whether it is derivable. -/
def family : String → Nat → Option (Seq × Bool)
  | "chain", n => some (chain n, true)
  | "chainU", n => some (chainU n, true)
  | "fan", n => some (fan n, true)
  | "chainBad", n => some (chainBad n, n == 0)
  | "chainUBad", n => some (chainUBad n, n == 0)
  | _, _ => none

end DILL.Corpus
