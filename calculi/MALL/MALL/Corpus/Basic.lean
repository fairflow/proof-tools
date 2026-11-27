/-
The corpus of the Run stage: sequents of known status, and families that
grow.  Code and data, not theory.

The status of each entry is from the source where it says so (Girard,
*Linear logic*, 1987: p. 5, p. 22, and the equations 1.9, 1.12, 1.13 read
as sequents, a linear equivalence being two of them), and otherwise the
operator's.  Nothing rests on a status: each fact of
`MALL/Corpus/Facts.lean` is checked by the kernel, and `mallrun status`
reports where a producer disagrees.
-/
import MALL.Run
import MALL.Tactic

namespace MALL.Corpus

open MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-- An entry of the corpus. -/
structure Entry where
  name : String
  seq : List Form
  /-- The sequent as Lean source. -/
  src : String
  /-- Its status. -/
  derivable : Bool
  /-- Where the status is from. -/
  why : String

def entry (name : String) (Γ : List Form) (derivable : Bool) (why : String) : Entry :=
  ⟨name, Γ, srcForms Γ, derivable, why⟩

/-- **The corpus.** -/
def entries : List Entry := [
  entry "axLetter" [p, pᗮ] true "the logical axiom, p. 22",
  entry "one" [𝟏] true "the rule 1, p. 22",
  entry "p26" [pᗮ, p ⊕ q] true "the two steps of p. 26 in the fragment",
  entry "p5with" [pᗮ ⅋ (p & p)] true "p. 5: A ⊸ A & A is derivable",
  entry "idTensor" [(p ⊗ q)ᗮ, p ⊗ q] true "the axiom at a compound formula",
  entry "tensorComm" [(p ⊗ q)ᗮ, q ⊗ p] true "1.9(ii): times is commutative",
  entry "tensorAssoc" [((p ⊗ q) ⊗ r)ᗮ, p ⊗ (q ⊗ r)] true "1.9(ii): times is associative",
  entry "tensorUnit" [(𝟏 ⊗ p)ᗮ, p] true "1.9(ii): 1 ⊗ G = G, one half",
  entry "tensorUnit'" [pᗮ, 𝟏 ⊗ p] true "1.9(ii): the other half",
  entry "parUnit" [(⊥ ⅋ p)ᗮ, p] true "1.9(ii): ⊥ ⅋ G = G, one half",
  entry "withProj" [(p & q)ᗮ, p] true "G & H ⊂ G",
  entry "plusInj" [pᗮ, p ⊕ q] true "G ⊂ G ⊕ H",
  entry "withUnit" [(⊤ & p)ᗮ, p] true "1.12(ii): ⊤ & G = G, one half",
  entry "distrib" [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] true "1.13(i), one half",
  entry "distrib'" [((p ⊗ q) ⊕ (p ⊗ r))ᗮ, p ⊗ (q ⊕ r)] true "1.13(i), the other half",
  entry "parDistrib" [(p ⅋ (q & r))ᗮ, (p ⅋ q) & (p ⅋ r)] true "1.13(i): ⅋ over &",
  entry "zeroAbsorbs" [(𝟎 ⊗ p)ᗮ, 𝟎] true "1.13(i): 0 ⊗ G = 0, one half",
  entry "topAbsorbs" [(⊤ ⅋ p)ᗮ, ⊤] true "1.13(i): ⊤ ⅋ G = ⊤, one half",
  entry "halfDistrib" [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)] true "1.13(ii)",
  entry "halfDistribPar" [((p ⅋ q) ⊕ (p ⅋ r))ᗮ, p ⅋ (q ⊕ r)] true "1.13(ii), for ⅋ and ⊕",
  entry "plusTwice" [p ⊕ pᗮ, p ⊕ pᗮ] true "two copies, used once each",
  entry "topSplit" [p, q, ⊤ ⊗ ⊤] true "⊤ takes any context, on either side of a ⊗",
  entry "topSlack" [p ⊗ ⊤, pᗮ, q, r] true "the ⊤ of the second premise takes what is left",
  entry "weakening" [𝟏, 𝟏] false "p. 22: weakening is forbidden",
  entry "weakening'" [𝟏, p, pᗮ] false "the same, by 1",
  entry "affine" [pᗮ ⅋ 𝟏] false "A ⊸ 1 would be weakening",
  entry "contraction" [p ⊕ pᗮ] false "p. 22: contraction is forbidden",
  entry "p5tensor" [pᗮ ⅋ (p ⊗ p)] false "p. 5: A ⊸ A ⊗ A is not derivable",
  entry "empty" [] false "no rule concludes the empty sequent",
  entry "zero" [𝟎] false "no rule for 0, p. 22",
  entry "zeroCtx" [𝟎, p] false "no rule for 0",
  entry "bot" [⊥] false "its premise would be the empty sequent",
  entry "letter" [p] false "a letter",
  entry "tensorDual" [p ⊗ pᗮ] false "A ⊗ A⊥",
  entry "mix" [p ⅋ pᗮ, q ⅋ qᗮ] false "the mix rule is not derivable",
  entry "halfDistribConv" [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] false "the converse of 1.13(ii)",
  entry "withTensor" [(p & q)ᗮ, p ⊗ q] false "G & H does not give G ⊗ H",
  entry "tensorWith" [(p ⊗ q)ᗮ, p & q] false "nor G ⊗ H, G & H"]

/-! ## Families that grow -/

/-- The letter numbered `n`. -/
def ltr (n : Nat) : Form := .atom n

/-- `⊢ p₀⊥, p₀ ⊗ p₁⊥, …, pₙ₋₁ ⊗ pₙ⊥, pₙ`: `n` tensors, each of which must
split the context in the one right way.  Derivable. -/
def chain (n : Nat) : List Form :=
  (ltr 0)ᗮ :: ((List.range n).map fun i => ltr i ⊗ (ltr (i + 1))ᗮ) ++ [ltr n]

/-- The same with the last letter changed: not derivable, and a search
must try everything to say so. -/
def chainBad (n : Nat) : List Form :=
  (ltr 0)ᗮ :: ((List.range n).map fun i => ltr i ⊗ (ltr (i + 1))ᗮ) ++ [ltr (n + 1)]

/-- `p₀ ⊗ (p₁ ⊗ (… ⊗ pₙ))`. -/
def bigTensor : Nat → Nat → Form
  | i, 0 => ltr i
  | i, n + 1 => ltr i ⊗ bigTensor (i + 1) n

/-- `⊢ p₀ ⊗ (p₁ ⊗ … ⊗ pₙ), pₙ⊥, …, p₀⊥`: one nest of tensors and a context
of `n + 1` letters, the first of which is wanted last.  Derivable. -/
def fan (n : Nat) : List Form :=
  bigTensor 0 n :: ((List.range (n + 1)).reverse.map fun i => (ltr i)ᗮ)

/-- The same with `p₀` in place of `p₀⊥`: not derivable. -/
def fanBad (n : Nat) : List Form :=
  bigTensor 0 n :: (((List.range n).reverse.map fun i => (ltr (i + 1))ᗮ) ++ [ltr 0])

/-- `p & p`, nested `n` deep. -/
def withs : Nat → Form
  | 0 => p
  | n + 1 => withs n & withs n

/-- `⊢ p⊥, (p & p) & …`: a derivation of `2ⁿ` axioms.  Derivable. -/
def withTree (n : Nat) : List Form := [pᗮ, withs n]

/-- `⊢ p₀ ⊗ ⊤, p₀⊥, p₁, …, pₙ`: the ⊤ takes `n` letters.  Derivable. -/
def slack (n : Nat) : List Form :=
  (ltr 0 ⊗ ⊤) :: (ltr 0)ᗮ :: ((List.range n).map fun i => ltr (i + 1))

/-- `⊢ ((p ⊗ q) & (p ⊗ r))⊥, p ⊗ (q & r)` beside `n` copies of ⊥: the
distribution that fails, so not derivable.  Its saturated set has
`17 (n + 1)` sequents, and a ⊗ in it stands beside up to `n` equal
formulas. -/
def bots (n : Nat) : List Form :=
  [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] ++ List.replicate n ⊥

/-- `⊥ ⅋ (⊥ ⅋ … ⅋ ⊥)`, `n + 1` times ⊥. -/
def parBot : Nat → Form
  | 0 => ⊥
  | n + 1 => ⊥ ⅋ parBot n

/-- The same sequent with the copies of ⊥ joined to its second formula by
⅋: `⊢ ((p ⊗ q) & (p ⊗ r))⊥, (p ⊗ (q & r)) ⅋ ⊥ ⅋ … ⅋ ⊥`.  Not derivable.
Its saturated set grows as the square of `n`. -/
def parBots : Nat → List Form
  | 0 => bots 0
  | n + 1 => [((p ⊗ q) & (p ⊗ r))ᗮ, (p ⊗ (q & r)) ⅋ parBot n]

/-- A family by its name: the sequent, and whether it is derivable. -/
def family : String → Nat → Option (List Form × Bool)
  | "chain", n => some (chain n, true)
  | "chainBad", n => some (chainBad n, false)
  | "fan", n => some (fan n, true)
  | "fanBad", n => some (fanBad n, false)
  | "withTree", n => some (withTree n, true)
  | "slack", n => some (slack n, true)
  | "bots", n => some (bots n, false)
  | "parbots", n => some (parBots n, false)
  | _, _ => none

end MALL.Corpus
