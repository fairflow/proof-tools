/-
The producer of saturated sets in numbers (`MALL/Coded.lean`).

Code: nothing here is trusted, and the file has no bound on axioms.  The
kernel checks what `encode` returns (`codeRefutes`).
-/
import MALL.Coded
import MALL.Refute

namespace MALL

instance : Inhabited Tree := ⟨.leaf⟩

namespace Encode

/-- A formula and the formulas it is built of. -/
def subs : Form → List Form
  | .tensor A C => .tensor A C :: (subs A ++ subs C)
  | .par A C => .par A C :: (subs A ++ subs C)
  | .wth A C => .wth A C :: (subs A ++ subs C)
  | .plus A C => .plus A C :: (subs A ++ subs C)
  | X => [X]

/-- A tree in order from a sorted array, of the least depth. -/
partial def build (a : Array Nat) (lo hi : Nat) : Tree :=
  if lo ≥ hi then .leaf
  else
    let m := (lo + hi) / 2
    .node (build a lo m) a[m]! (build a (m + 1) hi)

/-- The least power of two that is at least `n`. -/
partial def pow2 (n : Nat) (b : Nat := 4) : Nat := if b ≥ n then b else pow2 n (2 * b)

/-- **A set of sequents, in numbers**: the table lists every formula of
the set and its parts, larger formulas first; the base is a power of two
that exceeds every multiplicity by 3. -/
def encode (D : List (List Form)) (Γ : List Form) : CodeCert := Id.run do
  let mut seen : Std.HashMap Form Unit := {}
  for d in Γ :: D do
    for X in d do
      for Y in subs X do
        seen := seen.insert Y ()
  let tab := (seen.toArray.map (·.1)).qsort fun X Y =>
    X.size > Y.size || (X.size == Y.size && compare X Y == .lt)
  let mut idx : Std.HashMap Form Nat := {}
  for h : i in [0:tab.size] do
    idx := idx.insert tab[i] i
  let at' (X : Form) : Nat := idx.getD X 0
  let table := (List.range tab.size).map fun i =>
    let off (X : Form) : Nat := at' X - (i + 1)
    match tab.getD i .one with
    | .atom a => Node.atom a
    | .natom a => .natom a
    | .one => .one
    | .bot => .bot
    | .top => .top
    | .zero => .zero
    | .tensor A C => .tensor (off A) (off C)
    | .par A C => .par (off A) (off C)
    | .wth A C => .wth (off A) (off C)
    | .plus A C => .plus (off A) (off C)
  let most := (Γ :: D).foldl (fun m d => d.foldl (fun m X => max m (d.count X)) m) 0
  let B := if (most + 3) % 2 == 1 then most + 3 else most + 4
  let code (d : List Form) : Nat := d.foldl (fun c X => c + B ^ at' X) 0
  let keys := ((Γ :: D).map code).toArray.qsort (· < ·)
  let keys := keys.foldl (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
  return { B, table, tree := build keys 0 keys.size, goal := Γ.map at' }

/-- The tree as Lean source. -/
partial def showTree : Tree → String
  | .leaf => ".leaf"
  | .node .leaf k .leaf => s!"(.node .leaf {k} .leaf)"
  | .node l k r => s!"(.node {showTree l} {k} {showTree r})"

def showNode : Node → String
  | .atom a => s!".atom {a}"
  | .natom a => s!".natom {a}"
  | .one => ".one"
  | .bot => ".bot"
  | .top => ".top"
  | .zero => ".zero"
  | .tensor a c => s!".tensor {a} {c}"
  | .par a c => s!".par {a} {c}"
  | .wth a c => s!".wth {a} {c}"
  | .plus a c => s!".plus {a} {c}"

/-- A tree cut at a depth, for a check stated in parts: the top of the
tree as source with the subtrees below it named `part0`, `part1`, …; those
subtrees; the numbers of the top; and the proof, as source, that every
number passes, from theorems `part0_ok`, … and `key0_ok`, … -/
partial def cut : Nat → Tree → StateM (Array Tree × Array Nat) (String × String)
  | _, .leaf => pure (".leaf", "rfl")
  | 0, t => do
    let i := (← get).1.size
    modify fun (ts, ks) => (ts.push t, ks)
    pure (s!"part{i}", s!"part{i}_ok")
  | d + 1, .node l k r => do
    let (sl, pl) ← cut d l
    let j := (← get).2.size
    modify fun (ts, ks) => (ts, ks.push k)
    let (sr, pr) ← cut d r
    pure (s!"(.node {sl} {k} {sr})", s!"(Tree.all_node {pl} key{j}_ok {pr})")

/-- The certificate with the tree given as source. -/
def showCertWith (C : CodeCert) (tree : String) : String :=
  "{ B := " ++ toString C.B ++ "\n    table := [" ++ ", ".intercalate (C.table.map showNode) ++
  "]\n    goal := " ++ toString C.goal ++ "\n    tree := " ++ tree ++ " }"

/-- The certificate as Lean source. -/
def showCert (C : CodeCert) : String :=
  "{ B := " ++ toString C.B ++ "\n    table := [" ++ ", ".intercalate (C.table.map showNode) ++
  "]\n    goal := " ++ toString C.goal ++ "\n    tree := " ++ showTree C.tree ++ " }"

end Encode

end MALL
