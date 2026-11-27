import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
pre = '''import DILL.Corpus.Basic
open DILL DILL.Corpus
def beqF : Form → Form → Bool
  | .atom m, .atom n => m == n
  | .one, .one => true | .top, .top => true | .zero, .zero => true
  | .tensor a b, .tensor c d => beqF a c && beqF b d
  | .lolli a b, .lolli c d => beqF a c && beqF b d
  | .wth a b, .wth c d => beqF a c && beqF b d
  | .plus a b, .plus c d => beqF a c && beqF b d
  | .bang a, .bang c => beqF a c
  | _, _ => false
def f (i : Nat) : Form := (.atom i ⊸ .atom (i + 1)) ⊗ !(.atom 3 ⊕ .atom i)
def zone (n : Nat) : List Form := (List.range n).map fun i => Form.atom i ⊸ .atom (i + 1)
def permE : List Form → List Form → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => l₂.contains a && permE l₁ (l₂.erase a)
set_option profiler true
set_option maxRecDepth 100000
'''
T = {
 "2000 derived decEq, equal formulas of 9 signs": "example : (List.range 2000).all (fun i => decide (f i = f i)) = true := by decide +kernel",
 "2000 hand-written beq, the same": "example : (List.range 2000).all (fun i => beqF (f i) (f i)) = true := by decide +kernel",
 "2000 derived decEq, unequal at the root": "example : (List.range 2000).all (fun i => !decide (f i = !(f i))) = true := by decide +kernel",
 "2000 hand-written beq, unequal at the root": "example : (List.range 2000).all (fun i => !beqF (f i) (!(f i))) = true := by decide +kernel",
 "permB on a zone of 32, same order": "example : permB (zone 32) (zone 32) = true := by decide +kernel",
 "permE (erase) on a zone of 32, same order": "example : permE (zone 32) (zone 32) = true := by decide +kernel",
 "permE (erase) on a zone of 32, reversed": "example : permE (zone 32) (zone 32).reverse = true := by decide +kernel",
 "length of sub: 32 taken out of 32": "example : ((sub (zone 32) (zone 32)).length + (zone 32).length == (zone 32).length) = true := by decide +kernel",
}
for name, t in T.items():
    path = "Corpus/out/exp/b1.lean"
    open(path, "w").write(pre + t + "\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=100, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:160]
    print(f"{name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
