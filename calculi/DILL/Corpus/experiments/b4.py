import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
pre = '''import DILL.Corpus.Basic
open DILL DILL.Corpus
def beqF : Form → Form → Bool
  | .atom m, .atom n => Nat.beq m n
  | .one, .one => true | .top, .top => true | .zero, .zero => true
  | .tensor a b, .tensor c d => beqF a c && beqF b d
  | .lolli a b, .lolli c d => beqF a c && beqF b d
  | .wth a b, .wth c d => beqF a c && beqF b d
  | .plus a b, .plus c d => beqF a c && beqF b d
  | .bang a, .bang c => beqF a c
  | _, _ => false
def hashF : Form → Nat
  | .atom n => (n * 2654435761 + 97) % 4294967296
  | .one => 3 | .top => 5 | .zero => 7
  | .tensor A B => (hashF A * 1000003 + hashF B * 8191 + 11) % 4294967296
  | .lolli A B => (hashF A * 1000003 + hashF B * 8191 + 13) % 4294967296
  | .wth A B => (hashF A * 1000003 + hashF B * 8191 + 17) % 4294967296
  | .plus A B => (hashF A * 1000003 + hashF B * 8191 + 19) % 4294967296
  | .bang A => (hashF A * 1000003 + 23) % 4294967296
def eraseB (x : Form) : List Form → List Form
  | [] => []
  | a :: l => bif beqF a x then l else a :: eraseB x l
def eraseH (x : Form) : List Form → List Form
  | [] => []
  | a :: l => bif Nat.beq (hashF a) (hashF x) && decide (a = x) then l else a :: eraseH x l
def zone : List Form := links 128
def lens : List Form → Nat → Nat
  | [], n => n
  | _ :: l, n => lens l (n + 1)
def allB : List Nat → (Nat → Bool) → Bool
  | [], _ => true
  | a :: l, p => p a && allB l p
set_option profiler true
set_option maxRecDepth 1000000
'''
T = {
 "32 x the zone only walked (length)": "example : allB (List.range 32) (fun i => Nat.ble (lens (zone.drop 0) i) 1000) = true := by decide +kernel",
 "32 x List.erase of a late formula (derived equality)": "example : allB (List.range 32) (fun i => Nat.ble (lens (zone.erase (ltr (96 + i) ⊸ ltr (97 + i))) 0) 1000) = true := by decide +kernel",
 "32 x erase with a hand-written equality": "example : allB (List.range 32) (fun i => Nat.ble (lens (eraseB (ltr (96 + i) ⊸ ltr (97 + i)) zone) 0) 1000) = true := by decide +kernel",
 "32 x erase with the hashes compared first": "example : allB (List.range 32) (fun i => Nat.ble (lens (eraseH (ltr (96 + i) ⊸ ltr (97 + i)) zone) 0) 1000) = true := by decide +kernel",
}
for name, t in T.items():
    path = "Corpus/out/exp/b4.lean"
    open(path, "w").write(pre + t + "\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=100, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:160]
    print(f"{name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
