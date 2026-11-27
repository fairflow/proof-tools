import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
proto = open("Corpus/experiments/proto.lean.txt").read()
n = int(sys.argv[1])
d = defs(nochain(n)); N = d.count("⟹") - 2
B = {}
for off in sys.argv[2:]:
    B[f"depth log2 N + 1 - {off}"] = (f"def dd : Nat := Nat.log2 saturated.length + 1 - {off}\ndef D' : List Seq := saturated.map Fast.canon\n",
        "example : Fast.fastWith dd D' (Fast.build dd D') sequent = true := by decide +kernel")
B["no verification at the leaf (depth + 1)"] = ("def dd : Nat := Nat.log2 saturated.length + 1\ndef D' : List Seq := saturated.map Fast.canon\n" +
   "def hasT : Fast.BT → Nat → Bool\n  | .leaf xs, _ => !xs.isEmpty\n  | .node l r, k => bif Nat.beq (k % 2) 0 then hasT l (k / 2) else hasT r (k / 2)\n",
   "example : D'.all (Fast.satAtW Fast.insH (fun x => hasT (Fast.build dd D') (Fast.keyOf x.goal x.lin))) = true := by decide +kernel")
for name, (pre, b) in B.items():
    path = f"Corpus/out/exp/p3.lean"
    open(path, "w").write(d + proto + pre + "set_option profiler true\nset_option maxRecDepth 1000000\n" + b + "\nend DILL.Answer\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=170, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:200]
    print(f"N={N} {name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
