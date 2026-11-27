import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
proto = open("Corpus/experiments/proto.lean.txt").read()
which = sys.argv[1]
for n in [int(a) for a in sys.argv[2:]]:
    d = defs(nochain(n)); N = d.count("⟹") - 2
    body = {"fast": "example : Fast.refutedFast saturated sequent = true := by decide +kernel",
            "agree": "#eval (Fast.refutedFast saturated sequent, refutedBy saturated sequent)"}[which]
    path = f"Corpus/out/exp/p1.lean"
    open(path, "w").write(d + proto + "set_option profiler true\nset_option maxRecDepth 1000000\n" + body + "\nend DILL.Answer\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=170, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l or "(" in l)[:200]
    print(f"n={n} N={N} {which}: exit {code}, {dt:.1f} s, peak {mb:.0f} MB | {prof}", flush=True)
