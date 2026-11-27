import sys, subprocess; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
for n in [int(a) for a in sys.argv[1:]]:
    subprocess.run([".lake/build/bin/dillrun", "cert", "focus", "chain", str(n), "0"], capture_output=True, text=True)
    src = open(f"Corpus/out/run/chain_{n}_focus_tree.lean").read()
    path = f"Corpus/out/exp/t1_{n}.lean"
    open(path, "w").write(src.replace("set_option maxRecDepth", "set_option profiler true\nset_option maxRecDepth", 1))
    code, dt, mb, lines = lean(path, mem=4000, deadline=150, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:200]
    # the permutation test alone, once, at the full zone
    p2 = f"Corpus/out/exp/t1p_{n}.lean"
    open(p2, "w").write(f"import DILL.Corpus.Basic\nopen DILL DILL.Corpus\nset_option profiler true\nset_option maxRecDepth 100000 in\nexample : permB (chain {n}).lin (chain {n}).lin = true := by decide +kernel\n")
    c2, d2, m2, l2 = lean(p2, mem=4000, deadline=150, show=12)
    prof2 = "; ".join(l.strip() for l in l2 if "took" in l or "error" in l)[:120]
    print(f"chain {n}: the fact: exit {code}, {dt:.1f} s, peak {mb:.0f} MB | {prof} || one permB at the root zone: {prof2}, peak {m2:.0f} MB", flush=True)
