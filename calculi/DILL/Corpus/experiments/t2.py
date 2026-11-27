import sys, subprocess, re; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
def rev(m):
    items = m.group(2).split(", ")
    return m.group(1) + "[" + ", ".join(reversed(items)) + "])"
for n in [int(a) for a in sys.argv[1:]]:
    subprocess.run([".lake/build/bin/dillrun", "cert", "focus", "chain", str(n), "0"], capture_output=True, text=True)
    src = open(f"Corpus/out/run/chain_{n}_focus_tree.lean").read()
    src2 = re.sub(r"(\(\.lolliL [^\[\]]*)\[([^\[\]]+)\]\)", rev, src)
    for name, text in (("as the search writes it", src), ("the part named in the order of the zone", src2)):
        path = f"Corpus/out/exp/t2.lean"
        open(path, "w").write(text.replace("set_option maxRecDepth", "set_option profiler true\nset_option maxRecDepth", 1))
        code, dt, mb, lines = lean(path, mem=4000, deadline=150, show=12)
        prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:200]
        print(f"chain {n}, {name}: exit {code}, {dt:.1f} s, peak {mb:.0f} MB | {prof}", flush=True)
