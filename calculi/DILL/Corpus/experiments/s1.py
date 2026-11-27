import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
import time, subprocess
for n in [int(a) for a in sys.argv[1:]]:
    t = time.time()
    a = answer(nochain(n), deadline=120)
    tp = time.time() - t
    N = a.count("⟹") - 2
    path = f"Corpus/out/exp/s1_{n}.lean"
    open(path, "w").write(a.replace("import DILL.Engine", "import DILL.Engine\nset_option profiler true", 1))
    code, dt, mb, lines = lean(path, mem=4000, deadline=170, show=14)
    prof = "; ".join(l.strip() for l in lines if "type checking took" in l or "error" in l or "elaboration took" in l)[:260]
    print(f"links {n}: set of {N}; the command {tp:.2f} s; the file: exit {code}, {dt:.1f} s, peak {mb:.0f} MB | {prof}", flush=True)
