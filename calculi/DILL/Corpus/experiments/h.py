"""Harness: elaborate a Lean file under a memory cap and a deadline that
ends the process group; report time, exit, peak memory, first lines."""
import subprocess, os, signal, sys, time, resource
def lean(path, mem=4000, deadline=120.0, show=6):
    p = subprocess.Popen(["/usr/bin/time", "-l", "lake", "env", "lean", "-M", str(mem), path],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    t = time.time()
    try:
        out, err = p.communicate(timeout=deadline); code = p.returncode
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, err = p.communicate(); code = None
    dt = time.time() - t
    rss = [l for l in err.splitlines() if "maximum resident" in l]
    mb = int(rss[0].split()[0]) / 1e6 if rss else -1
    lines = [l for l in (out + err).splitlines() if l.strip() and "maximum resident" not in l and not l.startswith("  ")][:show]
    return code, dt, mb, lines
def nochain(n):
    return ", ".join(["a4"] + ["a%d -o a%d" % (i, i + 1) for i in range(4, 4 + n)]) + " => a%d" % (5 + n)
def answer(text, deadline=60):
    r = subprocess.run([".lake/build/bin/dillrun", "prove", "--deadline=%d" % deadline, text], capture_output=True, text=True)
    return r.stdout
def defs(text):
    """The printed file up to and including the set, without the facts."""
    a = answer(text)
    return a[:a.index("/-- The kernel computes the check")]
