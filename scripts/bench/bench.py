#!/usr/bin/env python3
"""Scaling benchmark for the LeanRDF tools.

Usage: scripts/bench/bench.py [--sizes 25,50,100,200] [--tools demo,owl,neg,check,classify,sparql,shacl]
                              [--timeout SECONDS] [--stages] [--out DIR] [--tsv FILE]

Generates inputs with scripts/bench/gen.py (deterministic), runs each tool on each size and
prints one row per run: tool, size, input triples (lines), wall seconds, exit code and peak
memory (MB). A run that exceeds the timeout is reported as TIMEOUT and larger sizes of that tool
are skipped. --stages also runs elpi's leanrdf-bench-stages for the demo rows and prints its
per-stage milliseconds.

Tools (binaries are built first with `lake build <exe>` in their package):
  demo      leanrdf-demo data.nt q.nt                       RDFS entailment, certificate checked
  owl       leanrdf-demo data.nt q.nt --profile owl         OWL 2 RL entailment
  neg       leanrdf-demo data.nt q-neg.nt                   not derived: RDFS countermodel
  check     leanrdf-check --data --query --cert             trusted check of a saved certificate
  big       leanrdf-demo data.nt q-all.nt --cert            N ground goals: certify + check scale
  checkbig  leanrdf-check on the certificate of `big`       trusted check of a ~3N-node certificate
  classify  leanrdf-classify onto.ttl                       certified EL classification
  sparql    leanrdf-sparql query (two queries, summed)       proven evaluator
  shacl     leanrdf-shacl validate                          proven validator

Sizes are scaled per tool (see SCALE) so that one --sizes list exercises every tool. Only the
Python standard library is used; the tools themselves are Lean and Elpi only.
"""
import argparse
import os
import subprocess
import sys
import tempfile
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
GEN = os.path.join(ROOT, "scripts", "bench", "gen.py")

BINS = {
    "demo": ("elpi", "leanrdf-demo"), "owl": ("elpi", "leanrdf-demo"), "neg": ("elpi", "leanrdf-demo"),
    "big": ("elpi", "leanrdf-demo"), "checkbig": ("check", "leanrdf-check"),
    "classify": ("elpi", "leanrdf-classify"), "check": ("check", "leanrdf-check"),
    "sparql": ("sparql", "leanrdf-sparql"), "shacl": ("shacl", "leanrdf-shacl"),
    "stages": ("elpi", "leanrdf-bench-stages"),
}
# input size per tool for a nominal size N (the SPARQL and SHACL tools are much faster)
SCALE = {"demo": 1, "owl": 0.5, "neg": 1, "check": 1, "big": 1, "checkbig": 1, "classify": 0.5,
         "sparql": 20, "shacl": 10}
KIND = {"demo": "rdfs", "owl": "owl", "neg": "rdfs", "check": "rdfs", "big": "rdfs", "checkbig": "rdfs",
        "classify": "el", "sparql": "sparql", "shacl": "shacl"}


def binpath(tool):
    pkg, exe = BINS[tool]
    return os.path.join(ROOT, pkg, ".lake", "build", "bin", exe)


def build(tools):
    done = set()
    for t in tools:
        pkg, exe = BINS[t]
        if (pkg, exe) in done:
            continue
        done.add((pkg, exe))
        r = subprocess.run(["lake", "build", exe], cwd=os.path.join(ROOT, pkg),
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            sys.exit(f"build of {pkg}:{exe} failed:\n{r.stderr[-2000:]}")


def run(cmd, cwd, timeout):
    """Run cmd; (seconds, exit code, peak RSS in MB of this child, output) or (None, "TIMEOUT", ...)."""
    with tempfile.TemporaryFile("w+") as out:
        t0 = time.monotonic()
        p = subprocess.Popen(cmd, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if time.monotonic() - t0 > timeout:
                p.kill()
                os.wait4(p.pid, 0)
                return None, "TIMEOUT", 0, ""
            time.sleep(0.005)
        dt = time.monotonic() - t0
        p.returncode = os.waitstatus_to_exitcode(status)
        # ru_maxrss: bytes on macOS, KiB on Linux
        mb = ru.ru_maxrss / (1 << 20 if sys.platform == "darwin" else 1 << 10)
        out.seek(0)
        return dt, p.returncode, mb, out.read()


def lines(path):
    with open(path) as f:
        return sum(1 for l in f if l.strip() and not l.lstrip().startswith(("@prefix", "#")))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="25,50,100,200")
    ap.add_argument("--tools", default="demo,owl,neg,check,classify,sparql,shacl")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--stages", action="store_true")
    ap.add_argument("--out", default=None, help="keep generated inputs here")
    ap.add_argument("--tsv", default=None, help="also write the rows to this file")
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()
    tools = a.tools.split(",")
    sizes = [int(s) for s in a.sizes.split(",")]
    if not a.no_build:
        build(tools + (["stages"] if a.stages else []))
    work = a.out or tempfile.mkdtemp(prefix="leanrdf-bench-")
    rows = []
    print(f"# inputs in {work}")
    print("tool\tN\tinput\tseconds\texit\tpeakMB")
    for tool in tools:
        for n in sizes:
            size = max(2, int(n * SCALE[tool]))
            d = os.path.join(work, f"{KIND[tool]}-{size}")
            if not os.path.isdir(d):
                subprocess.run([sys.executable, GEN, KIND[tool], str(size), d], check=True)
            b = binpath(tool)
            if tool == "demo":
                cmds, inp = [[b, "data.nt", "q.nt", "--cert", "cert.json"]], "data.nt"
            elif tool == "owl":
                cmds, inp = [[b, "data.nt", "q.nt", "--profile", "owl"]], "data.nt"
            elif tool == "neg":
                cmds, inp = [[b, "data.nt", "q-neg.nt"]], "data.nt"
            elif tool == "check":
                if not os.path.exists(os.path.join(d, "cert.json")):
                    subprocess.run([binpath("demo"), "data.nt", "q.nt", "--cert", "cert.json"], cwd=d,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                cmds, inp = [[b, "--data", "data.nt", "--query", "q.nt", "--cert", "cert.json"]], "data.nt"
            elif tool == "big":
                cmds, inp = [[b, "data.nt", "q-all.nt", "--cert", "cert-all.json"]], "data.nt"
            elif tool == "checkbig":
                if not os.path.exists(os.path.join(d, "cert-all.json")):
                    subprocess.run([binpath("big"), "data.nt", "q-all.nt", "--cert", "cert-all.json"], cwd=d,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                cmds, inp = [[b, "--data", "data.nt", "--query", "q-all.nt", "--cert", "cert-all.json"]], "data.nt"
            elif tool == "classify":
                cmds, inp = [[b, "onto.ttl"]], "onto.ttl"
            elif tool == "sparql":
                cmds = [[b, "query", "--location", "data.ttl", "--query", open(os.path.join(d, q)).read(),
                         "--results-format", "tsv"] for q in ("q1.rq", "q2.rq")]
                inp = "data.ttl"
            else:
                cmds, inp = [[b, "validate", "--data", "data.ttl", "--shapes", "shapes.ttl"]], "data.ttl"
            total, code, mb = 0.0, 0, 0.0
            for c in cmds:
                dt, code, m, out = run(c, d, a.timeout)
                if dt is None:
                    total = None
                    break
                total += dt
                mb = max(mb, m)
            secs = "TIMEOUT" if total is None else f"{total:.2f}"
            row = f"{tool}\t{size}\t{lines(os.path.join(d, inp))}\t{secs}\t{code}\t{mb:.0f}"
            rows.append(row)
            print(row, flush=True)
            if a.stages and tool in ("demo", "owl", "neg") and total is not None:
                extra = {"demo": [], "owl": ["--profile", "owl"], "neg": ["--countermodel"]}[tool]
                q = "q-neg.nt" if tool == "neg" else "q.nt"
                _, _, _, out = run([binpath("stages"), "data.nt", q] + extra, d, a.timeout)
                for l in out.splitlines():
                    if "\t" in l:
                        print(f"  stage\t{tool}\t{size}\t{l}", flush=True)
            if total is None:
                break
    if a.tsv:
        with open(a.tsv, "w") as f:
            f.write("tool\tN\tinput\tseconds\texit\tpeakMB\n" + "\n".join(rows) + "\n")


if __name__ == "__main__":
    main()
