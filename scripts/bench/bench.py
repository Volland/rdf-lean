#!/usr/bin/env python3
"""Scaling benchmark for the LeanRDF tools.

Usage: scripts/bench/bench.py [--sizes 25,50,100,200] [--tools demo,owl,neg,check,classify,sparql,shacl]
                              [--timeout SECONDS] [--stages] [--out DIR] [--tsv FILE]
                              [--compare BASE.tsv] [--slow]

Generates inputs with scripts/bench/gen.py (deterministic), runs each tool on each size and
prints one row per run: tool, size, input triples (lines), wall seconds, exit code and peak
memory (MB). A run that exceeds the timeout is reported as TIMEOUT and larger sizes of that tool
are skipped. --stages also runs elpi's leanrdf-bench-stages for the demo rows and prints its
per-stage milliseconds. --compare adds the seconds of the same tool and size from an earlier
--tsv file, and the speedup.

The `robust` tool runs once, whatever the sizes: every case of the robust.tsv that
`gen.py robust` writes, each with the exit code, output text and time limit it must meet (cases
tagged slow only with --slow). Each case is one row, `ok` or `FAIL` and why; bench.py exits 1
when a case fails.

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
  parse     leanrdf-io-bench nt big.nt                      N-Triples parse into a graph (ms)
  sparqlnt  leanrdf-sparql on big.nt, one pattern            parse + graph + query, peak memory
  digest    leanrdf-io-bench digest ring.nt                 RDFC-1.0 on a blank-node ring (work limit)
  bnodes    leanrdf-io-bench digest bnodes.nt               RDFC-1.0 on N distinct blank nodes
  sg        leanrdf-sg check, kernel, quote, export, decode  statement records, summed
  robust    leanrdf-check on malformed input                exit codes, messages, time limits

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
    "parse": ("check", "leanrdf-io-bench"), "digest": ("check", "leanrdf-io-bench"),
    "bnodes": ("check", "leanrdf-io-bench"), "sparqlnt": ("sparql", "leanrdf-sparql"),
    "sg": ("statements", "leanrdf-sg"), "robust": ("check", "leanrdf-check"),
}
# input size per tool for a nominal size N (the SPARQL and SHACL tools are much faster)
SCALE = {"demo": 1, "owl": 0.5, "neg": 1, "check": 1, "big": 1, "checkbig": 1, "classify": 0.5,
         "sparql": 20, "shacl": 10, "parse": 1000, "sparqlnt": 1000, "digest": 5, "bnodes": 500,
         "sg": 40, "robust": 0}
KIND = {"demo": "rdfs", "owl": "owl", "neg": "rdfs", "check": "rdfs", "big": "rdfs", "checkbig": "rdfs",
        "classify": "el", "sparql": "sparql", "shacl": "shacl", "parse": "nt", "sparqlnt": "nt",
        "digest": "ring", "bnodes": "ring", "sg": "sg", "robust": "robust"}


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
    with open(path, errors="replace") as f:
        return sum(1 for l in f if l.strip() and not l.lstrip().startswith(("@prefix", "#")))


def load_base(path):
    """Seconds by (tool, size) from an earlier --tsv file."""
    base = {}
    with open(path) as f:
        for l in f:
            c = l.rstrip("\n").split("\t")
            if len(c) >= 4 and c[0] != "tool":
                base[(c[0], c[1])] = c[3]
    return base


def run_robust(d, timeout, slow):
    """Run every case of d/robust.tsv; one row per case and whether all passed."""
    rows, ok_all = [], True
    with open(os.path.join(d, "robust.tsv")) as f:
        cases = [l.rstrip("\n").split("\t") for l in f if l.strip()]
    for name, tool, args, code, text, limit, tag in cases:
        if tag == "slow" and not slow:
            continue
        dt, got, mb, out = run([binpath(tool)] + args.split(), d, max(timeout, float(limit)))
        why = []
        if dt is None:
            why.append("timeout")
        else:
            if str(got) != code:
                why.append(f"exit {got}, expected {code}")
            if text != "-" and text not in out:
                why.append(f"output lacks {text!r}: {out[:200]!r}")
            if dt > float(limit):
                why.append(f"took {dt:.2f}s, limit {limit}s")
            if len(out) > 100000:
                why.append(f"output of {len(out)} characters")
        ok_all = ok_all and not why
        secs = "TIMEOUT" if dt is None else f"{dt:.2f}"
        rows.append((f"robust:{name}", secs, got, mb, "ok" if not why else "FAIL " + "; ".join(why)))
    return rows, ok_all


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="25,50,100,200")
    ap.add_argument("--tools", default="demo,owl,neg,check,classify,sparql,shacl")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--stages", action="store_true")
    ap.add_argument("--out", default=None, help="keep generated inputs here")
    ap.add_argument("--tsv", default=None, help="also write the rows to this file")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--compare", default=None, help="an earlier --tsv file to compare with")
    ap.add_argument("--slow", action="store_true", help="also run robust cases tagged slow")
    a = ap.parse_args()
    base = load_base(a.compare) if a.compare else None
    failed = False
    tools = a.tools.split(",")
    sizes = [int(s) for s in a.sizes.split(",")]
    if not a.no_build:
        build(tools + (["stages"] if a.stages else []))
    work = a.out or tempfile.mkdtemp(prefix="leanrdf-bench-")
    rows = []
    print(f"# inputs in {work}")
    print("tool\tN\tinput\tseconds\texit\tpeakMB" + ("\tbase\tspeedup" if base else ""))

    def emit(tool, size, inp, secs, code, mb, note=""):
        row = f"{tool}\t{size}\t{inp}\t{secs}\t{code}\t{mb:.0f}"
        rows.append(row)
        if base is not None:
            b = base.get((tool, str(size)), "-")
            try:
                row += f"\t{b}\t{float(b) / max(float(secs), 0.005):.1f}x"
            except ValueError:
                row += f"\t{b}\t-"
        print(row + (f"\t{note}" if note else ""), flush=True)

    for tool in tools:
        if tool == "robust":
            d = os.path.join(work, "robust")
            if not os.path.isdir(d):
                subprocess.run([sys.executable, GEN, "robust", "0", d], check=True)
            rrows, ok = run_robust(d, a.timeout, a.slow)
            failed = failed or not ok
            for name, secs, code, mb, note in rrows:
                emit(name, 0, "-", secs, code, mb, note)
            continue
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
            elif tool == "parse":
                cmds, inp = [[b, "nt", "big.nt"]], "big.nt"
            elif tool == "sparqlnt":
                cmds = [[b, "query", "--location", "big.nt", "--query",
                         open(os.path.join(d, "q.rq")).read(), "--results-format", "tsv"]]
                inp = "big.nt"
            elif tool == "digest":
                cmds, inp = [[b, "digest", "ring.nt"]], "ring.nt"
            elif tool == "bnodes":
                cmds, inp = [[b, "digest", "bnodes.nt"]], "bnodes.nt"
            elif tool == "sg":
                if not os.path.exists(os.path.join(d, "history.nt")):
                    with open(os.path.join(d, "history.nt"), "w") as f:
                        subprocess.run([b, "export", "records.jsonl", "--history"], cwd=d, stdout=f)
                cmds = [[b, "check", "records.jsonl"], [b, "kernel", "records.jsonl"],
                        [b, "quote", "records.jsonl"], [b, "export", "records.jsonl", "--history"],
                        [b, "decode", "history.nt", "--history"]]
                inp = "records.jsonl"
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
            emit(tool, size, lines(os.path.join(d, inp)), secs, code, mb)
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
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
