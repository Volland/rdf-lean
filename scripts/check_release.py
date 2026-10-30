#!/usr/bin/env python3
"""Checks the release contract of LeanRDF (OpenSpec capability `release`).

Offline checks (run in CI): licence files and README, package metadata in both lakefiles, the
CI workflow's jobs and the Pages workflow's action versions. With `--online` it also asks GitHub,
through `gh`, that the repository is public, that the latest CI run on `main` succeeded and that
the `v0.1.0` release exists.
Usage: python3 scripts/check_release.py [--online]
"""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPO = "Volland/rdf-lean"
VERSION = "0.1.0"
LICENCE = "MIT OR Apache-2.0"
# The first major version of each action that runs on Node 24, not Node 20.
NODE24 = {"actions/checkout": 5, "actions/setup-python": 6, "actions/upload-pages-artifact": 4,
          "actions/deploy-pages": 5}

def read(rel):
    return (ROOT / rel).read_text(encoding="utf-8")

# @tg: verifies:: [[openspec:release#Licence#Licence files and metadata]] {level: integration}
def check_licence():
    errs = [f"missing {f}" for f in ("LICENSE-MIT", "LICENSE-APACHE") if not (ROOT / f).exists()]
    if "[MIT licence](LICENSE-MIT)" not in read("README.md"):
        errs.append("README does not name the dual licence")
    for lf in ("lakefile.lean", "elpi/lakefile.lean"):
        if f'license := "{LICENCE}"' not in read(lf):
            errs.append(f"{lf} does not declare {LICENCE}")
    return errs

# @tg: verifies:: [[openspec:release#Package metadata#Version is 0.1.0]] {level: integration}
def check_metadata():
    errs = []
    for lf in ("lakefile.lean", "elpi/lakefile.lean"):
        s = read(lf)
        if f'version := v!"{VERSION}"' not in s:
            errs.append(f"{lf}: version is not {VERSION}")
        for field in ("description", "keywords", "homepage"):
            if not re.search(rf"^\s*{field} :=", s, re.M):
                errs.append(f"{lf}: no {field}")
    return errs

# The workflow itself is .github/workflows/ci.yaml; tg does not read YAML, so the contract it
# must keep is enforced (and annotated) here.
# @tg: implements:: [[openspec:release#Continuous integration]] {note: "enforces .github/workflows/ci.yaml"}
# @tg: verifies:: [[openspec:release#Continuous integration#CI runs both packages]] {level: integration}
def check_ci_workflow():
    s, errs = read(".github/workflows/ci.yaml"), []
    for needle in ("branches: [main]", "pull_request:", "leanprover/lean-action@v1",
                   "lake-package-directory: elpi", "test: true",
                   "lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt"):
        if needle not in s:
            errs.append(f"ci.yaml lacks `{needle}`")
    return errs

# @tg: verifies:: [[openspec:release#Continuous integration#Pages actions off Node 20]] {level: integration}
def check_pages_actions():
    errs = []
    for action, major in re.findall(r"uses: ([\w/-]+)@v(\d+)", read(".github/workflows/pages.yml")):
        if action in NODE24 and int(major) < NODE24[action]:
            errs.append(f"pages.yml: {action}@v{major} still runs on Node 20")
    return errs

def gh(*args):
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=True).stdout

# @tg: implements:: [[openspec:release#Tagged public release]] {note: "checks the release made with gh"}
# @tg: verifies:: [[openspec:release#Tagged public release#Release exists]] {level: e2e}
def check_online():
    errs = []
    if json.loads(gh("repo", "view", REPO, "--json", "visibility"))["visibility"] != "PUBLIC":
        errs.append("the repository is not public")
    runs = json.loads(gh("run", "list", "-R", REPO, "--workflow", "CI", "--branch", "main",
                         "--limit", "1", "--json", "conclusion,status"))
    if not runs or runs[0]["conclusion"] != "success":
        errs.append(f"the latest CI run on main is not green: {runs}")
    try:
        tag = json.loads(gh("release", "view", f"v{VERSION}", "-R", REPO, "--json", "tagName"))["tagName"]
        if tag != f"v{VERSION}":
            errs.append(f"release tag is {tag}")
    except subprocess.CalledProcessError:
        errs.append(f"no v{VERSION} release")
    return errs

def main():
    checks = [check_licence, check_metadata, check_ci_workflow, check_pages_actions]
    if "--online" in sys.argv:
        checks.append(check_online)
    errs = [e for c in checks for e in c()]
    for e in errs:
        print("FAIL", e)
    print("release contract:", "ok" if not errs else f"{len(errs)} problem(s)")
    return 1 if errs else 0

if __name__ == "__main__":
    sys.exit(main())
