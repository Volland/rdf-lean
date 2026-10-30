#!/usr/bin/env python3
"""Static site generator for the LeanRDF site (standard library only).

Reads site/content (home.html, book/*.md, docs/*.md, *.md pages, each Markdown file with a small front
matter) and writes _site/ for GitHub Pages; the Pages workflow publishes that directory.
Usage: python3 site/build.py
"""
import html, re, shutil, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "site" / "content"
OUT = ROOT / "_site"
BASE = "/rdf-lean"  # GitHub Pages project path
REPO = "https://github.com/Volland/rdf-lean"

# ---------------------------------------------------------------- markdown
def inline(s: str) -> str:
    codes = []
    def keep(m):
        codes.append("<code>" + html.escape(m.group(1)) + "</code>")
        return f"\x00{len(codes)-1}\x00"
    s = re.sub(r"`([^`]+)`", keep, s)
    s = html.escape(s, quote=False)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    s = re.sub(r"(?<![\w*])\*([^*\s][^*]*)\*(?!\w)", r"<em>\1</em>", s)
    def link(m):
        href = m.group(2)
        if href.startswith("/"):
            href = BASE + href
        return f'<a href="{href}">{m.group(1)}</a>'
    s = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", link, s)
    return re.sub(r"\x00(\d+)\x00", lambda m: codes[int(m.group(1))], s)

LEAN_KW = ("def|theorem|lemma|structure|inductive|where|match|with|fun|by|example|open|namespace|end|"
           "import|let|if|then|else|do|return|partial|private|abbrev|instance|deriving|mutual|show|"
           "have|exact|intro|obtain|rcases|cases|induction|simp|rw|refine|decide|native_decide")

def lean(code: str) -> str:
    """A light highlighter: comments, strings and keywords."""
    out = []
    for line in code.split("\n"):
        comment = ""
        idx = line.find("--")
        if idx >= 0 and line[:idx].count('"') % 2 == 0:
            line, comment = line[:idx], line[idx:]
        parts = re.split(r'("(?:[^"\\]|\\.)*")', line)
        buf = []
        for i, part in enumerate(parts):
            esc = html.escape(part, quote=False)
            if i % 2:
                buf.append(f'<span class="s">{esc}</span>')
            else:
                esc = re.sub(rf"(?<![\w.#])(#guard|#eval|#print|{LEAN_KW})(?![\w'?!])",
                             r'<span class="k">\1</span>', esc)
                buf.append(esc)
        if comment:
            buf.append(f'<span class="c">{html.escape(comment, quote=False)}</span>')
        out.append("".join(buf))
    return "\n".join(out)

def md(text: str) -> str:
    out, lines, i = [], text.split("\n"), 0
    para = []
    def flush():
        if para:
            out.append("<p>" + inline(" ".join(para)) + "</p>")
            para.clear()
    while i < len(lines):
        ln = lines[i]
        if ln.startswith("```"):
            flush()
            lang = ln[3:].strip()
            i += 1
            buf = []
            while i < len(lines) and not lines[i].startswith("```"):
                buf.append(lines[i]); i += 1
            body = lean("\n".join(buf)) if lang == "lean" else html.escape("\n".join(buf))
            cls = f' class="language-{lang}"' if lang else ""
            out.append(f"<pre><code{cls}>{body}</code></pre>")
        elif re.match(r"#{1,4} ", ln):
            flush()
            n = len(ln) - len(ln.lstrip("#"))
            title = ln[n + 1:]
            slug = re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")
            out.append(f'<h{n} id="{slug}">{inline(title)}</h{n}>')
        elif re.match(r"\s*[-*] ", ln):
            flush()
            items = []
            while i < len(lines) and re.match(r"\s*[-*] ", lines[i]):
                items.append(inline(re.sub(r"^\s*[-*] ", "", lines[i]))); i += 1
            i -= 1
            out.append("<ul>" + "".join(f"<li>{x}</li>" for x in items) + "</ul>")
        elif re.match(r"\d+\. ", ln):
            flush()
            items = []
            while i < len(lines) and re.match(r"\d+\. ", lines[i]):
                items.append(inline(re.sub(r"^\d+\. ", "", lines[i]))); i += 1
            i -= 1
            out.append("<ol>" + "".join(f"<li>{x}</li>" for x in items) + "</ol>")
        elif ln.startswith("> "):
            flush()
            buf = []
            while i < len(lines) and lines[i].startswith("> "):
                buf.append(lines[i][2:]); i += 1
            i -= 1
            out.append("<blockquote>" + md("\n".join(buf)) + "</blockquote>")
        elif ln.startswith("|") and i + 1 < len(lines) and re.match(r"\|[\s:|-]+\|$", lines[i + 1]):
            flush()
            head = [c.strip() for c in ln.strip("|").split("|")]
            i += 2
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                rows.append([c.strip() for c in lines[i].strip("|").split("|")]); i += 1
            i -= 1
            t = "<table><thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in head) + "</tr></thead><tbody>"
            for r in rows:
                t += "<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>"
            out.append(t + "</tbody></table>")
        elif ln.strip() == "":
            flush()
        elif ln.startswith("<"):
            flush(); out.append(ln)
        else:
            para.append(ln.strip())
        i += 1
    flush()
    return "\n".join(out)

def front(text: str):
    meta = {}
    if text.startswith("---\n"):
        head, _, body = text[4:].partition("\n---\n")
        for l in head.split("\n"):
            k, _, v = l.partition(":")
            meta[k.strip()] = v.strip()
        return meta, body
    return meta, text

# ---------------------------------------------------------------- layout
NAV = [("/", "Home"), ("/book/", "Book"), ("/docs/", "Docs"), ("/examples/", "Examples"), ("/reference/", "Reference"),
       ("/roadmap/", "Roadmap"), (REPO, "GitHub")]

def page(title, body, path, desc="", extra_nav="", article=True):
    nav = "".join(
        f'<a href="{(BASE + h) if h.startswith("/") else h}"{" aria-current=page" if h == path else ""}>{n}</a>'
        for h, n in NAV)
    d = html.escape(desc or "LeanRDF: RDF and RDFS entailment in Lean 4, searched by Elpi and checked by Lean.")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} · LeanRDF</title>
<meta name="description" content="{d}">
<link rel="icon" href="{BASE}/assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="{BASE}/assets/style.css">
</head>
<body>
<header class="top"><div class="wrap">
<a class="brand" href="{BASE}/"><img src="{BASE}/assets/logo.svg" alt="" width="32" height="32">Lean<span>RDF</span></a>
<nav>{nav}</nav>
</div></header>
<main class="wrap{' prose' if article else ''}">
{extra_nav}
{body}
</main>
<footer><div class="wrap">
<p>LeanRDF builds on <a href="https://github.com/Volland/lean-elpi">lean-elpi</a> and Lean 4.35. The W3C test suites it vendors are under the W3C test suite licence.</p>
<p><a href="{REPO}">Source on GitHub</a></p>
</div></footer>
</body>
</html>
"""

def write(rel, content):
    p = OUT / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")

def load(dirname):
    items = []
    for f in sorted((SRC / dirname).glob("*.md")):
        meta, body = front(f.read_text(encoding="utf-8").replace("{{BASE}}", BASE))
        meta["slug"] = f.stem
        items.append((meta, body))
    return items

def section(dirname, label, title, intro, desc):
    """A section of ordered pages (the book, the docs) with a contents sidebar and a pager."""
    pages = sorted(load(dirname), key=lambda x: int(x[0].get("order", "99")))
    def toc(cur):
        li = "".join(
            f'<li><a href="{BASE}/{dirname}/{m["slug"]}/"{" aria-current=page" if m["slug"] == cur else ""}>{html.escape(m["title"])}</a></li>'
            for m, _ in pages)
        return f'<aside class="toc"><strong>{label}</strong><ol>{li}</ol></aside>'
    cards = "".join(
        f'<li><a href="{BASE}/{dirname}/{m["slug"]}/"><strong>{html.escape(m["title"])}</strong></a><br>{html.escape(m.get("summary",""))}</li>'
        for m, _ in pages)
    write(f"{dirname}/index.html", page(title, f"{intro}<ol class=chapters>{cards}</ol>",
        f"/{dirname}/", desc=desc))
    for n, (m, body) in enumerate(pages):
        prev = pages[n - 1][0] if n else None
        nxt = pages[n + 1][0] if n + 1 < len(pages) else None
        pn = '<nav class="pager">'
        pn += f'<a href="{BASE}/{dirname}/{prev["slug"]}/">← {html.escape(prev["title"])}</a>' if prev else "<span></span>"
        pn += f'<a href="{BASE}/{dirname}/{nxt["slug"]}/">{html.escape(nxt["title"])} →</a>' if nxt else "<span></span>"
        pn += "</nav>"
        write(f"{dirname}/{m['slug']}/index.html", page(m["title"],
            f"<article>{md(body)}</article>{pn}", f"/{dirname}/", desc=m.get("summary", ""),
            extra_nav=toc(m["slug"])))

def main():
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()
    shutil.copytree(ROOT / "site" / "assets", OUT / "assets")
    (OUT / ".nojekyll").write_text("")

    home = (SRC / "home.html").read_text(encoding="utf-8").replace("{{BASE}}", BASE)
    write("index.html", page("RDF semantics in Lean 4", home, "/", article=False))

    section("book", "The book", "The LeanRDF book",
        "<h1>RDF semantics in Lean 4: a short book</h1><p>From triples to model theory to "
        "certified entailment, with LeanRDF as the running example. Read it in order: each "
        "chapter builds on the previous one.</p>",
        "A short book on RDF semantics in Lean 4 with LeanRDF.")
    section("docs", "Documentation", "LeanRDF documentation",
        "<h1>Documentation</h1><p>How to install, run and use LeanRDF: the command-line tools, "
        "the library API of every package, the certificate format, testing and contributing. "
        "The <a href=\"" + BASE + "/book/\">book</a> explains the ideas; these pages are the "
        "manual.</p>",
        "The LeanRDF manual: installation, tools, library API, formats and contributing.")

    for f in sorted(SRC.glob("*.md")):
        m, body = front(f.read_text(encoding="utf-8").replace("{{BASE}}", BASE))
        write(f"{f.stem}/index.html", page(m["title"], f"<article>{md(body)}</article>", f"/{f.stem}/",
              desc=m.get("summary", "")))
    write("404.html", page("Not found", f'<h1>Page not found</h1><p><a href="{BASE}/">Back to the home page</a></p>', "/"))
    print("built", sum(1 for _ in OUT.rglob("*.html")), "pages")

if __name__ == "__main__":
    sys.exit(main())
