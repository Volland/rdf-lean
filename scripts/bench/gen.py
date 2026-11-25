#!/usr/bin/env python3
"""Synthetic inputs of growing size for the LeanRDF scaling benchmark.

Usage: scripts/bench/gen.py KIND N OUTDIR

KIND is one of
  rdfs    data.nt, q.nt (entailed), q-neg.nt (not entailed: exercises the countermodel),
          q-all.nt (N ground query triples: a certificate of about 3N nodes)
          a 10-deep subClassOf chain, p0 subPropertyOf p1 with a domain and a range, and N
          instances typed C0 and linked by p0 in a ring
  owl     data.nt, q.nt: the rdfs shape plus OWL 2 RL features (a transitive property over a
          chain of N/4 nodes, inverseOf, symmetric, equivalentClass, someValuesFrom, hasValue)
  el      onto.ttl: an OWL 2 EL ontology with N named classes (subClassOf chains, existential
          restrictions, equivalent intersections), the shape of examples/owl-el-anatomy
  sparql  data.ttl, q1.rq (join + filter + order), q2.rq (group by + optional): a library of N books
  shacl   data.ttl, shapes.ttl: N employees, about 5% invalid, shapes of examples/shacl-employees

Only the Python standard library; deterministic for a given KIND and N.
"""
import os
import sys

E = "http://ex.org/"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS = "http://www.w3.org/2000/01/rdf-schema#"
OWL = "http://www.w3.org/2002/07/owl#"
TYPE, SC, SP = RDF + "type", RDFS + "subClassOf", RDFS + "subPropertyOf"
DOM, RNG = RDFS + "domain", RDFS + "range"


def t(s, p, o):
    o = o if o.startswith('"') or o.startswith("_:") else f"<{o}>"
    s = s if s.startswith("_:") else f"<{s}>"
    return f"{s} <{p}> {o} ."


def rdfs_lines(n, depth=10):
    L = [t(f"{E}C{c}", SC, f"{E}C{c + 1}") for c in range(depth)]
    L += [t(f"{E}p0", SP, f"{E}p1"), t(f"{E}p1", DOM, f"{E}C0"), t(f"{E}p1", RNG, f"{E}K0")]
    for i in range(n):
        L.append(t(f"{E}i{i}", TYPE, f"{E}C0"))
        L.append(t(f"{E}i{i}", f"{E}p0", f"{E}i{(i + 1) % n}"))
    return L


def write(out, name, text):
    with open(os.path.join(out, name), "w") as f:
        f.write(text)


def gen_rdfs(n, out):
    write(out, "data.nt", "\n".join(rdfs_lines(n)) + "\n")
    write(out, "q.nt", t(f"{E}i0", TYPE, f"{E}C10") + "\n" + t(f"{E}i{n - 1}", f"{E}p1", "_:x") + "\n")
    write(out, "q-neg.nt", t(f"{E}i0", TYPE, f"{E}Nope") + "\n")
    # a large query: every instance typed by the top of the chain (certificate of about 3N nodes)
    write(out, "q-all.nt", "".join(t(f"{E}i{i}", TYPE, f"{E}C10") + "\n" for i in range(n)))


def gen_owl(n, out):
    L = rdfs_lines(n)
    m = max(2, n // 4)
    L += [t(f"{E}anc", TYPE, OWL + "TransitiveProperty"),
          t(f"{E}desc", OWL + "inverseOf", f"{E}anc"),
          t(f"{E}knows", TYPE, OWL + "SymmetricProperty"),
          t(f"{E}C10", OWL + "equivalentClass", f"{E}D10"),
          t(f"{E}R", OWL + "onProperty", f"{E}p0"),
          t(f"{E}R", OWL + "someValuesFrom", f"{E}C0"),
          t(f"{E}H", OWL + "onProperty", f"{E}knows"),
          t(f"{E}H", OWL + "hasValue", f"{E}i0")]
    for i in range(m - 1):
        L.append(t(f"{E}a{i}", f"{E}anc", f"{E}a{i + 1}"))
    for i in range(0, n, 2):
        L.append(t(f"{E}i{i}", f"{E}knows", f"{E}i{(i + 3) % n}"))
    write(out, "data.nt", "\n".join(L) + "\n")
    write(out, "q.nt", t(f"{E}a0", f"{E}anc", f"{E}a{m - 1}") + "\n" +
          t(f"{E}a{m - 1}", f"{E}desc", f"{E}a0") + "\n" + t(f"{E}i0", TYPE, f"{E}D10") + "\n")


def gen_el(n, out):
    L = ["@prefix : <http://ex.org/el#> .", "@prefix owl: <http://www.w3.org/2002/07/owl#> .",
         "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .", ":partOf rdfs:subPropertyOf :hasSite ."]
    for i in range(n):
        if i % 10:
            L.append(f":A{i} rdfs:subClassOf :A{i - 1} .")
        if i % 7 == 3:
            L.append(f":A{i} rdfs:subClassOf [ owl:onProperty :partOf ; owl:someValuesFrom :A{i // 2} ] .")
        if i % 11 == 5:
            L.append(f":B{i} owl:equivalentClass [ owl:intersectionOf ( :A{i - 1} "
                     f"[ owl:onProperty :hasSite ; owl:someValuesFrom :A{i // 3} ] ) ] .")
    write(out, "onto.ttl", "\n".join(L) + "\n")


def gen_sparql(n, out):
    L = ["@prefix : <http://example.org/library#> .", "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> ."]
    authors = max(1, n // 5)
    for a in range(authors):
        L.append(f':a{a} a :Author ; :name "Author {a}" ; :born {1900 + a % 100} .')
    for b in range(n):
        pages = f" ; :pages {100 + (b * 37) % 500}" if b % 3 else ""
        L.append(f':b{b} a :Book ; :title "Book {b}"@en ; :author :a{b % authors} ; :year {1950 + b % 70}{pages} .')
    for k in range(n // 4):
        L.append(f':loan{k} :book :b{(k * 7) % n} ; :member :m{k % 10} .')
    write(out, "data.ttl", "\n".join(L) + "\n")
    write(out, "q1.rq", "PREFIX : <http://example.org/library#>\nSELECT ?title ?name WHERE {\n"
          "  ?book a :Book ; :title ?title ; :author ?a ; :year ?y .\n  ?a :name ?name .\n"
          "  FILTER (?y > 1990)\n} ORDER BY ?name ?title\n")
    write(out, "q2.rq", "PREFIX : <http://example.org/library#>\n"
          "SELECT ?name (COUNT(?book) AS ?books) (AVG(?pages) AS ?avg) WHERE {\n"
          "  ?book :author ?a . ?a :name ?name .\n  OPTIONAL { ?book :pages ?pages }\n"
          "} GROUP BY ?name ORDER BY DESC(?books) ?name\n")


def gen_shacl(n, out):
    L = ["@prefix : <http://example.org/hr#> .", "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .",
         ":Contractor rdfs:subClassOf :Employee ."]
    for i in range(n):
        cls = ":Contractor" if i % 4 == 0 else ":Employee"
        email = f'"e{i}@example.org"' if i % 20 else '"broken address"'
        age = 20 + i % 60 if i % 25 else 7
        mgr = f" ; :manager :e{i // 2}" if i else ""
        L.append(f':e{i} a {cls} ; :name "E{i}" ; :email {email} ; :age {age}{mgr} .')
    for k in range(max(1, n // 10)):
        members = ", ".join(f":e{j}" for j in range(k * 10, min(n, k * 10 + 10)))
        L.append(f":team{k} a :Team ; :member {members} ; :lead :e{k * 10} .")
    write(out, "data.ttl", "\n".join(L) + "\n")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "..", "..", "examples", "shacl-employees", "shapes.ttl")) as f:
        write(out, "shapes.ttl", f.read())


KINDS = {"rdfs": gen_rdfs, "owl": gen_owl, "el": gen_el, "sparql": gen_sparql, "shacl": gen_shacl}

if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] not in KINDS:
        sys.exit(__doc__)
    os.makedirs(sys.argv[3], exist_ok=True)
    KINDS[sys.argv[1]](int(sys.argv[2]), sys.argv[3])
