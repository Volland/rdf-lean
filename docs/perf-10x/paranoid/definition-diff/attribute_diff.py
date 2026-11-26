"""For each main theorem: for each constant its statement mentions directly, which of the
constants that differ between BASE and HEAD it reaches (statement closure, proofs not followed)."""
import json, sys, importlib.util
spec = importlib.util.spec_from_file_location('ed', sys.argv[1]); 
src = open(sys.argv[1]).read().replace('\nmain()\n', '\n')
ns = {}; exec(compile(src, 'export_diff', 'exec'), ns)
Export, sig = ns['Export'], ns['sig']
base, head = Export(sys.argv[2]), Export(sys.argv[3])
out = {}
for thm in sys.argv[4:]:
    ht = head.consts[thm]; bt = base.consts[thm]
    roots = sorted(set(ht['tconsts']) | set(bt['tconsts']))
    res = {}
    for r in roots:
        cb, ch = base.closure([r], False), head.closure([r], False)
        d = sorted(n for n in cb & ch if sig(base.consts[n]) != sig(head.consts[n]))
        hints = sorted(n for n in cb & ch if sig(base.consts[n]) == sig(head.consts[n]) and base.consts[n].get('hints') != head.consts[n].get('hints'))
        newp = sorted(n for n in ch - cb if 'LeanRDF' in n); gone = sorted(n for n in cb - ch if 'LeanRDF' in n)
        if d or newp or gone:
            res[r] = {'differ': d, 'head_only_LeanRDF': newp, 'base_only_LeanRDF': gone}
        else:
            res[r] = 'unchanged' + (' (hints-only: %d)' % len(hints) if hints else '')
    out[thm] = res
json.dump(out, sys.stdout, indent=1)
