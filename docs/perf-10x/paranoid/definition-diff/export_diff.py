"""Kernel-level diff of the constants that the main theorems' statements depend on, between two
leanexport NDJSON exports (BASE and HEAD). Expressions are compared structurally up to alpha
equivalence (binder names and binder info ignored, mdata transparent), like `lake comparator`.

usage: python3 -I export_diff.py BASE.ndjson HEAD.ndjson THEOREM...  > report.json
"""
import json, sys, hashlib

def H(*parts):
    return hashlib.sha1('\x00'.join(parts).encode()).hexdigest()[:20]

class Export:
    def __init__(self, path):
        self.names = {0: ''}
        self.levels = {0: 'z'}
        self.eh = {}      # expr idx -> structural hash
        self.econsts = {} # expr idx -> frozenset of constant names used
        self.consts = {}  # name -> dict
        with open(path) as f:
            f.readline()
            for line in f:
                if line.strip(): self.item(json.loads(line))
    def name(self, i): return self.names[i]
    def item(self, o):
        if 'in' in o:
            i = o['in']
            if 'str' in o:
                d = o['str']; pre = self.names[d['pre']]
                self.names[i] = (pre + '.' if pre else '') + d['str']
            else:
                d = o['num']; pre = self.names[d['pre']]
                self.names[i] = (pre + '.' if pre else '') + str(d['i'])
        elif 'il' in o:
            i = o['il']
            if 'succ' in o: self.levels[i] = 's(' + self.levels[o['succ']] + ')'
            elif 'max' in o: a, b = o['max']; self.levels[i] = 'max(%s,%s)' % (self.levels[a], self.levels[b])
            elif 'imax' in o: a, b = o['imax']; self.levels[i] = 'imax(%s,%s)' % (self.levels[a], self.levels[b])
            elif 'param' in o: self.levels[i] = 'p:' + self.names[o['param']]
        elif 'ie' in o:
            i = o['ie']; eh = self.eh; ec = self.econsts; E = frozenset()
            if 'bvar' in o: eh[i] = H('bvar', str(o['bvar'])); ec[i] = E
            elif 'sort' in o: eh[i] = H('sort', self.levels[o['sort']]); ec[i] = E
            elif 'const' in o:
                d = o['const']; n = self.names[d['name']]
                eh[i] = H('const', n, *[self.levels[u] for u in d['us']]); ec[i] = frozenset([n])
            elif 'app' in o:
                d = o['app']; eh[i] = H('app', eh[d['fn']], eh[d['arg']]); ec[i] = ec[d['fn']] | ec[d['arg']]
            elif 'lam' in o or 'forallE' in o:
                k = 'lam' if 'lam' in o else 'forallE'; d = o[k]
                eh[i] = H(k, eh[d['type']], eh[d['body']]); ec[i] = ec[d['type']] | ec[d['body']]
            elif 'letE' in o:
                d = o['letE']; eh[i] = H('let', eh[d['type']], eh[d['value']], eh[d['body']])
                ec[i] = ec[d['type']] | ec[d['value']] | ec[d['body']]
            elif 'proj' in o:
                d = o['proj']; n = self.names[d['typeName']]
                eh[i] = H('proj', n, str(d['idx']), eh[d['struct']]); ec[i] = ec[d['struct']] | frozenset([n])
            elif 'natVal' in o: eh[i] = H('nat', o['natVal']); ec[i] = E
            elif 'strVal' in o: eh[i] = H('str', o['strVal']); ec[i] = E
            elif 'mdata' in o: d = o['mdata']; eh[i] = eh[d['expr']]; ec[i] = ec[d['expr']]
            else: raise ValueError(o)
        else:
            (k, d), = o.items()
            if k == 'inductive':
                for t in d['types']: self.add('induct', t)
                for c in d['ctors']: self.add('ctor', c)
                for r in d['recs']: self.add('rec', r)
            else: self.add(k, d)
    def add(self, kind, d):
        n = self.names[d['name']]
        c = {'kind': kind, 'lps': [self.names[x] for x in d['levelParams']],
             'type': self.eh[d['type']], 'tconsts': self.econsts[d['type']], 'vconsts': frozenset(), 'extra': []}
        if 'value' in d:
            c['value'] = self.eh[d['value']]; c['vconsts'] = self.econsts[d['value']]
        if kind == 'def':
            c['hints'] = json.dumps(d['hints']); c['extra'] += [d['safety']]
        if kind == 'induct':
            c['ctors'] = [self.names[x] for x in d['ctors']]
            c['extra'] += [str(d[k]) for k in ('numParams', 'numIndices', 'numNested', 'isRec', 'isUnsafe', 'isReflexive')]
            c['extra'] += c['ctors'] + [self.names[x] for x in d['all']]
        if kind == 'ctor':
            c['induct'] = self.names[d['induct']]
            c['extra'] += [c['induct']] + [str(d[k]) for k in ('cidx', 'numParams', 'numFields', 'isUnsafe')]
        if kind == 'rec':
            rs = d['rules']; c['rules'] = [(self.names[r['ctor']], r['nfields'], self.eh[r['rhs']]) for r in rs]
            c['vconsts'] = frozenset().union(*[self.econsts[r['rhs']] for r in rs]) if rs else frozenset()
            c['extra'] += [str(d[k]) for k in ('numParams', 'numIndices', 'numMotives', 'numMinors', 'k', 'isUnsafe')]
            c['extra'] += [repr(c['rules'])]
        if kind == 'quot': c['extra'] += [d['kind']]
        self.consts[n] = c
    def deps(self, n, follow_proofs):
        c = self.consts.get(n)
        if c is None: return set()
        out = set(c['tconsts'])
        if c['kind'] in ('def', 'opaque', 'rec') or (c['kind'] == 'thm' and follow_proofs):
            out |= c['vconsts']
        if c['kind'] == 'induct': out |= set(c['ctors'])
        if c['kind'] == 'ctor': out.add(c['induct'])
        return out
    def closure(self, roots, follow_proofs):
        seen = set(); work = list(roots)
        while work:
            n = work.pop()
            if n in seen: continue
            seen.add(n); work.extend(self.deps(n, follow_proofs) - seen)
        return seen

def sig(c, with_value=True):
    parts = [c['kind'], ','.join(c['lps']), c['type']] + c['extra']
    if with_value and 'value' in c: parts.append(c['value'])
    return H(*parts)

def main():
    base, head = Export(sys.argv[1]), Export(sys.argv[2])
    report = {}
    for thm in sys.argv[3:]:
        r = {}
        bt, ht = base.consts.get(thm), head.consts.get(thm)
        r['present'] = [bt is not None, ht is not None]
        r['statement_type_identical'] = bool(bt and ht and bt['type'] == ht['type'] and bt['lps'] == ht['lps'])
        # the statement closure: what the TYPE of the theorem mentions, then the definitions
        # (values of defs/opaques/recursor rules, ctors) those reach; theorem proofs are not followed
        roots = set((bt or {}).get('tconsts', ())) | set((ht or {}).get('tconsts', ()))
        cb, ch = base.closure(roots, False), head.closure(roots, False)
        r['closure_size'] = [len(cb), len(ch)]
        r['only_in_base'] = sorted(cb - ch)
        r['only_in_head'] = sorted(ch - cb)
        diffs = []
        for n in sorted(cb & ch):
            a, b = base.consts[n], head.consts[n]
            if sig(a) != sig(b):
                what = []
                if a['kind'] != b['kind']: what.append('kind %s->%s' % (a['kind'], b['kind']))
                if a['type'] != b['type'] or a['lps'] != b['lps']: what.append('type')
                if a.get('value') != b.get('value'): what.append('value')
                if a['extra'] != b['extra']: what.append('metadata')
                diffs.append({'name': n, 'kind': b['kind'], 'differs_in': what})
            elif a.get('hints') != b.get('hints'):
                diffs.append({'name': n, 'kind': b['kind'], 'differs_in': ['reducibility hints only']})
        r['differing'] = diffs
        # the comparator-style closure (also follows theorem proofs), for reference
        fb, fh = base.closure(roots, True), head.closure(roots, True)
        r['full_closure_size'] = [len(fb), len(fh)]
        r['full_closure_differing_count'] = sum(1 for n in fb & fh if sig(base.consts[n]) != sig(head.consts[n]))
        report[thm] = r
    json.dump(report, sys.stdout, indent=1)

main()
