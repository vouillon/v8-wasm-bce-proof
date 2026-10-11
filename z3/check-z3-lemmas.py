# Usage: check-z3-lemmas.py <header>
# Checks the Z3 lemmas written in the comments of a header: each run of
# indented SMT-LIB comment lines ending with (check-sat) must be unsat.
import re, sys, z3
lines = open(sys.argv[1]).read().split('\n')
runs, cur = [], []
for line in lines:
    m = re.match(r'^\s*//   ([(; ].*)$', line)
    if m:
        cur.append(m.group(1))
    elif cur:
        runs.append(cur); cur = []
def split_defs(text):
    # Moves the define-fun forms out of {text}.
    defs, out, i = [], '', 0
    while True:
        j = text.find('(define-fun', i)
        if j < 0: return defs, out + text[i:]
        out += text[i:j]
        depth, k = 0, j
        while True:
            depth += {'(': 1, ')': -1}.get(text[k], 0)
            k += 1
            if depth == 0: break
        defs.append(text[j:k]); i = k
pre, lemmas = [], []
for run in runs:
    defs, text = split_defs('\n'.join(run))
    pre += defs
    if '(check-sat)' in text:
        for part in text.split('(check-sat)')[:-1]:
            lemmas.append(part)
ok = True
for i, b in enumerate(lemmas):
    s = z3.Solver()
    s.from_string('\n'.join(pre) + '\n' + b)
    r = s.check()
    last = [l for l in b.split('\n') if 'assert' in l][-1].strip()
    print(i + 1, r, last[:72])
    ok &= r == z3.unsat
print('ALL UNSAT' if ok else 'SOME LEMMA FAILS', len(lemmas))
# Vacuity: without the negated conclusion (the last assert), the
# assumptions must be satisfiable.
vac = True
for i, b in enumerate(lemmas):
    idx = b.rfind('(assert (not')
    if idx < 0: print('NO NEGATED CONCLUSION', i + 1); vac = False; continue
    s = z3.Solver(); s.from_string('\n'.join(pre) + '\n' + b[:idx])
    if s.check() != z3.sat: print('VACUOUS', i + 1); vac = False
print('NONE VACUOUS' if vac else 'SOME VACUOUS')
sys.exit(0 if ok and vac and lemmas else 1)
