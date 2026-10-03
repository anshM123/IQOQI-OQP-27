"""
sweep_table.py -- summary table of the global POVM search (runs/sweep_d{d}_D{D}.log).
For each (d, D): best I, I - I_ME, number of starts, number reaching I_ME (|I - I_ME| < 1e-9), number ABOVE.
usage: python sweep_table.py  (prints markdown)
"""
import re
import glob
import os
from povm_core import I_ME

rows = {}
for f in glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'sweep_d*_D*.log')):
    m = re.search(r'sweep_d(\d+)_D(\d+)\.log', f)
    d, D = int(m.group(1)), int(m.group(2))
    best = None
    bestgap = None
    n = me = above = 0
    ime = None
    for line in open(f):
        if line.startswith('# d='):
            ime = I_ME(d)
        if line.startswith('start'):
            n += 1
            I = float(re.search(r'I = ([-0-9.]+)', line).group(1))
            gap_full = float(re.search(r'I-I_ME = ([-+0-9.e]+)', line).group(1))   # double precision
            if best is None or gap_full > bestgap:
                best, bestgap = I, gap_full
            me += (' ME ' in line or line.rstrip().endswith('ME') or '  ME  ' in line)
            above += ('ABOVE' in line)
    if best is not None:
        rows[(d, D)] = (best, bestgap, n, me, above)

print('| d | D | starts | best I | best I - I_ME(d) | starts at I_ME | starts above |')
print('|---|---|---|---|---|---|---|')
for (d, D) in sorted(rows):
    best, gap, n, me, above = rows[(d, D)]
    print(f'| {d} | {D} | {n} | {best:.13f} | {gap:+.3e} | {me} | {above} |')
tot = sum(r[2] for r in rows.values())
print(f'\ntotal starts: {tot}; total above I_ME: {sum(r[4] for r in rows.values())}')
