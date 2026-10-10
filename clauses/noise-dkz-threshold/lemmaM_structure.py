"""structure of pairing solutions: minimise the mass on interior cells (x1,x2>=1, x1+x2<=S-1)."""
import sys, numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
from lemmaM_pairing import Q_law

def solve(d, obj="core"):
    Q, G, kap = Q_law(d); S = d - 1
    cells = [(a, b) for a in range(d) for b in range(a, d) if a + b <= S]
    idx = {c: i for i, c in enumerate(cells)}
    nv = len(cells)
    A = lil_matrix((d + (S + 1) // 2, nv)); rhs = []; r = 0
    for a in range(d):
        for b in range(d):
            if a + b <= S:
                A[r, idx[(min(a, b), max(a, b))]] += 1.0
        rhs.append(Q[a]); r += 1
    for y in range((S + 1) // 2):
        for a in range(y + 1):
            A[r, idx[(min(a, y - a), max(a, y - a))]] += 1.0
        y2 = S - y
        for a in range(y2 + 1):
            A[r, idx[(min(a, y2 - a), max(a, y2 - a))]] -= 1.0
        rhs.append(0.0); r += 1
    c = np.array([1.0 if (a >= 1 and a + b <= S - 1) else 0.0 for (a, b) in cells])
    res = linprog(c, A_eq=csr_matrix(A[:r]), b_eq=np.array(rhs), bounds=[(0, None)] * nv, method="highs")
    return res, cells, Q

for d in [int(x) for x in sys.argv[1:]]:
    res, cells, Q = solve(d)
    x = res.x
    core = [(cells[i], x[i]) for i in range(len(cells)) if x[i] > 1e-12 and cells[i][0] >= 1 and sum(cells[i]) <= d - 2]
    print(f"d={d} status={res.status} core mass={res.fun:.6e}  #core cells={len(core)}")
    core.sort(key=lambda t: -t[1])
    print("  top core cells:", [(c, f"{w:.3e}") for c, w in core[:25]])
    S = d - 1
    print("  edges (x,0) x=1..8:", [f"{x[cells.index((0, k))]:.3e}" for k in range(1, 9)])
    print("  Q(0..6):", np.round(Q[:7], 5), " Q(S-6..S):", np.round(Q[-7:], 5), " c=", (Q[d//2]))
