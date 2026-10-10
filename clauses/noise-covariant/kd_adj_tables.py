"""exact integer tables (c, c0) (c_i(0) = 0, primitive) for the class representatives found by kd_adjacency.py;
writes kd_facets_d{d}.json in the format of kd_facets.py (only if that file does not exist, else _adj suffix)."""
import sys, json, math, os
import numpy as np
import flint
from kd_adjacency import vertices, coords
d = int(sys.argv[1])
V = vertices(d); X = coords(V, d)
A = np.hstack([np.ones((len(V), 1), np.int64), X])
rows = []
for k in range(len(V)):
    if np.linalg.matrix_rank(A[rows + [k]].astype(float)) > len(rows):
        rows.append(k)
    if len(rows) == A.shape[1]:
        break
Bm = flint.fmpz_mat([[int(v) for v in A[k]] for k in rows]); Binv = Bm.inv()
data = json.load(open(f"kd_adj_d{d}.json"))
out = []
for cl in data:
    s = [int(v) for v in cl["slack"]]
    coef = [sum((Binv[i, j] * s[rows[j]] for j in range(len(rows))), flint.fmpq(0)) for i in range(len(rows))]
    den = 1
    for q in coef:
        den = den * int(q.q) // math.gcd(den, int(q.q))
    ci = [int(q * den) for q in coef]
    g = 0
    for v in ci:
        g = math.gcd(g, abs(v))
    ci = [v // g for v in ci]
    h0, h = ci[0], ci[1:]
    # slack s = h0 + h.x ; table: c_i(0) = 0, c_i(n) = -h_{i,n}, c0 = h0
    c = [[0] + [-h[i * (d - 1) + n - 1] for n in range(1, d)] for i in range(4)]
    # exact check against the slack vector (up to the positive factor)
    vals = [h0 - sum(c[i][n[i]] for i in range(4)) for n in V]
    ratio = None
    for a, b in zip(vals, s):
        if b != 0:
            ratio = (a, b); break
    assert all(a * ratio[1] == b * ratio[0] for a, b in zip(vals, s)) and ratio[0] * ratio[1] > 0
    sub = (c[0] == c[1] == c[2]) and all(c[3][m] == -c[0][(-m) % d] for m in range(d))
    out.append({"size": cl["size"], "c0": h0, "c": c, "tight": cl["tight"], "subadditive_form": sub})
    print(f"size {cl['size']:5d} tight {cl['tight']:3d} c0={h0} c={c}  f-type: {sub}")
fn = f"kd_facets_d{d}.json" if not os.path.exists(f"kd_facets_d{d}.json") else f"kd_facets_d{d}_adj.json"
json.dump(out, open(fn, "w")); print("written", fn)
