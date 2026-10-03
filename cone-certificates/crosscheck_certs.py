"""Independent cross-check of saved certificates (non-interval): mpmath.clsin at 50 digits; for d <= 10 also the ORIGINAL definition
u_m = Kt(m) + Kt(2d-m), Kt(m) = (1/d) sum_r K(r+m, r), K = mixed second difference of G over cell endpoints (not the window-sum form)."""
import json, sys
import mpmath as mp
mp.mp.dps = 50
def check(d):
    c = json.load(open(f"certs/cert_d{d}.json")); q = c['q']; N = 4*d
    G = lambda u: -(mp.mpf(N)**2/(2*mp.pi**2))*mp.clsin(2, 2*mp.pi*u/N)
    cache = {}
    def Gq(j):                                   # G(j/q), j any integer
        if j not in cache: cache[j] = G(mp.mpf(j)/q)
        return cache[j]
    v = [2/mp.sin(mp.pi*m/(2*d)) for m in range(1, d)]
    cols = []
    for n in c['cells']:
        if d <= 10:
            L = [0]
            for x in range(4*d): L.append(L[-1] + n[x % d])          # integer endpoints (units 1/q)
            def K(x, y):
                ax, bx, ay, by = L[x], L[x+1], L[y], L[y+1]
                return Gq(bx-ay) - Gq(ax-ay) - Gq(bx-by) + Gq(ax-by)
            Kt = [sum(K((r+m) % N, r) if (r+m) % N != r else 0 for r in range(d))/d for m in range(N)]
            # endpoints of cells with x+m >= N must be shifted by N: handle via periodicity of G (Cl2 is 2pi-periodic in 2pi u/N)
            cols.append([Kt[m] + Kt[2*d-m] for m in range(1, d)])
        else:
            ext = n + n; cs = [0]
            for x in ext: cs.append(cs[-1] + x)
            P = []
            for m in range(d + 1):
                P.append(sum(Gq(cs[r+m]-cs[r]) + Gq(2*d*q - (cs[r+m]-cs[r])) for r in range(d))/d)
            cols.append([P[m+1] - 2*P[m] + P[m-1] for m in range(1, d)])
    lam = [mp.mpf(x) for x in c['lam']]
    res = max(abs(v[m] - sum(cols[k][m]*lam[k] for k in range(len(lam)))) for m in range(d-1))
    print(f"d={d}: K={len(lam)}  min lambda {float(min(lam)):.3e}  max|v - U lam| = {float(res):.3e}  (max v = {float(max(v)):.2f})")
for d in [int(x) for x in sys.argv[1:]]:
    check(d)
