"""
GLOBAL_fam3COR_cube_ivcheck.py -- independent re-check (mpmath interval arithmetic, separate code) of the S^COR local
cube certificates of Theorem F3': at each DKZ copy z_c of F3 the model w(z) = w* + M (z - z_c) + (1/2) sum (z - z_c)^T
N_lam (z - z_c) e_lam with
  w*  the exact KKT weights (types A, B, C),
  M   the exact solution of the four link-gradient equations, re-solved here in interval arithmetic from the
      float least-squares particular solution xf: x = xf + C^T (C C^T)^{-1} (d - C xf) (an enclosure of the exact x),
  N   the stored dyadic quadratic correction (data, exactly zero sum),
has, for every link l, an interval Hessian of D_l = sum_m Q_l(m) log(Q_l(m)/P_l(m)) over the cube that is negative
definite (interval Cholesky of -[H_l]); in addition D_l(z_c) - S0 and grad D_l(z_c) are enclosed and contain 0.
usage: python GLOBAL_fam3COR_cube_ivcheck.py [rho]
"""
import sys
import json
import itertools
import mpmath
from mpmath import iv, mpf

iv.dps = 40
L = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 1)]
TRIP = list(itertools.product(range(3), repeat=3))


def hit(lam):
    al, b0, b1 = lam
    return [b0 % 3, b1 % 3, (b0 - al) % 3, (b1 - al) % 3]


def ivsolve(A, b):
    """interval Gaussian elimination with pivoting on the interval midpoints (small dense systems)."""
    n = len(A)
    A = [row[:] for row in A]
    b = b[:]
    for k in range(n):
        piv = max(range(k, n), key=lambda i: abs(A[i][k].mid))
        A[k], A[piv] = A[piv], A[k]
        b[k], b[piv] = b[piv], b[k]
        assert not (A[k][k].a <= 0 <= A[k][k].b)
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            for j in range(k, n):
                A[i][j] = A[i][j] - f * A[k][j]
            b[i] = b[i] - f * b[k]
    x = [None] * n
    for i in reversed(range(n)):
        x[i] = (b[i] - sum(A[i][j] * x[j] for j in range(i + 1, n))) / A[i][i]
    return x


def main():
    rho = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf("0.0002")
    import GLOBAL_fam3COR as C                      # only to read the float particular solution Mf and dyadic N
    cms = C.copy_cor_models()
    D = json.load(open("GLOBAL_fam3_copies.json"))
    s3 = iv.sqrt(3)
    beta = ((16 + 24 * s3) - iv.sqrt(3280 - 960 * s3)) / 54
    Qlev = [2 * (2 + s3) / 9, 2 * (2 - s3) / 9, iv.mpf(1) / 9]
    rlev = [1 + beta * (iv.mpf(1) / 2 - k) for k in range(3)]
    S0 = sum(Qlev[k] * iv.log(rlev[k]) for k in range(3))
    Pst = [Qlev[k] / rlev[k] for k in range(3)]
    W = {"A": Pst[2], "B": Pst[1] / 4, "C": Pst[1] / 2}
    allok = True
    for cj, cm in zip(D["copies"], cms):
        p, lev, facet, types = cj["p"], cj["levels"], cj["facet"], cj["types"]
        zc = [iv.pi * int(t) / 6 for t in p]
        w = [iv.mpf(0)] * 27
        for lam, t in zip(facet, types):
            w[lam] = W[t]
        # exact M: per direction i, C x = d with C[l][a] = r*_l(hit_l(lambda_a)), d_l = sum_m dQ_l(m)_i log r*_l(m)
        M = [[iv.mpf(0)] * 3 for _ in range(27)]
        Cm = [[rlev[lev[l][hit(TRIP[lam])[l]]] for lam in facet] for l in range(4)]
        for i in range(3):
            d = []
            for l in range(4):
                ph = sum(L[l][t] * zc[t] for t in range(3))
                s = iv.mpf(0)
                for m in range(3):
                    psi = ph + 2 * iv.pi * m / 3
                    s += (-4 * iv.sin(psi) - 4 * iv.sin(2 * psi)) / 9 * L[l][i] * iv.log(rlev[lev[l][m]])
                d.append(s)
            xf = [iv.mpf(float(cm["Mf"][lam, i])) for lam in facet]
            res = [d[l] - sum(Cm[l][a] * xf[a] for a in range(len(facet))) for l in range(4)]
            G = [[sum(Cm[l][a] * Cm[k][a] for a in range(len(facet))) for k in range(4)] for l in range(4)]
            y = ivsolve(G, res)
            for a, lam in enumerate(facet):
                M[lam][i] = xf[a] + sum(Cm[l][a] * y[l] for l in range(4))
        N = [[[iv.mpf(float(cm["Nd"][lam, i, j])) for j in range(3)] for i in range(3)] for lam in range(27)]
        dz = [iv.mpf([-rho, rho])] * 3
        box = [zc[i] + dz[i] for i in range(3)]
        # P over the cube, grad P over the cube, Hessian of P (constant), and P, grad P at the copy
        Pb = [[iv.mpf(0)] * 3 for _ in range(4)]
        dPb = [[[iv.mpf(0)] * 3 for _ in range(3)] for _ in range(4)]
        PH = [[[[iv.mpf(0)] * 3 for _ in range(3)] for _ in range(3)] for _ in range(4)]
        Pc = [[iv.mpf(0)] * 3 for _ in range(4)]
        Pgc = [[[iv.mpf(0)] * 3 for _ in range(3)] for _ in range(4)]
        valid = True
        for lam in range(27):
            lo = w[lam] - sum(abs(M[lam][i]) * iv.mpf(rho) for i in range(3)) - \
                sum(abs(N[lam][i][j]) * iv.mpf(rho) ** 2 for i in range(3) for j in range(3)) / 2
            valid &= lo.a >= 0
            hl = hit(TRIP[lam])
            for l in range(4):
                m = hl[l]
                Pc[l][m] += w[lam]
                Pb[l][m] += w[lam] + sum(M[lam][i] * dz[i] for i in range(3)) + \
                    sum(N[lam][i][j] * dz[i] * dz[j] for i in range(3) for j in range(3)) / 2
                for i in range(3):
                    Pgc[l][m][i] += M[lam][i]
                    dPb[l][m][i] += M[lam][i] + sum(N[lam][i][j] * dz[j] for j in range(3))
                    for j in range(3):
                        PH[l][m][i][j] += N[lam][i][j]
        line = []
        for l in range(4):
            ph_c = sum(L[l][t] * zc[t] for t in range(3))
            ph_b = sum(L[l][t] * box[t] for t in range(3))
            Dc = iv.mpf(0)
            g = [iv.mpf(0)] * 3
            H = [[iv.mpf(0)] * 3 for _ in range(3)]
            for m in range(3):
                pc = ph_c + 2 * iv.pi * m / 3
                Qc = (3 + 4 * iv.cos(pc) + 2 * iv.cos(2 * pc)) / 9
                dKc = (-4 * iv.sin(pc) - 4 * iv.sin(2 * pc)) / 9
                Dc += Qc * (iv.log(Qc) - iv.log(Pc[l][m]))
                for i in range(3):
                    g[i] += dKc * L[l][i] * (iv.log(Qc) - iv.log(Pc[l][m]) + 1) - Qc * Pgc[l][m][i] / Pc[l][m]
                pb = ph_b + 2 * iv.pi * m / 3
                Q = (3 + 4 * iv.cos(pb) + 2 * iv.cos(2 * pb)) / 9
                dK = (-4 * iv.sin(pb) - 4 * iv.sin(2 * pb)) / 9
                d2K = (-4 * iv.cos(pb) - 8 * iv.cos(2 * pb)) / 9
                P = Pb[l][m]
                assert Q.a > 0 and P.a > 0
                lr = iv.log(Q) - iv.log(P)
                a = [dK * L[l][i] / Q - dPb[l][m][i] / P for i in range(3)]
                for i in range(3):
                    for j in range(3):
                        H[i][j] += d2K * L[l][i] * L[l][j] * (lr + 1) + Q * a[i] * a[j] - Q * PH[l][m][i][j] / P
            A = [[-H[i][j] for j in range(3)] for i in range(3)]
            Lc = [[iv.mpf(0)] * 3 for _ in range(3)]
            nd = True
            for j in range(3):
                s = A[j][j] - sum(Lc[j][k] ** 2 for k in range(j))
                if not s.a > 0:
                    nd = False
                    break
                Lc[j][j] = iv.sqrt(s)
                for i in range(j + 1, 3):
                    Lc[i][j] = (A[i][j] - sum(Lc[i][k] * Lc[j][k] for k in range(j))) / Lc[j][j]
            zero_ok = (Dc - S0).a <= 0 <= (Dc - S0).b and all(t.a <= 0 <= t.b for t in g)
            line.append((l, nd, zero_ok, mpmath.nstr(max(abs((Dc - S0).a), abs((Dc - S0).b)), 3),
                         mpmath.nstr(max(max(abs(t.a), abs(t.b)) for t in g), 3)))
            allok &= nd and zero_ok
        print(f"copy {p}: rho = {rho}; model valid {valid}; per link (l, -[H_l] PD, D_l(z_c) = S0 and grad = 0 "
              f"enclosed, |D_l - S0| <=, |grad| <=): {line}", flush=True)
        allok &= valid
    print("COR LOCAL CUBES RE-CHECKED INDEPENDENTLY (mpmath.iv)" if allok else "FAILED")


if __name__ == "__main__":
    main()
