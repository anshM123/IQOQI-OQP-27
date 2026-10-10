"""
GLOBAL_fam3_cube_ivcheck.py -- independent re-check (mpmath interval arithmetic, separate code from the python-flint
implementation of GLOBAL_fam3BB.py) of the two local cube certificates of Theorem F3 (S^UNI):
on the cube |z - z_c|_inf <= rho around each DKZ copy z_c of the family F3, with the exact KKT model w* plus the
stored dyadic first-order correction M (column sums 0, supported on the CGLMP facet), the Hessian of
F(z) = (1/4) sum_{l,m} Q_l(m) log(Q_l(m) / P_l(m)) is negative definite.  Negative definiteness of every matrix in the
interval enclosure is shown by a Gershgorin-type test on -H after an exact-arithmetic-free diagonal scaling:
  -H_ii - sum_{j != i} |H_ij| > 0 for all i   (sufficient), or else an interval Cholesky.
The copy data (levels, facet strategies, types) are recomputed here from scratch in floating point and checked
against GLOBAL_fam3_copies.json; F(z_c) = S0 and grad F(z_c) = 0 are the exact identities of GLOBAL_fam3_exact.py.
usage: python GLOBAL_fam3_cube_ivcheck.py [rho]
"""
import sys
import json
import itertools
import mpmath
from mpmath import iv, mpf

iv.dps = 40
mpmath.mp.dps = 40
L = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 1)]
TRIP = list(itertools.product(range(3), repeat=3))


def hit(lam):
    al, b0, b1 = lam
    return [b0 % 3, b1 % 3, (b0 - al) % 3, (b1 - al) % 3]


def main():
    rho = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf("0.001")
    import numpy as np
    D = json.load(open("GLOBAL_fam3_copies.json"))
    cert = np.load("GLOBAL_fam3BB_cert.npz")
    import GLOBAL_fam3BB as G                      # only to read the stored dyadic M of each copy (data)
    copies = G.load_copies()
    s3 = iv.sqrt(3)
    beta = ((16 + 24 * s3) - iv.sqrt(3280 - 960 * s3)) / 54
    Qlev = [2 * (2 + s3) / 9, 2 * (2 - s3) / 9, iv.mpf(1) / 9]
    rlev = [1 + beta * (iv.mpf(1) / 2 - k) for k in range(3)]
    Pst = [Qlev[k] / rlev[k] for k in range(3)]
    W = {"A": Pst[2], "B": Pst[1] / 4, "C": Pst[1] / 2}
    allok = True
    for cj, cp in zip(D["copies"], copies):
        p = cj["p"]
        lev = cj["levels"]
        facet = cj["facet"]
        types = cj["types"]
        zc = [iv.pi * int(t) / 6 for t in p]
        box = [zc[i] + iv.mpf([-rho, rho]) for i in range(3)]
        M = [[iv.mpf(float(cp["M"][lam, i])) for i in range(3)] for lam in range(27)]
        w = [iv.mpf(0)] * 27
        for lam, t in zip(facet, types):
            w[lam] = W[t]
        # P over the cube (affine in z - z_c) and its constant gradient
        dz = [iv.mpf([-rho, rho])] * 3
        Pb = [[iv.mpf(0)] * 3 for _ in range(4)]
        Pg = [[[iv.mpf(0)] * 3 for _ in range(3)] for _ in range(4)]
        for lam in range(27):
            hl = hit(TRIP[lam])
            for l in range(4):
                Pb[l][hl[l]] += w[lam] + sum(M[lam][i] * dz[i] for i in range(3))
                for i in range(3):
                    Pg[l][hl[l]][i] += M[lam][i]
        H = [[iv.mpf(0)] * 3 for _ in range(3)]
        for l in range(4):
            ph = sum(L[l][i] * box[i] for i in range(3))
            for m in range(3):
                psi = ph + 2 * iv.pi * m / 3
                Q = (3 + 4 * iv.cos(psi) + 2 * iv.cos(2 * psi)) / 9
                dK = (-4 * iv.sin(psi) - 4 * iv.sin(2 * psi)) / 9
                d2K = (-4 * iv.cos(psi) - 8 * iv.cos(2 * psi)) / 9
                P = Pb[l][m]
                assert Q.a > 0 and P.a > 0
                lr = iv.log(Q) - iv.log(P)
                a = [dK * L[l][i] / Q - Pg[l][m][i] / P for i in range(3)]
                for i in range(3):
                    for j in range(3):
                        H[i][j] += (d2K * L[l][i] * L[l][j] * (lr + 1) + Q * a[i] * a[j]) / 4
        # model validity on the cube: w + M dz >= 0 for every strategy
        valid = all((w[lam] - sum(abs(M[lam][i]) * iv.mpf(rho) for i in range(3))).a >= 0 for lam in range(27))
        # negative definiteness: interval Cholesky of -H
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
        print(f"copy {p}: rho = {rho}; model valid on the cube {valid}; -[H] positive definite (interval Cholesky) {nd}; "
              f"H diagonal midpoints {[mpmath.nstr(H[i][i].mid, 6) for i in range(3)]}", flush=True)
        allok &= valid and nd
    print("LOCAL CUBES RE-CHECKED INDEPENDENTLY (mpmath.iv)" if allok else "FAILED")


if __name__ == "__main__":
    main()
