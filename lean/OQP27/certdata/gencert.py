"""Build a CONE_d certificate (format OQP27.ConeCertificate) for given integer cells, verify it with the exact
emulation of the Lean checker, and print the Lean source."""
import sys, json
from fractions import Fraction as F
import mpmath as mp
import leanemu as E

mp.mp.dps = 50


def rat_sig(x, sig=20):
    """rational with about `sig` significant digits."""
    x = mp.mpf(x)
    if x == 0:
        return F(0)
    e = int(mp.floor(mp.log10(abs(x))))
    scale = sig - 1 - e
    if scale >= 0:
        return F(int(mp.nint(x * mp.mpf(10) ** scale)), 10 ** scale)
    return F(int(mp.nint(x / mp.mpf(10) ** (-scale))) * 10 ** (-scale))


def nice_up(x):
    """a simple rational >= x (two significant digits, rounded up)."""
    x = F(x)
    if x <= 0:
        return F(0)
    xf = mp.mpf(x.numerator) / x.denominator
    e = int(mp.floor(mp.log10(xf)))
    unit = F(10) ** (e - 1)
    k = -(-x // unit)
    return k * unit


def build(d, q, cells, verbose=True):
    gT = E.gTab(d, q)
    UT = [E.uList(d, gT, n) for n in cells]
    n = d - 1
    K = len(cells)
    U = mp.matrix(n, K)
    for k in range(K):
        for i in range(n):
            I = UT[k][i]
            U[i, k] = (mp.mpf(I.lo.numerator) / I.lo.denominator + mp.mpf(I.hi.numerator) / I.hi.denominator) / 2
    v = mp.matrix([2 / mp.sin(mp.pi * (i + 1) / (2 * d)) for i in range(n)])
    if K == n:
        lam = mp.lu_solve(U, v)
    else:
        raise ValueError("square only")
    lamQ = [rat_sig(lam[k], 22) for k in range(K)]
    W = U * U.T
    Rm = mp.inverse(W)
    RQ = [[rat_sig(Rm[i, j], 22) for j in range(n)] for i in range(n)]
    # first pass with loose eps/beta to measure
    ok, info, _, _ = E.fullCheck(d, q, cells, lamQ, RQ, F(1, 2), F(1, 10 ** 30))
    eps = nice_up(max(info['maxrow'] * 4, F(1, 10 ** 40)))
    beta = nice_up(max(info['maxRr'] * 4, F(1, 10 ** 40)))
    ok, info, _, _ = E.fullCheck(d, q, cells, lamQ, RQ, eps, beta)
    if verbose:
        print(f"d={d}: ok={ok} maxrow={float(info['maxrow']):.3e} maxRr={float(info['maxRr']):.3e} "
              f"mincol={float(info['mincol']):.4e} min lam={float(min(lamQ)):.4e} eps={eps} beta={beta}", file=sys.stderr)
    return ok, dict(d=d, q=q, cells=[list(c) for c in cells], lam=lamQ, R=RQ, eps=eps, beta=beta, info=info)


def lean_rat(x):
    x = F(x)
    if x.denominator == 1:
        return f"{x.numerator}"
    return f"{x.numerator}/{x.denominator}"


def lean_cert(c, name):
    cells = "[" + ", ".join("[" + ", ".join(str(a) for a in cell) + "]" for cell in c['cells']) + "]"
    lam = "[" + ", ".join(lean_rat(x) for x in c['lam']) + "]"
    R = "[" + ",\n      ".join("[" + ", ".join(lean_rat(x) for x in row) + "]" for row in c['R']) + "]"
    return (f"/-- Certificate for `d = {c['d']}`: {len(c['cells'])} integer cells. -/\n"
            f"def {name} : ConeCertificate where\n"
            f"  d := {c['d']}\n  q := {c['q']}\n  cells := {cells}\n  lam := {lam}\n"
            f"  R := {R}\n  eps := {lean_rat(c['eps'])}\n  beta := {lean_rat(c['beta'])}\n")


if __name__ == "__main__":
    spec = json.load(open(sys.argv[1]))
    out = []
    for key, cells in spec.items():
        d = int(key)
        ok, c = build(d, 1, cells)
        if not ok:
            print(f"d={d}: FAILED", file=sys.stderr)
            continue
        out.append(lean_cert(c, f"cert{d}"))
    print("\n".join(out))
