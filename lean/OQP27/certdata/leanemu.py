"""Exact (Fraction) emulation of the Lean checker OQP27.ConeCertificate.fullCheck (files CertInterval, CertTrig,
CertClausen, CertPipeline, CertCheck).  Every function mirrors the Lean definition of the same name."""
from fractions import Fraction as F
from math import floor, ceil, factorial

PREC = 100
PILO = F(314159265358979323846, 10 ** 20)
PIHI = F(314159265358979323847, 10 ** 20)
HTERMS = 20


def rdDown(k, x):
    return F(floor(x * 2 ** k), 2 ** k)


def rdUp(k, x):
    return F(ceil(x * 2 ** k), 2 ** k)


class QI:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        self.lo = F(lo); self.hi = F(hi)

    def __repr__(self):
        return f"[{float(self.lo):.17g}, {float(self.hi):.17g}]"


DEFAULT = QI(0, 0)


def pt(q): return QI(q, q)
def add(I, J): return QI(I.lo + J.lo, I.hi + J.hi)
def neg(I): return QI(-I.hi, -I.lo)
def sub(I, J): return QI(I.lo - J.hi, I.hi - J.lo)


def smul(c, I):
    c = F(c)
    return QI(c * I.lo, c * I.hi) if c >= 0 else QI(c * I.hi, c * I.lo)


def mul(I, J):
    a, b, c, d = I.lo * J.lo, I.lo * J.hi, I.hi * J.lo, I.hi * J.hi
    return QI(min(min(a, b), min(c, d)), max(max(a, b), max(c, d)))


def inv(I): return QI(1 / I.hi, 1 / I.lo)
def mag(I): return max(abs(I.lo), abs(I.hi))
def rnd(k, I): return QI(rdDown(k, I.lo), rdUp(k, I.hi))


def sumRange(n, f):
    lo = F(0); hi = F(0)
    for i in range(n):
        x = f(i); lo += x.lo; hi += x.hi
    return QI(lo, hi)


def getD(l, i, d):
    return l[i] if 0 <= i < len(l) else d


# ---------------- CertTrig
def sinTaylor(x, n):
    return sum(F((-1) ** i) * (x ** (2 * i + 1) / factorial(2 * i + 1)) for i in range(n))


def cosTaylor(x, n):
    return sum(F((-1) ** i) * (x ** (2 * i) / factorial(2 * i)) for i in range(n))


def sinSmall(r):
    xl = rdDown(PREC, PILO * r); xh = rdUp(PREC, PIHI * r)
    if 0 <= r and xh <= 1:
        return QI(rdDown(PREC, sinTaylor(xl, 10)), rdUp(PREC, sinTaylor(xh, 11)))
    return QI(-1, 1)


def cosSmall(r):
    xl = rdDown(PREC, PILO * r); xh = rdUp(PREC, PIHI * r)
    if 0 <= r and xh <= 1:
        return QI(rdDown(PREC, cosTaylor(xh, 10)), rdUp(PREC, cosTaylor(xl, 11)))
    return QI(-1, 1)


def sinPi(r):
    r = F(r)
    r0 = r - 2 * floor(r / 2)
    r1 = r0 - 1 if 1 <= r0 else r0
    r2 = 1 - r1 if F(1, 2) < r1 else r1
    base = sinSmall(r2) if r2 <= F(1, 4) else cosSmall(F(1, 2) - r2)
    return neg(base) if 1 <= r0 else base


# ---------------- CertClausen
def tailLo(y):
    return 1 / y + 1 / (2 * y ** 2) + 1 / (6 * y ** 3) - 1 / (30 * y ** 5)


def tailHi(y):
    return tailLo(y) + 1 / (42 * y ** 7)


def hEnc(Q, b):
    base = sum(F(1) / (F(b) + Q * i) ** 2 for i in range(HTERMS))
    y = F(HTERMS) + F(b) / Q
    return rnd(PREC, QI(base + tailLo(y) / F(Q) ** 2, base + tailHi(y) / F(Q) ** 2))


def sinTab(Q):
    return [sinPi(F(2 * b) / Q) for b in range(Q)]


def hTab(Q):
    return [hEnc(Q, a + 1) for a in range(Q)]


def clEnc(Q, sT, hT, c):
    return rnd(PREC, sumRange(Q, lambda a: mul(getD(sT, (c * (a + 1)) % Q, DEFAULT), getD(hT, a, DEFAULT))))


def clTab(Q, n):
    sT = sinTab(Q); hT = hTab(Q)
    return [clEnc(Q, sT, hT, c) for c in range(n + 1)]


def factorEnc(d):
    return rnd(PREC, QI(F(4 * d) ** 2 / (2 * PIHI ** 2), F(4 * d) ** 2 / (2 * PILO ** 2)))


def gEnc(d, q, clT, J):
    return rnd(PREC, neg(mul(factorEnc(d), add(getD(clT, J, DEFAULT), getD(clT, 2 * d * q - J, DEFAULT)))))


# ---------------- CertPipeline
def winN(d, n, r, m):
    return sum(getD(n, (r + i) % d, 0) for i in range(m))


def gTab(d, q):
    clT = clTab(4 * d * q, 2 * d * q)
    fe = factorEnc(d)
    return [gEnc(d, q, clT, J) for J in range(d * q + 1)]


def pEnc(d, gT, n, m):
    return smul(F(1, d), sumRange(d, lambda r: getD(gT, winN(d, n, r, m), DEFAULT)))


def pList(d, gT, n):
    return [pEnc(d, gT, n, m) for m in range(d + 1)]


def uFromP(pL, m):
    return add(sub(getD(pL, m + 1, DEFAULT), smul(2, getD(pL, m, DEFAULT))), getD(pL, m - 1, DEFAULT))


def uList(d, gT, n):
    pL = pList(d, gT, n)
    return [uFromP(pL, i + 1) for i in range(d - 1)]


def sinV(d, m):
    return sinPi(F(m) / (2 * d))


def vEnc(d, m):
    return rnd(PREC, smul(2, inv(sinV(d, m))))


# ---------------- CertCheck
def coneCheckCore(n, K, UI, vI, lam, R, eps, beta, verbose=False):
    W = [[rnd(100, sumRange(K, lambda k: mul(UI(i, k), UI(j, k)))) for j in range(n)] for i in range(n)]
    def WI(i, j): return W[i][j]
    def EI(i, j):
        return sub(pt(1 if i == j else 0), sumRange(n, lambda l: smul(R(i, l), WI(l, j))))
    res = [rnd(100, sub(vI(i), sumRange(K, lambda k: smul(lam(k), UI(i, k))))) for i in range(n)]
    def RrI(i):
        return sumRange(n, lambda l: smul(R(i, l), res[l]))
    rows = [sum(mag(EI(i, j)) for j in range(n)) for i in range(n)]
    rr = [mag(RrI(i)) for i in range(n)]
    ok = (0 <= eps) and (eps < 1) and (0 <= beta)
    ok = ok and all(r <= eps for r in rows) and all(x <= beta for x in rr)
    cols = [lam(k) - sum(mag(UI(i, k)) for i in range(n)) * (beta / (1 - eps)) for k in range(K)]
    ok = ok and all(c > 0 for c in cols)
    info = dict(maxrow=max(rows) if rows else 0, maxRr=max(rr) if rr else 0,
                mincol=min(cols) if cols else 0)
    return ok, info


def fullCheck(d, q, cells, lam, R, eps, beta):
    gT = gTab(d, q)
    UT = [uList(d, gT, n) for n in cells]
    vT = [vEnc(d, i + 1) for i in range(d - 1)]
    okd = 1 <= d
    oks = all(0 < sinV(d, i + 1).lo for i in range(d - 1))
    okc = q > 0 and all(sum(getD(n, r, 0) for r in range(d)) == d * q for n in cells)
    UI = lambda i, k: getD(getD(UT, k, []), i, DEFAULT)
    vI = lambda i: getD(vT, i, DEFAULT)
    lamF = lambda k: getD(lam, k, F(0))
    RF = lambda i, j: getD(getD(R, i, []), j, F(0))
    okcore, info = coneCheckCore(d - 1, len(cells), UI, vI, lamF, RF, eps, beta)
    return okd and oks and okc and okcore, info, UT, vT
