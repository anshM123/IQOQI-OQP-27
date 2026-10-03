"""a08: the eps^2 coefficient.  phi_2(b) = b^3 d_x u_e(0, 1/b) of the model (identity (I2): proof RIGOR_ALLD.md s.2, checks
a14_identities.py):
   phi_2(b) = -(pi/2)(1 + pi/12) b^3/B + (pi/2) t1c b^2/B + (pi/2) A0 b^3/B^2 - (A0^2/2) b^2 B4/B^3,
   B = b kappa_2(b) = B_2(b),  B4 = b^3 kappa_4(b)/2 = B_4(b),  t1c = -(2/3 + 5 pi/72 + 1/(3 pi)).
A_2(m) = Delta^4 phi_2(m) with phi_2(0) = 0, phi_2(-1) = phi_2(1) (even extension).
CLAIMS (CERTIFIED by this script):  A_2(1) in [-2.7560, -2.7559];  A_2(m) > 0 for every m >= 2.
 Part 1: interval arithmetic for 2 <= m <= M2 (polygamma at integers).
 Part 2: m > M2: phi_2 = b^3 c_a(w) + b^2 c_b(w), w = 1/b, with c_a, c_b expanded in w (Binet expansions of B, B4 with remainder,
         exact Taylor-model arithmetic in w with an interval remainder rho w^N on [0, W]); A_2(m) = sum of exact 4th differences of
         powers m^-k plus |Delta^4 rem| <= 16 max rem on [m-2, m+2].
Output: logs/alld/A2.json (exact enclosure of A_2(1), flags).  The class TMw and binet_tm are imported by a13_constants.py."""
import sys, json
import mpmath
from mpmath import iv
from a02_jets import lo_str, hi_str
from a03_special import polyg, kappa, binet_beta, binet_rho, ivF, PI


class TMw:
    """f(w) = sum_{k<N} c[k] w^k + r(w), |r(w)| <= rho w^N on [0, W]."""
    def __init__(self, c, rho, N, W):
        self.c, self.rho, self.N, self.W = list(c) + [iv.mpf(0)] * (N - len(c)), iv.mpf(rho), N, W

    def absum(self, start=0):
        return sum((abs(self.c[k]) * self.W ** k for k in range(start, self.N)), iv.mpf(0))

    def __add__(self, o):
        if not isinstance(o, TMw):
            c = list(self.c); c[0] = c[0] + o
            return TMw(c, self.rho, self.N, self.W)
        return TMw([a + b for a, b in zip(self.c, o.c)], self.rho + o.rho, self.N, self.W)

    def __mul__(self, o):
        if not isinstance(o, TMw):
            return TMw([a * o for a in self.c], self.rho * abs(o), self.N, self.W)
        N, W = self.N, self.W
        c = [iv.mpf(0)] * N
        extra = iv.mpf(0)
        for i, a in enumerate(self.c):
            for j, b in enumerate(o.c):
                if i + j < N:
                    c[i + j] += a * b
                else:
                    extra += abs(a * b) * W ** (i + j - N)
        rho = extra + self.absum() * o.rho + o.absum() * self.rho + self.rho * o.rho * W ** N
        return TMw(c, rho, N, W)

    def inv1(self):
        """1/f for f = 1 - y, y(0) = 0, y = O(w^2)."""
        y = self * (-1) + 1
        assert abs(y.c[0]).b == 0 and abs(y.c[1]).b == 0
        eta = y.absum(2) / self.W ** 2 + y.rho * self.W ** (self.N - 2)       # |y| <= eta w^2
        L = self.N // 2
        assert self.N % 2 == 0                  # the tail bound below uses w^(2L) <= W^(2L-N) w^N, i.e. 2L >= N
        S = TMw([iv.mpf(1)], 0, self.N, self.W)
        P = TMw([iv.mpf(1)], 0, self.N, self.W)
        for _ in range(1, L):
            P = P * y
            S = S + P
        assert (eta * self.W ** 2).b < 1
        tail = eta ** L * self.W ** (2 * L - self.N) / (1 - eta * self.W ** 2)
        return TMw(S.c, S.rho + tail, self.N, self.W)


def binet_tm(j, K, W):
    beta = binet_beta(j, K)
    c = [iv.mpf(0)] * (2 * K)
    c[0] = iv.mpf(1)
    for k in range(1, K):
        c[2 * k] = -ivF(beta[k])
    return TMw(c, binet_rho(j, K, 0)[0], 2 * K, W)


def consts():
    A0 = PI / 2 - 1
    T1C = -(iv.mpf(2) / 3 + 5 * PI / 72 + 1 / (3 * PI))
    return A0, T1C


def phi2(m):
    A0, T1C = consts()
    b = iv.mpf(m)
    B = b * kappa(2, b)
    B4 = b ** 3 * kappa(4, b) / 2
    return (-(PI / 2) * (1 + PI / 12) * b ** 3 / B + (PI / 2) * T1C * b ** 2 / B + (PI / 2) * A0 * b ** 3 / B ** 2
            - (A0 ** 2 / 2) * b ** 2 * B4 / B ** 3)


if __name__ == '__main__':
    iv.prec = 160
    A0, T1C = consts()
    M2 = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    P = {0: iv.mpf(0)}
    for m in range(1, M2 + 3):
        P[m] = phi2(m)
    P[-1] = P[1]
    D4 = lambda m: P[m - 2] - 4 * P[m - 1] + 6 * P[m] - 4 * P[m + 1] + P[m + 2]
    A21 = D4(1)
    print("A_2(1) =", mpmath.nstr(A21.a, 12), mpmath.nstr(A21.b, 12))
    bad = [m for m in range(2, M2 + 1) if not D4(m).a > 0]
    print(f"Part 1: A_2(m) > 0 for 2 <= m <= {M2}: {not bad}  (bad: {bad[:10]});  m^5 A_2(m) at m = 10, 100, {M2}:",
          [mpmath.nstr((D4(m) * m ** 5).mid, 6) for m in (10, 100, M2)])
    # ------------------------------------------------------------------ Part 2: m > M2
    K = 6
    W = iv.mpf(1) / (M2 - 1)
    Bt = binet_tm(1, K, W)
    B4t = binet_tm(2, K, W)
    iB = Bt.inv1()
    iB2, iB3 = iB * iB, iB * iB * iB
    ca = iB * (-(PI / 2) * (1 + PI / 12)) + iB2 * ((PI / 2) * A0)          # phi_2 = b^3 ca + b^2 cb
    cb = iB * ((PI / 2) * T1C) + (B4t * iB3) * (-(A0 ** 2) / 2)
    N = ca.N
    print("expansion: c_a,4 =", mpmath.nstr(ca.c[4].mid, 10), " (24 c_a,4 =", mpmath.nstr((24 * ca.c[4]).mid, 8), ")  rho_a, rho_b =",
          mpmath.nstr(ca.rho.b, 4), mpmath.nstr(cb.rho.b, 4))
    m = iv.mpf(M2 + 1)
    lead = 24 * ca.c[4]                     # c_a,4 b^-1: Delta^4 b^-1 >= 24/m^5 (Jensen, s^-5 convex, M_4 mean 0); needs c_a,4 > 0
    assert ca.c[4].a > 0
    minus = iv.mpf(0)
    for k in range(5, N):                       # c_a,k w^(k-3) = c_a,k b^-(k-3), j = k-3 >= 2
        j = k - 3
        minus += abs(ca.c[k]) * j * (j + 1) * (j + 2) * (j + 3) * m ** 5 / (m - 2) ** (j + 4)
    for k in range(3, N):                       # c_b,k b^-(k-2), j = k-2 >= 1
        j = k - 2
        minus += abs(cb.c[k]) * j * (j + 1) * (j + 2) * (j + 3) * m ** 5 / (m - 2) ** (j + 4)
    minus += 16 * m ** 5 * (ca.rho * (m - 2) ** (3 - N) + cb.rho * (m - 2) ** (2 - N))
    ok2 = (lead - minus).a > 0
    # every term of 'minus' decreases in m (m^5/(m-2)^(j+4), j >= 1; m^5 (m-2)^(3-N), N = 12), so m = M2 + 1 is the worst case
    print(f"Part 2 (m >= {M2+1}): m^5 A_2(m) >= 24 c_a,4 - (rest) = {mpmath.nstr(lead.a, 8)} - {mpmath.nstr(minus.b, 4)} > 0: {ok2}")
    print("Also cross-check: series value of m^5 A_2 at m = M2 vs Part 1:", mpmath.nstr((D4(M2) * M2 ** 5).mid, 8))
    ok = bool((not bad) and ok2 and A21.a > -2.7560 and A21.b < -2.7559)
    print("A2 CLAIMS CERTIFIED:", ok)
    json.dump(dict(ok=ok, M2=M2, A21=[lo_str(A21), hi_str(A21)], A2pos=not bad, part2=bool(ok2), iv_prec=iv.prec),
              open('logs/alld/A2.json', 'w'), indent=0)
