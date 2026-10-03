"""ri11: the Radon identity for an arbitrary Hermitian B (PROOF.md s.3.5, Theorem RI-B).

B = diag(b) with distinct values b_1 < ... < b_n (multiplicities m_k, spectral projections Pi_k), H Hermitian,
H_d = sum_k Pi_k H Pi_k.  For tau in a gap (b_l, b_{l+1}) the roots y of det(H + c - y(B - tau)) are the eigenvalues of
(B - tau)^{-1}(H + c).
 (1) complex form: for Im c > 0,  Psi_B(c) := sum_gaps int (S_+ - S0_+) dtau = E(c) = Tr[(H_d+c)Log(H_d+c)] - Tr[(H+c)Log(H+c)],
     S_+ = sum of the C_+ roots (there are sum_{k>l} m_k of them in gap l), S0_+ = sum_{k>l} (Tr Pi_k H Pi_k + m_k c)/(b_k - tau);
 (2) interior ends: Lam_+ - Lam0_+ has the same limit at b_k from the left and from the right;
 (3) RI-B:  (1/2pi) int_{b_1}^{b_n} sum_i |Im y_i(tau)| dtau = Tr H_+ - Tr (H_d)_+   (c = 0), branch points located by a sign scan
     of the discriminant (sign = (-1)^{#non-real pairs}) with geometric refinement at the gap ends, plus bisection.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import rand_herm, to_mp, eigvals

mp.mp.dps = 30

class GenB:
    def __init__(self, H, bvals, name):
        self.name = name; self.Hf = H; self.M = H.shape[0]
        self.b = [mp.mpf(x) for x in bvals]
        self.levels = sorted(set(self.b))
        self.H = to_mp(H)
        M = self.M
        self.Hd = mp.matrix(M, M)
        for i in range(M):
            for j in range(M):
                if self.b[i] == self.b[j]:
                    self.Hd[i, j] = self.H[i, j]
        self.blocks = {}
        for lev in self.levels:
            idx = [i for i in range(M) if self.b[i] == lev]
            sub = mp.matrix([[self.H[i, j] for j in idx] for i in idx]) if len(idx) > 1 else mp.matrix([[self.H[idx[0], idx[0]]]])
            mu = [mp.re(e) for e in mp.eigh(sub, eigvals_only=True)] if len(idx) > 1 else [mp.re(sub[0, 0])]
            self.blocks[lev] = (len(idx), mu)
        self.lam = [mp.re(e) for e in mp.eigh(self.H, eigvals_only=True)]
        self.lam0 = [mp.re(e) for e in mp.eigh(self.Hd, eigvals_only=True)]

    def roots(self, tau, c):
        M = self.M
        Y = mp.matrix(M, M)
        for i in range(M):
            for j in range(M):
                Y[i, j] = (self.H[i, j] + (c if i == j else 0))/(self.b[i] - tau)
        return eigvals(Y)

    def roots_gap(self, lo, hi, s2, c2, c):
        """roots for tau = lo + (hi - lo) s2 = hi - (hi - lo) c2, with b_i - tau formed without cancellation
        (every b_i is <= lo or >= hi when tau is in the gap (lo, hi))."""
        M = self.M; w = hi - lo
        Y = mp.matrix(M, M)
        for i in range(M):
            den = (self.b[i] - lo) - w*s2 if self.b[i] <= lo else (self.b[i] - hi) + w*c2
            for j in range(M):
                Y[i, j] = (self.H[i, j] + (c if i == j else 0))/den
        return eigvals(Y)

    def S0(self, tau, c, above):
        tot = mp.mpc(0)
        for lev in self.levels:
            if (lev > tau) == above:
                m, mu = self.blocks[lev]
                tot += (sum(mu, mp.mpf(0)) + m*c)/(lev - tau)
        return tot

    def Lam0(self, tau, c):
        tot = mp.mpc(0)
        for lev in self.levels:
            if lev > tau:
                m, mu = self.blocks[lev]
                tot += sum((mp.log((x + c)/(lev - tau)) for x in mu), mp.mpc(0))
        return tot

    def diff_plus(self, tau, c, lo, hi):
        eps = mp.mpf(10)**(5 - mp.mp.dps)*(hi - lo)
        tau = min(max(tau, lo + eps), hi - eps)
        ys = self.roots(tau, c)
        if tau - lo <= hi - tau:
            return sum((y for y in ys if mp.im(y) > 0), mp.mpc(0)) - self.S0(tau, c, True)
        return self.S0(tau, c, False) - sum((y for y in ys if mp.im(y) < 0), mp.mpc(0))

    def Lam_plus(self, tau, c):
        return sum((mp.log(y) for y in self.roots(tau, c) if mp.im(y) > 0), mp.mpc(0))

    def Psi(self, c):
        tot = mp.mpc(0)
        for lo, hi in zip(self.levels[:-1], self.levels[1:]):
            tot += mp.quad(lambda t: self.diff_plus(t, c, lo, hi), mp.linspace(lo, hi, 5))
        return tot

    def E(self, c):
        zl = lambda z: z*mp.log(z)
        return sum((zl(l + c) for l in self.lam0), mp.mpc(0)) - sum((zl(l + c) for l in self.lam), mp.mpc(0))

    def R(self):
        return sum((max(l, 0) for l in self.lam), mp.mpf(0)) - sum((max(l, 0) for l in self.lam0), mp.mpf(0))

    # ---- real axis
    def sgn_disc(self, tau):
        ys = self.roots(tau, mp.mpf(0))
        pr = mp.mpc(1)
        for i in range(self.M):
            for j in range(i + 1, self.M):
                pr *= (ys[i] - ys[j])**2
        return mp.sign(mp.re(pr))

    def L(self):
        total = mp.mpf(0); nbp = 0
        for lo, hi in zip(self.levels[:-1], self.levels[1:]):
            w = hi - lo
            with mp.workdps(2*mp.mp.dps):
                pts = [lo + w*mp.sin(mp.pi/2*mp.mpf(j)/400)**2 for j in range(1, 400)]
                pts += [lo + w*mp.mpf(10)**(-j) for j in range(3, mp.mp.dps//2)] + [hi - w*mp.mpf(10)**(-j) for j in range(3, mp.mp.dps//2)]
                pts = sorted(set(pts))
                sg = [self.sgn_disc(t) for t in pts]
                bps = []
                for (a, b, sa, sb) in zip(pts[:-1], pts[1:], sg[:-1], sg[1:]):
                    if sa*sb < 0:
                        for _ in range(400):
                            mid = (a + b)/2; sm = self.sgn_disc(mid)
                            if sm*sa > 0: a = mid
                            else: b = mid
                            if b - a < mp.mpf(10)**(-mp.mp.dps//2 - 3)*min(a - lo, hi - b): break
                        bps.append((a + b)/2)
            nbp += len(bps)
            ths = [mp.mpf(0)] + [mp.asin(mp.sqrt((t - lo)/w)) for t in bps] + [mp.pi/2]
            for ta, tb in zip(ths[:-1], ths[1:]):
                m = (ta + tb)/2
                ys = self.roots(lo + w*mp.sin(m)**2, mp.mpf(0))
                k = sum(1 for y in ys if mp.im(y) > mp.mpf(10)**(-mp.mp.dps//2)*(1 + abs(y)))
                if k == 0:
                    continue
                def f(th, k=k):
                    s, cth = mp.sin(th), mp.cos(th)
                    if s == 0 or cth == 0:
                        return mp.mpf(0)
                    mm = min(s*s, cth*cth)
                    boost = int(1.5*max(0, -mp.log10(mm))) + 10
                    with mp.workdps(mp.mp.dps + min(boost, 3*mp.mp.dps)):
                        ims = sorted((abs(mp.im(y)) for y in self.roots_gap(lo, hi, s*s, cth*cth, mp.mpf(0))), reverse=True)
                        v = sum(ims[:2*k], mp.mpf(0))*w*2*s*cth
                    return +v
                total += mp.quad(f, mp.linspace(ta, tb, 4))
        return total/(2*mp.pi), nbp

rng = np.random.default_rng(77)
cases = [((0, 0.37, 1), 3), ((-1, 0.2, 0.5, 2), 4), ((0, 0.6, 0.6, 1), 4), ((0, 0.3, 0.3, 0.31, 1), 5), ((-0.5, 0.1, 0.1, 0.9, 2.0, 2.0), 6)]
insts = [GenB(rand_herm(rng, M, 1.0), b, f'specB={b}') for (b, M) in cases]

print('(1) complex form Psi_B(c) = E(c)')
w1 = mp.mpf(0)
for G in insts:
    for c in [mp.mpc('0.3', '0.8'), mp.mpc('-0.7', '0.2')]:
        ps = G.Psi(c); e = G.E(c); w1 = max(w1, abs(ps - e))
    print(f'  {G.name:40s} last c: Psi = {mp.nstr(ps, 18):>44s}  E = {mp.nstr(e, 18):>44s}')
print(f'  max |Psi_B - E| = {mp.nstr(w1, 3)}')

print('(2) interior ends: limits of Lam_+ - Lam0_+ from both sides of each interior b_k')
w2 = mp.mpf(0)
for G in insts:
    c = mp.mpc('0.2', '0.6')
    for lev in G.levels[1:-1]:
        e = mp.mpf('1e-9')
        left = G.Lam_plus(lev - e, c) - G.Lam0(lev - e, c); right = G.Lam_plus(lev + e, c) - G.Lam0(lev + e, c)
        w2 = max(w2, abs(left - right))
print(f'  max |left limit - right limit| at distance 1e-9 = {mp.nstr(w2, 3)}   (O(distance) expected)')

print('(3) RI-B at c = 0')
w3 = mp.mpf(0)
for G in insts:
    Lv, nbp = G.L(); Rv = G.R(); w3 = max(w3, abs(Lv - Rv))
    print(f'  {G.name:40s} #branchpts={nbp:2d}  L_B = {mp.nstr(Lv, 22):>26s}  R = {mp.nstr(Rv, 22):>26s}  diff = {mp.nstr(abs(Lv - Rv), 3)}')
print(f'  max |L_B - R| = {mp.nstr(w3, 3)}')
print('ALL OK' if w1 < 1e-20 and w2 < 1e-6 and w3 < 1e-15 else 'CHECK')
