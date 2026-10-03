"""q06: high-precision test of the closed form for a GENERAL Hermitian B = sum_k b_k Pi_k (BMV side result, PROOF.md s.7).
  (i)  tau-marginal: int F(s,tau) ds = sum_{k<l, b_k < tau < b_l} ||Pi_k A Pi_l||_F^2/(b_l - b_k)   (piecewise constant in tau);
  (ii) Radon slices crossing the interior lines tau = b_k:  int_{b_1}^{b_n} F(w + xi tau, tau) dtau = U_xi(w),
       U_xi = convex potential of spec(A - xi B) against spec(A_d - xi B), A_d = sum_k Pi_k A Pi_k (pinching).
A line part gamma (x) delta(tau - b_k) on an interior line would show up in (ii) as a defect gamma(w + xi b_k).
usage: python q06_generalB_hp.py dps"""
import numpy as np, mpmath as mp, sys, time
from q_core import to_mp

def setup(seed, M, bs, mult, scale):
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); U, _ = np.linalg.qr(Z)
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); A = scale*(G + G.conj().T)/2
    lab = np.repeat(np.arange(len(bs)), mult)          # eigenvalue label of each column of U
    return A, U, lab

class GB:
    def __init__(self, A, U, lab, bs):
        self.M = A.shape[0]; self.bs = [mp.mpf(b) for b in bs]
        Um, _ = mp.qr(to_mp(U))                       # exactly unitary at working precision
        self.A = to_mp(A)
        self.Pis = []
        for k in range(len(bs)):
            cols = [j for j in range(self.M) if lab[j] == k]
            V = mp.matrix(self.M, len(cols))
            for c, j in enumerate(cols):
                for i in range(self.M): V[i, c] = Um[i, j]
            self.Pis.append(V)
        self.B = sum((self.bs[k]*(V*V.H) for k, V in enumerate(self.Pis)), mp.zeros(self.M, self.M))
        self.Ad = sum(((V*V.H)*self.A*(V*V.H) for V in self.Pis), mp.zeros(self.M, self.M))
        self.Af = A; self.Bf = np.array(self.B.tolist(), dtype=complex)

    def roots(self, s, tau):
        Jinv = sum(((V*V.H)/(b - tau) for b, V in zip(self.bs, self.Pis)), mp.zeros(self.M, self.M))   # exact spectral inverse
        X = Jinv*(self.A - s*mp.eye(self.M))
        return mp.eig(X, left=False, right=False)

    def F(self, s, tau):
        if not (self.bs[0] < tau < self.bs[-1]) or any(tau == b for b in self.bs):
            return mp.mpf(0)
        thr = mp.mpf(10)**(-(mp.mp.dps*2)//3)
        return sum((abs(mp.im(e)) for e in self.roots(s, tau) if abs(mp.im(e)) > thr*max(1, abs(e))), mp.mpf(0))/(2*mp.pi)

    def count(self, s, tau):
        if not (self.bs[0] < tau < self.bs[-1]) or any(tau == b for b in self.bs):
            return -1
        ev = self.roots(s, tau); thr = mp.mpf(10)**(-(mp.mp.dps*2)//3)*max([mp.mpf(1)] + [abs(e) for e in ev])
        return sum(1 for e in ev if abs(mp.im(e)) > thr)

    def countf(self, s, tau):
        M = self.M; x = np.linalg.eigvals(np.linalg.solve(self.Bf - tau*np.eye(M), self.Af - s*np.eye(M)))
        return int(np.sum(np.abs(x.imag) > 1e-8*max(1, np.abs(x).max())))

    def U(self, xi, w):
        lam = [mp.re(e) for e in mp.eigh(self.A - xi*self.B, eigvals_only=True)]
        lam0 = [mp.re(e) for e in mp.eigh(self.Ad - xi*self.B, eigvals_only=True)]
        return sum((max(w - l, 0) for l in lam), mp.mpf(0)) - sum((max(w - l, 0) for l in lam0), mp.mpf(0))

    def marg_pred(self, tau):
        tot = mp.mpf(0)
        for k in range(len(self.bs)):
            for l in range(k + 1, len(self.bs)):
                if self.bs[k] < tau < self.bs[l]:
                    X = self.Pis[k].H*self.A*self.Pis[l]
                    tot += sum(abs(X[i, j])**2 for i in range(X.rows) for j in range(X.cols))/(self.bs[l] - self.bs[k])
        return tot

def path_int(C, path, u0, u1, extra, ngrid=6000):
    us = np.linspace(float(u0), float(u1), ngrid)[1:-1]
    cs = []
    for u in us:
        s, t = path(mp.mpf(u))
        cs.append(C.countf(float(s), float(t)) if C.bs[0] < t < C.bs[-1] else -1)
    bps = [mp.mpf(u0)] + [mp.mpf(e) for e in extra]
    for k in range(len(us) - 1):
        if cs[k] != cs[k + 1]:
            a, b = mp.mpf(us[k]), mp.mpf(us[k + 1]); ca = C.count(*path(a))
            for _ in range(int(mp.mp.dps*3.5)):
                m = (a + b)/2
                if C.count(*path(m)) == ca: a = m
                else: b = m
            bps.append((a + b)/2)
    bps.append(mp.mpf(u1)); bps = sorted(set(bps))
    tot = mp.mpf(0); err = mp.mpf(0)
    for a, b in zip(bps[:-1], bps[1:]):
        v, e = mp.quad(lambda u: C.F(*path(u)), [a, b], error=True, maxdegree=10); tot += v; err += e
    return tot, err

if __name__ == "__main__":
    mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    cases = [(3, [0.0, 0.37, 1.0], [1, 1, 1], 1.0, 0), (4, [-1.0, 0.2, 0.5, 2.0], [1, 1, 1, 1], 3.0, 1),
             (4, [0.0, 0.6, 1.0], [1, 2, 1], 20.0, 2), (5, [0.0, 0.3, 0.31, 1.0], [1, 2, 1, 1], 5.0, 3)]
    for (M, bs, mult, scale, seed) in cases:
        A, U, lab = setup(seed, M, bs, mult, scale); C = GB(A, U, lab, bs); t0 = time.time()
        print(f"=== M={M} spec B = {bs} mult {mult}, scale {scale}  spec A = {np.round(np.linalg.eigvalsh(A), 3)}", flush=True)
        lo, hi = [mp.re(e) for e in mp.eigh(C.A, eigvals_only=True)][0], [mp.re(e) for e in mp.eigh(C.A, eigvals_only=True)][-1]
        worst = mp.mpf(0)
        for k in range(len(bs) - 1):            # one tau in each gap
            tau = C.bs[k] + (C.bs[k + 1] - C.bs[k])*mp.mpf('0.4142')
            v, e = path_int(C, lambda u, tau=tau: (u, tau), lo, hi, [])
            pr = C.marg_pred(tau); dev = abs(v - pr)/pr; worst = max(worst, dev)
            print(f"  marginal tau={mp.nstr(tau,5)}: int = {mp.nstr(v, 18)}  predicted = {mp.nstr(pr, 18)}  rel.dev {mp.nstr(dev, 3)} (qerr {mp.nstr(e, 2)})", flush=True)
        rng = np.random.default_rng(100 + seed)
        for _ in range(3):
            xi = mp.mpf(float(rng.normal()*2*scale))
            lam = sorted(np.linalg.eigvalsh(A - float(xi)*C.Bf))
            w = mp.mpf(float(lam[0] + (lam[-1] - lam[0])*rng.uniform(0.25, 0.75)))
            Uv = C.U(xi, w)
            v, e = path_int(C, lambda u, xi=xi, w=w: (w + xi*u, u), C.bs[0], C.bs[-1], [])   # no breakpoint at interior b_k: F is smooth there, (B - tau) singular
            dev = abs(v - Uv)/max(abs(Uv), mp.mpf(10)**-20); worst = max(worst, dev)
            print(f"  Radon xi={mp.nstr(xi,5)} w={mp.nstr(w,6)}: int = {mp.nstr(v, 18)}  U = {mp.nstr(Uv, 18)}  rel.dev {mp.nstr(dev, 3)} (qerr {mp.nstr(e, 2)})", flush=True)
        print(f"  --> worst {mp.nstr(worst, 3)}  [{time.time()-t0:.0f}s]", flush=True)
