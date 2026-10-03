"""Core numerics for Q_RI (the Radon identity), see PROOF.md.

Notation (PROOF.md s.0):  H Hermitian M x M, P = diag(1,...,1,0,...,0) of rank M - r, B = 1 - P (rank r), H_d = BHB + PHP.
For 0 < tau < 1 and c in the closed upper half plane, the roots y of  p(y; tau, c) = det(H + c - y(P - tau))  are the
eigenvalues of  Y(tau, c) = (P - tau)^{-1}(H + c) = (P/(1-tau) - B/tau)(H + c).
For Im c > 0 (Lemma A): no real roots, M - r roots in C_+, r roots in C_-.
  S_+   = sum of the C_+ roots,     Lam_+ = sum of Log over the C_+ roots (principal Log),
  S0_+  = (Tr_P PHP + (M - r)c)/(1 - tau),   Lam0_+ = sum_k Log((mu_k + c)/(1 - tau))   (pinched pencil, explicit).
  Psi(c) = int_0^1 (S_+ - S0_+) dtau,   E(c) = Tr[(H_d + c)Log(H_d + c)] - Tr[(H + c)Log(H + c)].
RI:  L(H) := (1/2pi) int_0^1 sum_i |Im y_i(tau, 0)| dtau  =  R(H) := Tr H_+ - Tr (H_d)_+.
P is taken diagonal without loss of generality (unitary invariance of both sides).
"""
import numpy as np
import mpmath as mp

# ------------------------------------------------------------------ instances
def rand_herm(rng, M, scale=1.0):
    X = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    return (X + X.conj().T)/2*scale

def eigvals(A):
    """eigenvalues of an mp.matrix (mpmath.eig returns a tuple for 1 x 1 input even with left=right=False)."""
    if A.rows == 1:
        return [A[0, 0]]
    return list(mp.eig(A, left=False, right=False))

def to_mp(A):
    return mp.matrix([[mp.mpc(complex(A[i, j])) for j in range(A.shape[1])] for i in range(A.shape[0])])

class Inst:
    """H (numpy complex Hermitian), r = rank B; P = diag(1_{M-r}, 0_r).  Stores mp copies at the current mp.dps."""
    def __init__(self, H, r, name=''):
        self.Hf = np.array(H, dtype=complex); self.M = self.Hf.shape[0]; self.r = r; self.name = name
        M = self.M
        self.Pf = np.diag([1.0]*(M - r) + [0.0]*r); self.Bf = np.eye(M) - self.Pf
        self.refresh()

    def refresh(self):
        M, r = self.M, self.r
        self.H = to_mp(self.Hf)
        self.P = mp.diag([1]*(M - r) + [0]*r); self.B = mp.eye(M) - self.P
        self.Hd = self.B*self.H*self.B + self.P*self.H*self.P
        HP = mp.matrix(M - r, M - r); HB = mp.matrix(r, r)
        for i in range(M - r):
            for j in range(M - r):
                HP[i, j] = self.H[i, j]
        for i in range(r):
            for j in range(r):
                HB[i, j] = self.H[M - r + i, M - r + j]
        self.mu = [mp.re(e) for e in mp.eigh(HP, eigvals_only=True)] if M - r > 0 else []   # spec PHP|ranP
        self.beta = [mp.re(e) for e in mp.eigh(HB, eigvals_only=True)] if r > 0 else []    # spec BHB|ranB
        self.lam = [mp.re(e) for e in mp.eigh(self.H, eigvals_only=True)]                  # spec H
        self.lam0 = sorted(self.mu + self.beta)                                            # spec H_d
        self.normH = max(abs(x) for x in self.lam)
        self.frobBHP2 = mp.re(sum(abs(self.H[i, j])**2 for i in range(M - r) for j in range(M - r, M)))

    # ---------------- pencil roots
    def Y(self, tau, c):
        M = self.M
        Jinv = self.P/(1 - tau) - self.B/tau
        return Jinv*(self.H + c*mp.eye(M))

    def roots(self, tau, c):
        return eigvals(self.Y(tau, c))

    def split(self, tau, c):
        """roots in C_+ and C_- (for Im c > 0 there are no real roots)."""
        ys = self.roots(tau, c)
        up = [y for y in ys if mp.im(y) > 0]; dn = [y for y in ys if mp.im(y) < 0]
        return up, dn

    def S_plus(self, tau, c):
        up, dn = self.split(tau, c)
        assert len(up) == self.M - self.r, (len(up), self.M - self.r, tau, c)
        return sum(up, mp.mpc(0))

    def Lam_plus(self, tau, c):
        up, dn = self.split(tau, c)
        assert len(up) == self.M - self.r
        return sum((mp.log(y) for y in up), mp.mpc(0))

    def S0_plus(self, tau, c):
        return (sum(self.mu, mp.mpf(0)) + (self.M - self.r)*c)/(1 - tau)

    def Lam0_plus(self, tau, c):
        return sum((mp.log((m + c)/(1 - tau)) for m in self.mu), mp.mpc(0))

    def S_minus(self, tau, c):
        up, dn = self.split(tau, c)
        return sum(dn, mp.mpc(0))

    def S0_minus(self, tau, c):
        return -(sum(self.beta, mp.mpf(0)) + self.r*c)/tau

    def diff_plus(self, tau, c):
        """S_+ - S0_+, evaluated in the numerically safer form near tau = 1 (S0_- - S_-, equal by the trace identity).
        tau is clamped to [eps, 1 - eps], eps = 10^(5 - dps): the integrand is bounded at both ends for Im c > 0 (Lemma D),
        so this changes integrals by O(eps) only, and avoids 1 - tau = 0 at extreme tanh-sinh nodes."""
        eps = mp.mpf(10)**(5 - mp.mp.dps)
        tau = min(max(tau, eps), 1 - eps)
        if tau <= mp.mpf(1)/2:
            return self.S_plus(tau, c) - self.S0_plus(tau, c)
        return self.S0_minus(tau, c) - self.S_minus(tau, c)

    # ---------------- closed forms
    def E(self, c):
        zlog = lambda z: z*mp.log(z) if z != 0 else mp.mpc(0)
        return sum((zlog(l + c) for l in self.lam0), mp.mpc(0)) - sum((zlog(l + c) for l in self.lam), mp.mpc(0))

    def Theta1(self, c):
        return sum((mp.log(l + c) for l in self.lam), mp.mpc(0)) - sum((mp.log(l + c) for l in self.lam0), mp.mpc(0))

    def R(self, c0=0):
        return sum((max(l + c0, 0) for l in self.lam), mp.mpf(0)) - sum((max(l + c0, 0) for l in self.lam0), mp.mpf(0))

    def Psi(self, c, **kw):
        f = lambda t: self.diff_plus(t, c)
        return mp.quad(f, [0, mp.mpf(1)/4, mp.mpf(1)/2, mp.mpf(3)/4, 1], **kw)

    # ---------------- real-axis quantities (RI)
    def roots_split_tau(self, s2, c2, c):
        """roots for tau = s2, 1 - tau = c2 given separately (no cancellation near tau = 1)."""
        M = self.M
        Jinv = self.P/c2 - self.B/s2
        return eigvals(Jinv*(self.H + c*mp.eye(M)))

    def imsum(self, tau, c0=0):
        """sum_i |Im y_i(tau, c0)| for real c0."""
        return sum((abs(mp.im(y)) for y in self.roots(tau, mp.mpf(c0))), mp.mpf(0))

    def imsum_theta(self, th, c0, k):
        """(sum of the 2k largest |Im y_i|) * sin(2 theta),  tau = sin^2 theta, 1 - tau = cos^2 theta; on a piece between
        consecutive branch points exactly k conjugate pairs are non-real.  Working precision is raised near the ends because
        the roots there have size up to 1/min(tau, 1 - tau) while the non-real ones have size <= K/sqrt(tau(1 - tau))."""
        if k == 0:
            return mp.mpf(0)
        s, c = mp.sin(th), mp.cos(th)
        s2, c2 = s*s, c*c
        if s2 == 0 or c2 == 0:
            return mp.mpf(0)
        m = min(s2, c2)
        boost = int(1.5*max(0, -mp.log10(m))) + 10
        with mp.workdps(mp.mp.dps + min(boost, 3*mp.mp.dps)):
            ys = self.roots_split_tau(s2, c2, mp.mpf(c0))
            ims = sorted((abs(mp.im(y)) for y in ys), reverse=True)
            val = sum(ims[:2*k], mp.mpf(0))*2*s*c
        return +val

    def disc(self, tau, c0=0):
        """y-discriminant of p(y; tau, c0) = lead^{2M-2} prod_{i<j}(y_i - y_j)^2 (real for real c0), a polynomial in tau."""
        M, r = self.M, self.r
        lead = (tau - 1)**(M - r)*tau**r          # det(tau - P) = leading coeff of det(H + c - y(P - tau)) up to (-1)^M
        ys = self.roots(tau, mp.mpf(c0))
        pr = mp.mpc(1)
        for i in range(M):
            for j in range(i + 1, M):
                pr *= (ys[i] - ys[j])**2
        return mp.re(lead**(2*M - 2)*pr)

    def disc_reduced(self, tau, c0=0):
        """disc / (tau^{r(r-1)} (1 - tau)^{(M-r)(M-r-1)}): the discriminant vanishes to these orders at tau = 0, 1 (r roots of
        size ~ 1/tau, resp. M - r roots of size ~ 1/(1 - tau)); the quotient is a polynomial of degree <= 2 r (M - r)."""
        M, r = self.M, self.r
        return self.disc(tau, c0)/(tau**(r*(r - 1))*(1 - tau)**((M - r)*(M - r - 1)))

    def breakpoints(self, c0=0, nscan=600):
        """real zeros in (0,1) of the reduced discriminant: Chebyshev interpolation at doubled precision + polyroots, then a
        sign scan (uniform in theta, tau = sin^2 theta, plus geometric points near both ends) with bisection as a safeguard."""
        M, r = self.M, self.r
        deg = 2*r*(M - r)
        n = deg + 1
        out = []; self.aux_nodes = []
        with mp.workdps(2*mp.mp.dps):
            nodes = [(1 + mp.cos(mp.pi*(k + mp.mpf(1)/2)/n))/2 for k in range(n)]
            vals = [self.disc_reduced(u, c0) for u in nodes]
            zs = [2*u - 1 for u in nodes]
            V = mp.matrix([[z**k for k in range(n)] for z in zs])
            cf = mp.lu_solve(V, mp.matrix(vals))
            coeffs = [cf[k] for k in range(n)][::-1]
            scale = max(abs(x) for x in coeffs)
            while len(coeffs) > 1 and abs(coeffs[0]) < scale*mp.mpf(10)**(-mp.mp.dps//2):
                coeffs = coeffs[1:]
            if len(coeffs) > 1:
                rts = mp.polyroots(coeffs, maxsteps=4000, extraprec=4*mp.mp.dps, error=False)
                for z in rts:
                    if abs(mp.im(z)) < mp.mpf(10)**(-mp.mp.dps//6) and -1 < mp.re(z) < 1:
                        out.append((1 + mp.re(z))/2)
                    elif abs(mp.im(z)) < mp.mpf('0.1') and -1 < mp.re(z) < 1:
                        # near-real complex zero: no branch point on (0,1), but a nearby complex one -> extra quadrature nodes
                        tc, w = (1 + mp.re(z))/2, abs(mp.im(z))/2
                        self.aux_nodes += [+(tc + j*w) for j in (-10, -3, -1, 0, 1, 3, 10) if 0 < tc + j*w < 1]
        out = [+t for t in out if 0 < t < 1]
        # safeguard scan (doubled precision; geometric points near both ends down to 10^(-dps/2))
        with mp.workdps(2*mp.mp.dps):
            jmax = max(3, mp.mp.dps//4)
            pts = [mp.sin(mp.pi/2*mp.mpf(j)/nscan)**2 for j in range(1, nscan)]
            pts += [mp.mpf(10)**(-j) for j in range(2, jmax)] + [1 - mp.mpf(10)**(-j) for j in range(2, jmax)]
            pts = sorted(set(pts))
            sg = [mp.sign(self.disc_reduced(t, c0)) for t in pts]
            for (a, b, sa, sb) in zip(pts[:-1], pts[1:], sg[:-1], sg[1:]):
                if sa*sb < 0 and not any(a <= t <= b for t in out):
                    for _ in range(400):
                        mid = (a + b)/2
                        sm = mp.sign(self.disc_reduced(mid, c0))
                        if sm*sa > 0: a, sa = mid, sm
                        else: b = mid
                        if b - a < mp.mpf(10)**(-mp.mp.dps//2 - 3)*min(a, 1 - b): break
                    out.append((a + b)/2)
        out = [+t for t in out]
        out = sorted(out)
        ded = []
        for t in out:
            if not ded or t - ded[-1] > mp.mpf(10)**(-mp.mp.dps//2)*(1 + t):
                ded.append(t)
        return ded

    def L(self, c0=0, bps=None):
        """(1/2pi) int_0^1 sum |Im y_i(tau, c0)| dtau in theta (tau = sin^2 theta), split at the branch points."""
        if bps is None:
            bps = self.breakpoints(c0)
        aux = [t for t in getattr(self, 'aux_nodes', []) if all(abs(t - b) > mp.mpf(10)**(-8) for b in bps)]
        ths = sorted(set([mp.mpf(0)] + [mp.asin(mp.sqrt(t)) for t in list(bps) + aux] + [mp.pi/2]))
        val = mp.mpf(0)
        for a, b in zip(ths[:-1], ths[1:]):
            if b - a <= 0:
                continue
            m = (a + b)/2
            ys = self.roots_split_tau(mp.sin(m)**2, mp.cos(m)**2, mp.mpf(c0))
            k = sum(1 for y in ys if mp.im(y) > mp.mpf(10)**(-mp.mp.dps//2)*(1 + abs(y)))
            if k:
                val += mp.quad(lambda th: self.imsum_theta(th, c0, k), [a, b])
        return val/(2*mp.pi)


def standard_instances(seed=11):
    rng = np.random.default_rng(seed)
    out = []
    for (M, r, sc) in [(2, 1, 1.0), (3, 1, 1.0), (3, 2, 2.0), (4, 1, 1.0), (4, 2, 1.5), (4, 3, 1.0), (5, 2, 1.0), (5, 3, 3.0), (6, 3, 1.0)]:
        out.append(Inst(rand_herm(rng, M, sc), r, f'rand_M{M}_r{r}'))
    # degenerate / structured cases
    M = 4; H = np.diag([1.0, 1.0, -0.5, 2.0]).astype(complex); H[0, 2] = H[2, 0] = 0.7; H[1, 3] = 0.3j; H[3, 1] = -0.3j
    out.append(Inst(H, 2, 'repeated_PHP'))
    M = 4; H = np.zeros((M, M), complex); H[0, 3] = H[3, 0] = 1.0; H[1, 2] = 2.0 + 1j; H[2, 1] = 2.0 - 1j
    out.append(Inst(H, 2, 'zero_diag_blocks'))
    rng2 = np.random.default_rng(5); H = rand_herm(rng2, 5, 1.0); H[:3, 3:] *= 1e-3; H[3:, :3] *= 1e-3
    out.append(Inst(H, 2, 'near_commuting'))
    return out
