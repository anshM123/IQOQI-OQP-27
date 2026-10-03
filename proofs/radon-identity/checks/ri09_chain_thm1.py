"""ri09: the deduction RI  =>  Theorem 1 of Q_2bmv (2BMV), step by step (PROOF.md s.4).

g Hermitian, F(s,tau) = (1/2pi) sum_i |Im x_i(s,tau)|, x_i roots of det(g - s - x(P - tau)),
D(a,t) = Tr e^{ag - tP} - e^{-t} Tr_P e^{aPgP} - Tr_B e^{aBgB}.
 (a) change of variables: on the line s = w + xi tau the roots are x = xi + y with y the roots of det(H - y(P - tau)),
     H = g - xi P - w  (pointwise check of the integrands), and H_d = g_d - xi P - w;
 (b) RI for this H gives the Radon slice:  int_0^1 F(w + xi tau, tau) dtau = U_xi(w)  (both forms of U_xi agree);
 (c) Lemma 3(b) for real a != 0 with the one-line computation  int e^{aw}(lam - w)_+ dw = e^{a lam}/a^2 (a > 0):
       int e^{aw} U_xi(w) dw = D(a, a xi)/a^2;
 (d) full chain numerically for real (a, t):  int_R e^{aw} [ (1/2pi) int_0^1 sum|Im y| dtau ](w) dw  (inner integral by
     pencil quadrature, NOT by the RI formula; outer by Gauss-Legendre between the kinks of U_xi)  vs  D(a,t)/a^2, xi = t/a;
 (e) one genuinely complex (a, t) (t/a not real): direct 2D integral of e^{as - t tau} F vs D(a,t)/a^2 (moderate accuracy;
     this is the analytic-continuation step; cf. Q_2bmv/q01).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, rand_herm, eigvals

mp.mp.dps = 20
rng = np.random.default_rng(44)

def D(I, a, t):
    M, r = I.M, I.r
    tot = mp.expm(a*I.H - t*I.P)
    trf = sum(tot[i, i] for i in range(M))
    eP = sum((mp.exp(a*m) for m in I.mu), mp.mpf(0)); eB = sum((mp.exp(a*b) for b in I.beta), mp.mpf(0))
    return trf - mp.exp(-t)*eP - eB

def spec_xi(I, xi):
    lam = sorted([mp.re(e) for e in mp.eigh(I.H - xi*I.P, eigvals_only=True)])
    lam0 = sorted(list(I.beta) + [m - xi for m in I.mu])
    return lam, lam0

def U(I, xi, w):
    lam, lam0 = spec_xi(I, xi)
    return sum((max(l - w, 0) for l in lam), mp.mpf(0)) - sum((max(l - w, 0) for l in lam0), mp.mpf(0))

def U_alt(I, xi, w):
    lam, lam0 = spec_xi(I, xi)
    return sum((max(w - l, 0) for l in lam), mp.mpf(0)) - sum((max(w - l, 0) for l in lam0), mp.mpf(0))

g = rand_herm(rng, 4, 1.0); G = Inst(g, 2, 'g_M4_r2')
# (a) pointwise
worst_a = mp.mpf(0)
for k in range(10):
    xi, w, tau = mp.mpf(rng.normal()), mp.mpf(rng.normal()), mp.mpf(rng.uniform(0.05, 0.95))
    s = w + xi*tau
    xs = G.roots(tau, -s)
    Hx = g - float(xi)*np.diag([1.0]*2 + [0.0]*2) - float(w)*np.eye(4)
    J = Inst(np.array(Hx), 2)
    # use the exact mp values (avoid float rounding of xi, w): build H in mp directly
    J.H = G.H - xi*G.P - w*mp.eye(4)
    ys = [y + xi for y in J.roots(tau, 0)]
    rest = list(ys); dmax = mp.mpf(0)
    for p in xs:                                   # greedy nearest matching (sorting can pair conjugates crosswise)
        j = min(range(len(rest)), key=lambda k: abs(rest[k] - p)); dmax = max(dmax, abs(rest[j] - p)); rest.pop(j)
    worst_a = max(worst_a, dmax)
print(f'(a) roots on the line s = w + xi tau equal xi + (roots for H = g - xi P - w): max diff {mp.nstr(worst_a, 3)}')

# (b) both forms of U_xi; RI-slice at a few (xi, w) with the pencil quadrature
worst_b = mp.mpf(0); worst_b2 = mp.mpf(0)
for (xi, w) in [(mp.mpf('0.3'), mp.mpf('-0.2')), (mp.mpf('-1.1'), mp.mpf('0.5')), (mp.mpf('2.0'), mp.mpf('-1.0'))]:
    worst_b = max(worst_b, abs(U(G, xi, w) - U_alt(G, xi, w)))
    J = Inst(np.eye(4), 2); J.H = G.H - xi*G.P - w*mp.eye(4)
    # recompute block data for J from its mp H
    J.mu = [mp.re(e) for e in mp.eigh(mp.matrix([[J.H[i, j] for j in range(2)] for i in range(2)]), eigvals_only=True)]
    J.beta = [mp.re(e) for e in mp.eigh(mp.matrix([[J.H[i, j] for j in range(2, 4)] for i in range(2, 4)]), eigvals_only=True)]
    J.lam = [mp.re(e) for e in mp.eigh(J.H, eigvals_only=True)]; J.lam0 = sorted(J.mu + J.beta)
    Lv = J.L(0)
    worst_b2 = max(worst_b2, abs(Lv - U(G, xi, w)))
    print(f'    slice xi={mp.nstr(xi, 3)}, w={mp.nstr(w, 3)}: pencil quadrature {mp.nstr(Lv, 16)},  U_xi(w) = {mp.nstr(U(G, xi, w), 16)}')
print(f'(b) the two forms of U_xi agree to {mp.nstr(worst_b, 3)};  Radon slice = U_xi to {mp.nstr(worst_b2, 3)}')

# (c) Lemma 3(b) for real a != 0
worst_c = mp.mpf(0)
for (a, xi) in [(mp.mpf('0.7'), mp.mpf('0.4')), (mp.mpf('-1.3'), mp.mpf('1.5')), (mp.mpf('2.1'), mp.mpf('-0.8'))]:
    lam, lam0 = spec_xi(G, xi)
    kinks = sorted(set(lam + lam0))
    num = mp.quad(lambda w: mp.exp(a*w)*U(G, xi, w), kinks)            # U_xi vanishes outside [min, max]
    closed = (sum((mp.exp(a*l) for l in lam), mp.mpf(0)) - sum((mp.exp(a*l) for l in lam0), mp.mpf(0)))/a**2
    dval = mp.re(D(G, a, a*xi))/a**2
    worst_c = max(worst_c, abs(num - dval), abs(closed - dval))
    print(f'    a={mp.nstr(a, 3)}, xi={mp.nstr(xi, 3)}: int e^(aw) U = {mp.nstr(num, 16)}, closed = {mp.nstr(closed, 16)}, D(a,a xi)/a^2 = {mp.nstr(dval, 16)}')
print(f'(c) Lemma 3(b): max diff {mp.nstr(worst_c, 3)}')

# (d) full chain for real (a, t), inner integral by pencil quadrature
def slice_quad(xi, w):
    J = Inst(np.eye(4), 2); J.H = G.H - xi*G.P - w*mp.eye(4)
    return J.L(0)
worst_d = mp.mpf(0)
for (a, t) in [(mp.mpf('0.9'), mp.mpf('0.5')), (mp.mpf('-0.6'), mp.mpf('1.4'))]:
    xi = t/a
    lam, lam0 = spec_xi(G, xi)
    kinks = sorted(set(lam + lam0))
    nodes, weights = [], []
    xs, ws = np.polynomial.legendre.leggauss(8)
    for lo, hi in zip(kinks[:-1], kinks[1:]):
        for x, wt in zip(xs, ws):
            nodes.append((lo + hi)/2 + (hi - lo)/2*mp.mpf(x)); weights.append((hi - lo)/2*mp.mpf(wt))
    tot = sum((wt*mp.exp(a*w)*slice_quad(xi, w) for w, wt in zip(nodes, weights)), mp.mpf(0))
    dval = mp.re(D(G, a, t))/a**2
    worst_d = max(worst_d, abs(tot - dval))
    print(f'    a={mp.nstr(a, 3)}, t={mp.nstr(t, 3)}: chain (slices by quadrature, {len(nodes)} w-nodes) = {mp.nstr(tot, 14)},  D(a,t)/a^2 = {mp.nstr(dval, 14)}')
print(f'(d) chain RI -> Laplace identity on real (a,t): max diff {mp.nstr(worst_d, 3)}')

# (e) complex (a, t), direct 2D integral in float (scipy), as an end-to-end sanity check of the continuation step
from scipy.integrate import quad
gf = G.Hf; Pf = G.Pf; Bf = G.Bf
def Ff(s, tau):
    ev = np.linalg.eigvals((Pf/(1 - tau) - Bf/tau) @ (gf - s*np.eye(4)))
    return np.sum(np.abs(ev.imag))/(2*np.pi)
lmin, lmax = float(min(G.lam)), float(max(G.lam))
a, t = 0.8 + 0.6j, 0.3 - 1.1j
def inner(tau, part):
    sp = np.linspace(lmin, lmax, 41)
    f = lambda s: (np.exp(a*s - t*tau)*Ff(s, tau)).real if part == 0 else (np.exp(a*s - t*tau)*Ff(s, tau)).imag
    return quad(f, lmin, lmax, points=sp[1:-1], limit=400, epsabs=1e-11)[0]
def outer(part):
    return quad(lambda th: inner(np.sin(th)**2, part)*np.sin(2*th), 0, np.pi/2, limit=200, epsabs=1e-9)[0]
val = outer(0) + 1j*outer(1)
dval = complex(D(G, mp.mpc(a), mp.mpc(t))/mp.mpc(a)**2)
print(f'(e) complex (a,t) = ({a}, {t}): 2D integral = {val:.10f},  D(a,t)/a^2 = {dval:.10f},  |diff| = {abs(val - dval):.2e}')
ok = worst_a < 1e-15 and worst_b < 1e-15 and worst_b2 < 1e-15 and worst_c < 1e-15 and worst_d < 1e-6 and abs(val - dval) < 1e-5
print('ALL OK' if ok else 'CHECK')
