"""Referee check: standing facts F2-F5, Lemma 1 (a),(b),(c) incl. sign conventions and s < 1, Lemma 2."""
import numpy as np, mpmath as mp
from scipy.optimize import brentq
from rv_core import *

rng = np.random.default_rng(101)
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

# ---------------- F1/F2/F3/F4 against the definition (mpmath, 30 digits)
mp.mp.dps = 30
e_def = e_F2 = e_F4 = 0.0
for _ in range(300):
    x = rng.uniform(0.001, 0.999); y = rng.normal()*rng.choice([0.3, 3, 10])
    hm = h_mp(mp.mpc(x, y)); hm2 = h_mp(mp.mpc(x, -y))
    e_def = max(e_def, abs(float(hm) - float(h(x + 1j*y))))
    e_F2 = max(e_F2, abs(float(hm - hm2 - (1 - x)*y)))
    # F4: h_x - i h_y = phi'
    hx = mp.diff(lambda t: h_mp(mp.mpc(t, y)), x); hy = mp.diff(lambda t: h_mp(mp.mpc(x, t)), y)
    e_F4 = max(e_F4, abs(complex(hx - 1j*hy - phip_mp(mp.mpc(x, y)))), abs(complex(phip(np.array([x+1j*y]))[0]) - complex(phip_mp(mp.mpc(x, y)))))
say('F-checks: |h(numpy)-h(mp def)| <=', e_def, ' F2 err', e_F2, ' F4 (h_x - i h_y = phi\') err', e_F4)
# boundary values of phi' (F3)
for y in [-2.0, -0.3, 0.4, 2.5]:
    a = complex(phip_mp(mp.mpc(1e-25, y)))
    b = (-np.log(np.exp(PI*y) - 1)/PI - 1j) if y > 0 else -np.log(1 - np.exp(PI*y))/PI
    c = complex(phip_mp(mp.mpc(1, y))); d = -np.log(1 + np.exp(PI*y))/PI
    say(f'  F3 boundary y={y}: phi\'(0+iy)={a:.12f} formula {b:.12f} | phi\'(1+iy)={c:.12f} formula {d:.12f}')

# ---------------- F5 Legendre: inf_y h(x+iy) - p y = Phi_c(x,p)
mp.mp.dps = 40
worst5 = mp.mpf(0); worst5b = mp.mpf(1)
for _ in range(60):
    x = mp.mpf(rng.uniform(0.01, 0.99)); p = mp.mpf(rng.uniform(0.001, 0.999))*(1 - x)
    # stationary point: h_y = p  <=>  arg(1 - e^{pi y} e^{-i pi x}) = pi p
    fy = lambda yy: mp.arg(1 - mp.exp(mp.pi*yy)*mp.exp(-1j*mp.pi*x))/mp.pi - p
    ys = mp.findroot(fy, (mp.mpf(-60), mp.mpf(60)), solver='bisect')
    val = h_mp(mp.mpc(x, ys)) - p*ys
    Phic = L_mp(x) + L_mp(p) + L_mp(1 - x - p)
    worst5 = max(worst5, abs(val - Phic))
    for yy in np.linspace(-8, 8, 9):
        worst5b = min(worst5b, h_mp(mp.mpc(x, yy)) - p*yy - Phic)
say('F5: |min_y (h - p y) - Phi_c| <=', mp.nstr(worst5, 5), '; min over grid of h - p y - Phi_c =', mp.nstr(worst5b, 5), '(>= 0 required)')

# ---------------- Lemma 1 (a), (b) incl. R(t) = exp(-2 pi i F(t)) and s < 1
ea = eb = eR = eR2 = 0.0; nb = 0
for trial in range(400):
    M = int(rng.integers(2, 9)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1.0))
    sc = 10**rng.uniform(-1, 2.5)
    g = rand_herm(M, rng, sc)
    if trial % 4 == 1:   # clustered spectrum / one huge eigenvalue
        w, U = np.linalg.eigh(g); w = np.round(w/sc*2)*sc/2 + 1e-3*rng.normal(size=M); w[-1] *= 30; g = (U*w) @ U.conj().T
    v = rand_unit(M, rng)
    X = s*np.outer(v, v.conj()) + 1j*g
    nu = np.linalg.eigvals(X); x, y = nu.real, nu.imag
    ea = max(ea, max(0, -x.min()), max(0, x.max() - s), abs(x.sum() - s))
    if x.min() <= 1e-10:
        continue
    gam = quantiles(x, y)
    spec = compress_spec(g, v)
    eb = max(eb, np.max(np.abs(gam - spec))/max(1.0, np.abs(y).max())); nb += 1
    # R(t) checks (sign conventions)
    A = g - 1j*s*np.outer(v, v.conj())
    for t in rng.normal(size=3)*sc:
        Rt = np.linalg.det(A - t*np.eye(M))/np.linalg.det(A.conj().T - t*np.eye(M))
        Ft = Fdist(t, x, y)
        eR = max(eR, abs(Rt - np.exp(-2j*PI*Ft)))
        G = v.conj() @ np.linalg.solve(g - t*np.eye(M), v)
        eR2 = max(eR2, abs(Rt - (1 - 1j*s*G)/(1 + 1j*s*G)))
say(f'Lemma 1(a): max violation of 0<=x<=s, sum x = s: {ea:.2e}')
say(f'Lemma 1(b): {nb} cases, max |gamma - spec(PgP)|/scale = {eb:.2e};  |R(t) - exp(-2pi i F(t))| <= {eR:.2e};  |R - (1-isG)/(1+isG)| <= {eR2:.2e}')

# ---------------- Lemma 1 (c): converse construction
ec = ep = 0.0; minp = 1e9
for trial in range(300):
    M = int(rng.integers(1, 8)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1.0))
    wts = rng.exponential(size=M)**3 + 1e-6; x = s*wts/wts.sum()
    y = rng.normal(size=M)*10**rng.uniform(-1, 2)
    if trial % 5 == 0: y = np.round(y) + 1e-6*rng.normal(size=M)      # clustered
    # poles: F = k - 1/2
    lo = y.min() - 1e6; hi = y.max() + 1e6
    Fd = lambda t: Fdist(t, x, y)
    sp = np.array([brentq(lambda t: Fd(t) - (k - 0.5), lo, hi, xtol=1e-14, rtol=1e-15, maxiter=500) for k in range(1, M + 1)])
    Fp = np.array([np.sum(x/(PI*(x**2 + (t - y)**2))) for t in sp])
    p = 1/(PI*s*Fp)              # residues of G = (1-R)/(is(1+R)) at its poles
    minp = min(minp, p.min()); ep = max(ep, abs(p.sum() - 1))
    gg = np.diag(sp); vv = np.sqrt(p/p.sum())
    nu2 = np.linalg.eigvals(s*np.outer(vv, vv) + 1j*gg)
    nu = x + 1j*y
    # match multisets
    from scipy.optimize import linear_sum_assignment
    C = np.abs(nu[:, None] - nu2[None, :]); r, c = linear_sum_assignment(C)
    ec = max(ec, C[r, c].max()/max(1, np.abs(y).max()))
say(f'Lemma 1(c): residues p_i min {minp:.2e} (>0), |sum p_i - 1| <= {ep:.2e}, |spec(s vv*+ig) - nu|/scale <= {ec:.2e}')

# ---------------- Lemma 2: trace identity on general configurations (incl. atoms x = 0, s < 1)
e2 = 0.0
for trial in range(400):
    M = int(rng.integers(1, 9)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1.0))
    wts = rng.exponential(size=M)**2
    nz = rng.random(M) < 0.3
    if nz.all(): nz[0] = False
    wts[nz] = 0; x = s*wts/wts.sum()
    y = rng.normal(size=M)*10**rng.uniform(-1, 2.3)
    if trial % 4 == 0: y[:] = np.round(y/5)*5    # coincident atoms / points
    gam = quantiles(x, y)
    lhs = np.sum((1 - x)*y) - gam.sum(); rhs = (1 - s)/s*np.sum(x*y)
    e2 = max(e2, abs(lhs - rhs)/max(1, np.abs(y).max()))
say(f'Lemma 2: max |sum(1-x)y - sum gamma - alpha S|/scale = {e2:.2e}  (400 configs, 30% atoms, coincident y)')
open('rv_01_lemma12.log', 'w').write('\n'.join(out) + '\n')
