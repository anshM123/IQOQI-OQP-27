"""Referee check of Lemma 6: zeros of
   f(nu) = phi'(nu) + (i/pi) sum_j c_j/(nu - i g_j) - mu + i a nu + eps pi cos(pi nu)   in S = {0 < x < 1}
are <= J + 1.  Count (A) by an adaptive winding number on [delta,1] x [-R,R] with delta = 1e-100, the left side
evaluated in exact local coordinates (u = y - g_j near poles, log form of phi' near 0), and (B) by Newton: global
grid (x > 1e-12) + local Newton in w = nu - i g_j near each pole (zeros there can have x ~ 1e-60).
Also test the bookkeeping formula  #zeros = J + 1 - Z/2,  Z = #zeros of r_-(y) = f(iy) on (-R, 0)."""
import numpy as np, sys, time
from rv_core import phip, PI

DELTA = 1e-100

class Fun:
    def __init__(s, c, g, mu, a, eps):
        s.c = np.asarray(c, float); s.g = np.asarray(g, float); s.mu = mu; s.a = a; s.eps = eps
    def phip_small(s, nu):
        # phi'(nu) for |nu| small: -(1/pi)[log(pi) + log(nu) + i pi/2] - (1/pi) log((1-e^{-i pi nu})/(i pi nu))
        corr = -np.log1p(-1j*PI*nu/2 - (PI*nu)**2/6)/PI
        return -(np.log(PI) + np.log(nu) + 1j*PI/2)/PI + corr
    def reg(s, nu, skip=None):
        """f minus the pole term 'skip' (all other terms)."""
        nu = np.asarray(nu, complex)
        small = np.abs(nu) < 1e-6
        ph = np.where(small, s.phip_small(np.where(small, nu, 1.0)), phip(np.where(small, 0.5, nu)))
        tot = ph - s.mu + 1j*s.a*nu + s.eps*PI*np.cos(PI*nu)
        for j in range(len(s.g)):
            if j != skip:
                tot = tot + (1j/PI)*s.c[j]/(nu - 1j*s.g[j])
        return tot
    def __call__(s, nu):
        return s.reg(nu)
    def near_pole(s, j, w):
        """f(i g_j + w) evaluated with w exact."""
        return (1j/PI)*s.c[j]/w + s.reg(1j*s.g[j] + w, skip=j)
    def deriv(s, nu):
        nu = np.asarray(nu, complex)
        e = np.exp(1j*PI*np.clip(nu.imag, -600, 600)*1j/1j)  # placeholder (not used)
        y = nu.imag
        ph2 = np.where(y > -300, -1j/(np.exp(1j*PI*np.where(y > -300, nu, 0)) - 1), 0j)
        pol = -(1j/PI)*np.sum(s.c[:, None]/(nu.ravel()[None, :] - 1j*s.g[:, None])**2, axis=0).reshape(nu.shape)
        return ph2 + pol + 1j*s.a - s.eps*PI**2*np.sin(PI*nu)

def track(F, t0, t1, n0=400, maxpts=2_000_000, relaxed=False):
    """total change of arg of F(t) for t in [t0,t1], adaptive refinement.
    relaxed=True (only used on the upper-left side, where Im f >= -1 - o(1) and the only positive contributions to
    Im f are the pole terms, monotone in |u| on each side of a pole): a step whose two values both have Im <= -0.3
    cannot wind around 0, so it is accepted without refinement."""
    t = np.linspace(t0, t1, n0)
    for it in range(80):
        v = F(t)
        if np.any(~np.isfinite(v)) or np.any(v == 0):
            return np.nan
        d = np.angle(v[1:]/v[:-1])
        rat = np.abs(np.log(np.abs(v[1:]/v[:-1])))
        bad = (np.abs(d) > 0.25) | (rat > 0.7)
        if relaxed:
            bad &= ~((v[1:].imag <= -0.3) & (v[:-1].imag <= -0.3))
        if not np.any(bad):
            return float(np.sum(d))
        if len(t) > maxpts:
            return np.nan
        t = np.sort(np.concatenate([t, 0.5*(t[1:][bad] + t[:-1][bad])]))
        if t0 > t1: t = t[::-1]
    return np.nan

def winding(f, R, delta=DELTA, verbose=False):
    """contour: bottom (dl,-R)->(1,-R); right; top (1,R)->(delta,R); left x = delta from R down to rho_c with pole
    passages in exact local coordinates; horizontal (delta,rho_c)->(dl,rho_c); left x = dl from rho_c down to -R.
    The excluded sliver {x < dl, y < rho_c} can only contain zeros on the axis (corner zero, zeros of r_-) or
    non-generic mirror pairs."""
    g = f.g; J = len(g)
    rho_c = min(1e-6, 0.25*g[0]); dl = min(1e-8, rho_c/10)
    parts = {}
    parts['bottom'] = track(lambda t: f(t - 1j*R), dl, 1.0)
    parts['right'] = track(lambda t: f(1 + 1j*t), -R, R)
    parts['top'] = track(lambda t: f(t + 1j*R), 1.0, delta)
    gaps = np.diff(np.concatenate([[0.0], g]))
    rho = [0.25*min(gaps[j], gaps[j+1] if j + 1 < J else 1.0, 1.0) for j in range(J)]
    K = 140.0
    def pole_pass(j):
        def Fp(t):  # u = y - g_j from +rho_j down to -rho_j, log-spaced to |u| ~ 1e-140
            u = -np.sign(t)*rho[j]*10.0**(K*(np.abs(t) - 1))
            u = np.where(t == 0, 0.0, u)
            return f.near_pole(j, delta + 1j*u)
        return track(Fp, -1.0, 1.0, n0=4000, relaxed=True)
    left = 0.0
    top_y = R
    for j in range(J - 1, -1, -1):
        left += track(lambda t: f(delta + 1j*t), top_y, g[j] + rho[j], relaxed=True)
        left += pole_pass(j)
        top_y = g[j] - rho[j]
    left += track(lambda t: f(delta + 1j*t), top_y, rho_c, relaxed=True)
    parts['left_up'] = left
    parts['horiz'] = track(lambda t: f(10.0**t + 1j*rho_c), np.log10(delta), np.log10(dl))
    parts['left_low'] = track(lambda t: f(dl + 1j*t), rho_c, -R)
    tot = sum(parts.values())
    if verbose:
        print({k: round(v/PI, 4) for k, v in parts.items()})
    return tot/(2*PI), parts

def Zcount(f, R):
    ys = -np.geomspace(1e-12, R, 400000)
    r = np.real(f.reg(1j*ys))   # on the negative imaginary axis f is real
    Z = int(np.sum(np.sign(r[1:]) != np.sign(r[:-1])))
    if r[0] < 0: Z += 1          # r_- -> +inf as y -> 0-, monotone (log) in (-1e-12, 0)
    if r[-1] < 0: Z += 1
    return Z

def newton_zeros(f, R):
    g = f.g
    xs = np.concatenate([[1e-9, 1e-7, 1e-5, 1e-3], np.linspace(0.01, 0.99, 25), [1 - 1e-3, 1 - 1e-6]])
    ys = np.concatenate([np.linspace(-R, R, 161), -np.geomspace(1e-8, R, 60), np.geomspace(1e-8, R, 60)]
                        + [gj + np.concatenate([-np.geomspace(1e-9, 1, 25), np.geomspace(1e-9, 1, 25)]) for gj in g])
    z = (xs[:, None] + 1j*ys[None, :]).ravel()
    for it in range(100):
        dz = f(z)/f.deriv(z)
        dz = np.where(np.isfinite(dz), dz, 0)
        lim = 0.25*np.maximum(np.minimum(z.real, 1 - z.real), 1e-14) + 0.05
        z = z - np.minimum(1.0, lim/np.maximum(np.abs(dz), 1e-300))*dz
        z = np.where(z.real <= 0, 1e-15 + 1j*z.imag, z)
        z = np.where(z.real >= 1.2, 1.2 + 1j*z.imag, z)
    fz = f(z)
    ok = np.isfinite(fz) & (np.abs(fz) < 1e-8*(1 + np.abs(f.deriv(z))*1e-8)) & (np.abs(z.imag) < R) & (z.real < 1)
    ok &= np.where(z.imag < 0, z.real > 1e-9, z.real > 1e-12)
    zs = []
    for w in z[ok]:
        if all(abs(w - u) > 1e-7*(1 + abs(u)) for u in zs):
            zs.append(w)
    # local Newton near each pole, in w = nu - i g_j
    for j in range(len(g)):
        q = f.reg(1j*g[j] + 1e-300, skip=j)
        w = -(1j/PI)*f.c[j]/q
        for it in range(200):
            val = f.near_pole(j, w)
            h_ = max(abs(w)*1e-7, 1e-320)
            der = (f.near_pole(j, w + h_) - f.near_pole(j, w - h_))/(2*h_)
            dw = val/der
            if not np.isfinite(dw): break
            w = w - dw
            if w.real <= 0: w = abs(w.real)*0.5 + 1j*w.imag + 1e-300
            if abs(dw) < 1e-14*abs(w): break
        if np.isfinite(w) and w.real > 0 and abs(f.near_pole(j, w)) < 1e-6*(1 + abs(q)) and abs(w) < 0.5*min(np.diff(np.concatenate([[0], g, [1e9]]))):
            nu = 1j*g[j] + w
            if nu.real > 1e-12 and any(abs(nu - u) < 1e-7*(1 + abs(u)) for u in zs):
                continue
            zs.append(complex(w.real, g[j] + w.imag) if nu.real <= 1e-12 else nu)
    return zs

def pick_R(c, g, mu, a, eps):
    big = 10 + abs(mu) + np.sum(c) + a
    return float(max(np.log(40*big*(1 + big)/eps)/PI + 2.0, g.max() + 3.0))

def gen(rng, regime):
    J = int(rng.integers(1, 9))
    g = np.sort(np.abs(rng.normal(size=J))*10**rng.uniform(-1, 1.0, size=J))
    c = 10**rng.uniform(-2, 2, size=J)
    mu = rng.normal()*10**rng.uniform(-2, 1.5)
    a = 0.0 if rng.random() < 0.4 else 10**rng.uniform(-2, 1.5)
    eps = 10**rng.uniform(-8, 0)
    if regime == 'pole0':   g[0] = 10**rng.uniform(-6, -2); g = np.sort(g)
    if regime == 'bigc':    c = 10**rng.uniform(2, 5, size=J)
    if regime == 'tinyc':   c = 10**rng.uniform(-7, -3, size=J)
    if regime == 'mixc':    c = 10**rng.uniform(-6, 5, size=J)
    if regime == 'bigmu':   mu = rng.choice([-1, 1])*10**rng.uniform(1.5, 4)
    if regime == 'biga':    a = 10**rng.uniform(1, 3)
    if regime == 'tinyeps': eps = 10**rng.uniform(-14, -9)
    if regime == 'cluster': g = g[0] + 1e-3*np.sort(np.abs(rng.normal(size=J))) + 1e-6*np.arange(J)
    if regime == 'negmu':   mu = -10**rng.uniform(0, 3); a = 10**rng.uniform(-1, 2)
    if regime == 'posmu':   mu = 10**rng.uniform(0, 3); a = 0.0 if rng.random() < 0.5 else 10**rng.uniform(-2, 1)
    if regime == 'farpole': g = np.sort(np.abs(rng.normal(size=J))*10**rng.uniform(0.5, 1.2, size=J))
    return J, np.sort(g), c, mu, a, eps

def run(nsamp, seed, regime):
    rng = np.random.default_rng(seed)
    st = dict(n=0, viol=0, fail=0, formula_bad=0, newton_more=0, newton_less=0, maxexcess=-99, hist={})
    for k in range(nsamp):
        J, g, c, mu, a, eps = gen(rng, regime)
        if len(np.unique(g)) < J: continue
        f = Fun(c, g, mu, a, eps)
        R = pick_R(c, g, mu, a, eps)
        w, parts = winding(f, R)
        st['n'] += 1
        if not np.isfinite(w) or abs(w - round(w)) > 1e-3:
            st['fail'] += 1; print('  fail', regime, J, w, flush=True); continue
        cnt = int(round(w))
        st['maxexcess'] = max(st['maxexcess'], cnt - (J + 1))
        st['hist'][cnt - (J + 1)] = st['hist'].get(cnt - (J + 1), 0) + 1
        if cnt > J + 1:
            st['viol'] += 1
            print('VIOLATION', regime, J, list(g), list(c), mu, a, eps, cnt, flush=True)
        Z = Zcount(f, R)
        if Z % 2 or cnt != J + 1 - Z//2:
            st['formula_bad'] += 1
            print(f'  formula mismatch: count {cnt}, Z={Z}', regime, J, list(g), list(c), mu, a, eps, flush=True)
        zs = newton_zeros(f, R)
        if len(zs) > cnt:
            st['newton_more'] += 1
            print(f'  NEWTON found {len(zs)} > winding {cnt}', regime, J, list(g), list(c), mu, a, eps, zs, flush=True)
        if len(zs) < cnt: st['newton_less'] += 1
    return st

if __name__ == '__main__':
    regimes = sys.argv[1].split(',') if len(sys.argv) > 1 else ['rand']
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
    for i, reg in enumerate(regimes):
        t0 = time.time()
        st = run(nsamp, seed0 + i, reg)
        print(f'[{reg}] {st}  ({time.time()-t0:.0f}s)', flush=True)
