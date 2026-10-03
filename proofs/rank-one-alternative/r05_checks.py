# (1) subcritical: spec(PgP) = integer quantiles of sigma = sum Cauchy(y_k, x_k), nu = spec(s vv* + i g)
# (2) subcritical trace identity: sum (1-x)y - sum gam = ((1-s)/s) sum x y
# (3) zero count with harmonic penalty  f_eps = f + eps*pi*cos(pi nu):  #zeros <= J+1
import numpy as np
from scipy.optimize import brentq
rng = np.random.default_rng(5)
PI = np.pi
e1 = e2 = 0
for t in range(200):
    M = int(rng.integers(2, 8)); s = rng.uniform(0.05, 1)
    sc = 10**rng.uniform(-1, 1.5)
    g = rng.normal(size=(M,M))+1j*rng.normal(size=(M,M)); g = (g+g.conj().T)/2*sc
    v = rng.normal(size=M)+1j*rng.normal(size=M); v /= np.linalg.norm(v)
    nu = np.linalg.eigvals(s*np.outer(v,v.conj()) + 1j*g); x, y = nu.real, nu.imag
    P = np.eye(M) - np.outer(v, v.conj()); w, V = np.linalg.eigh(P); Qb = V[:, w > .5]
    gam = np.sort(np.linalg.eigvalsh(Qb.conj().T@g@Qb))
    Fs = lambda tt: np.sum(0.5+np.arctan((tt-y)/x)/PI)
    q = np.array([brentq(lambda tt: Fs(tt)-j, -1e4*sc-1e4, 1e4*sc+1e4, xtol=1e-13) for j in range(1, M)])
    e1 = max(e1, np.max(np.abs(q-gam))/max(1, sc))
    e2 = max(e2, abs(np.sum((1-x)*y) - gam.sum() - (1-s)/s*np.sum(x*y))/max(1, sc))
print('(1) quantile err', e1, ' (2) trace identity err', e2, ' sum x - s ok')
def f(nu, c, gam, mu, al, eps):
    return (-np.log(1 - np.exp(-1j*PI*nu))/PI + (1j/PI)*np.sum(c[:,None]/(nu[None,:]-1j*gam[:,None]),axis=0)
            - mu + 1j*al*nu + eps*PI*np.cos(PI*nu))
def winding(c, gam, mu, al, eps, R=12.0, d=1e-7, n=300000):
    t = np.linspace(0,1,n)
    ys = np.linspace(-R,R,n)
    extra = np.concatenate([g0 + np.geomspace(1e-9, 5, 3000)*sg for g0 in list(gam)+[0.0] for sg in (1,-1)])
    yl = np.sort(np.concatenate([ys, extra[(extra>-R)&(extra<R)]]))
    path = np.concatenate([(d+(1-2*d)*t)-1j*R, (1-d)+1j*yl, ((1-d)-(1-2*d)*t)+1j*R, d+1j*yl[::-1], [d-1j*R]])
    ang = np.unwrap(np.angle(f(path, c, gam, mu, al, eps)))
    return (ang[-1]-ang[0])/(2*PI)
worst = -99
for trial in range(200):
    J = int(rng.integers(1, 6))
    gam = np.sort(np.abs(rng.normal(size=J))*10**rng.uniform(-1, 0.8, size=J))
    c = 10**rng.uniform(-2, 2, size=J)
    mu = rng.normal()*10**rng.uniform(-2, 1.5)
    al = 0.0 if rng.random()<0.5 else 10**rng.uniform(-2, 1)
    eps = 10**rng.uniform(-6, 0)
    R = max(8.0, (np.log(1/eps)+np.log(1+abs(mu)+sum(c)))/PI + 8)
    w = winding(c, gam, mu, al, eps, R=R)
    worst = max(worst, w-(J+1))
    if w-(J+1) > 0.01: print('VIOLATION', J, gam, c, mu, al, eps, w)
print('(3) max (count - (J+1)) with penalty =', worst)
