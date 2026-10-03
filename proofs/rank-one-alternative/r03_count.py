# Zero count of f(nu) = phi'(nu) + (i/pi) sum_j c_j/(nu - i gam_j) - mu + i alpha nu  in the strip 0<x<1.
# Claim: #zeros (with multiplicity) <= J + 1, J = #poles (gam_j > 0).
import numpy as np
rng = np.random.default_rng(3)
PI = np.pi
def f(nu, c, gam, mu, al):
    return -np.log(1 - np.exp(-1j*PI*nu))/PI + (1j/PI)*np.sum(c[:,None]/(nu[None,:]-1j*gam[:,None]),axis=0) - mu + 1j*al*nu
def winding(c, gam, mu, al, R=60.0, d=1e-7, n=400000):
    # rectangle [d,1-d] x [-R,R], counterclockwise
    t = np.linspace(0,1,n)
    ys = np.concatenate([np.linspace(-R,R,n)])
    # dense near poles and near 0 on the left side
    extra = np.concatenate([g + np.geomspace(1e-9, 5, 3000)*s for g in list(gam)+[0.0] for s in (1,-1)])
    yl = np.sort(np.concatenate([ys, extra[(extra>-R)&(extra<R)]]))
    bottom = (d + (1-2*d)*t) - 1j*R
    right = (1-d) + 1j*yl
    top = ((1-d) - (1-2*d)*t) + 1j*R
    left = d + 1j*yl[::-1]
    path = np.concatenate([bottom, right, top, left, bottom[:1]])
    v = f(path, c, gam, mu, al)
    ang = np.unwrap(np.angle(v))
    return (ang[-1]-ang[0])/(2*PI)
worst = -99
for trial in range(300):
    J = rng.integers(1, 6)
    gam = np.sort(np.abs(rng.normal(size=J))*10**rng.uniform(-1, 1.3, size=J))
    c = 10**rng.uniform(-2, 2, size=J)
    mu = rng.normal()*10**rng.uniform(-2, 1.5)
    al = 0.0 if rng.random()<0.5 else 10**rng.uniform(-2, 1)
    w = winding(c, gam, mu, al)
    ex = w - (J+1)
    worst = max(worst, ex)
    if ex > 0.01: print('VIOLATION', J, gam, c, mu, al, w)
print('max (count - (J+1)) =', worst)
