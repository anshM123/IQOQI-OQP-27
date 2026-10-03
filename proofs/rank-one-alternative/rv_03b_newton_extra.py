"""Referee: check that the extra Newton 'zeros' reported in rv_03 logs (y < 0, tiny x) are zeros of the holomorphic
extension ON the line x = 0 (i.e. zeros of r_-), not zeros in S: re-solve at 50 digits and test Re -> 0."""
import re, glob, mpmath as mp, numpy as np
mp.mp.dps = 50
def fmp(nu, c, g, mu, a, eps):
    return (-mp.log(1 - mp.exp(-1j*mp.pi*nu))/mp.pi + (1j/mp.pi)*mp.fsum([cj/(nu - 1j*gj) for cj, gj in zip(c, g)])
            - mu + 1j*a*nu + eps*mp.pi*mp.cos(mp.pi*nu))
def rminus(y, c, g, mu, a, eps):
    return mp.re(fmp(mp.mpc(0, y), c, g, mu, a, eps))
for fn in sorted(glob.glob('rv_03_lemma6_*.log')):
    for line in open(fn):
        if 'NEWTON found' not in line: continue
        nums = lambda s: [float(v) for v in re.findall(r'np\.float64\(([^)]+)\)', s)]
        parts = line.split('] [')
        head = line[:line.index('[np.float64')]
        J = int(head.split()[-1])
        allf = nums(line)
        g = allf[:J]; c = allf[J:2*J]
        rest = line[line.index(']', line.index(']', line.index('[np.float64') ) + 1) + 1:]
        mu, a, eps = [float(v) for v in rest.split('[')[0].split()[:3]]
        zs = [complex(z.replace('np.complex128(', '').replace(')', '').replace('(', '')) for z in re.findall(r'(?:np\.complex128\()?\(?([-0-9.e+]+[-+][0-9.e+-]+j)\)?', rest)]
        for z in zs:
            if z.imag < 0 and z.real < 1e-5:
                try:
                    zz = mp.findroot(lambda w: fmp(w, c, g, mu, a, eps), mp.mpc(z.real, z.imag))
                except Exception as e:
                    zz = None
                y0 = z.imag
                sc = rminus(y0 - 1e-5, c, g, mu, a, eps)*rminus(y0 + 1e-5, c, g, mu, a, eps)
                print(fn, 'J', J, 'newton zero', z, '-> 50-digit root', mp.nstr(zz, 12) if zz is not None else None,
                      '| r_- sign change within 1e-5:', bool(sc < 0))
