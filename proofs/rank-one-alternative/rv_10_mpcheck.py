"""Referee: 50-digit re-evaluation of every saved adversarial worst point with a negative double-precision value
(rv_07_worst_*.npy: (*) defect; rv_09_worst_*.npy: s<1 functional T)."""
import numpy as np, mpmath as mp, glob, re
from rv_core import unitary_from, herm_from, star_defect, star_defect_mp, to_mp, h_mp, h
mp.mp.dps = 50
rows = []
for fn in sorted(glob.glob('rv_07_worst_rank1_*.npy') + glob.glob('rv_07_worst_allM5_*.npy')):
    d = np.load(fn); r = int(d[0]); gmax = d[1]; x = d[2:]; M = int(round(np.sqrt(len(x)/2)))
    U = unitary_from(x[:M*M], M); B = U[:, :r] @ U[:, :r].conj().T; g = herm_from(gmax*np.tanh(x[M*M:]), M)
    D = star_defect(B, g)
    D50 = star_defect_mp(B, g) if D < 1e-9 else None
    rows.append((fn, D, D50))
for fn in sorted(glob.glob('rv_09_worst_*.npy')):
    m = re.match(r'rv_09_worst_M(\d+)_g(\d+)_s(\d+)_(\w+)\.npy', fn); M = int(m.group(1)); gmax = float(m.group(2))
    p = np.load(fn)
    s = 0.005 + 0.99/(1 + np.exp(-p[0])); v = p[1:M + 1] + 1j*p[M + 1:2*M + 1]; v = v/np.linalg.norm(v)
    g = herm_from(gmax*np.tanh(p[2*M + 1:]), M)
    P = np.eye(M) - np.outer(v, v.conj())
    T = (np.sum(h(np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g))) - np.sum(np.maximum(np.linalg.eigvalsh(P @ g @ P), 0))
         - (1 - s)*max(np.real(v.conj() @ g @ v), 0))
    T50 = None
    if T < 1e-9:
        vm = to_mp(v.reshape(-1, 1)); gm = to_mp(g); sm = mp.mpf(s)
        E, _ = mp.eig(sm*(vm*vm.H) + 1j*gm)
        Pm = mp.eye(M) - vm*vm.H
        w, _ = mp.eighe((Pm*gm*Pm + (Pm*gm*Pm).H)/2)
        k = mp.re((vm.H*gm*vm)[0, 0])
        T50 = mp.fsum([h_mp(e) for e in E]) - mp.fsum([max(mp.re(e), 0) for e in w]) - (1 - sm)*max(k, 0)
    rows.append((fn, T, T50))
for fn in sorted(glob.glob('rv_11_worst_*.npy')):
    m = re.match(r'rv_11_worst_M(\d+)_g(\d+)_s(\d+)_', fn); M = int(m.group(1)); gmax = float(m.group(2))
    d = np.load(fn); s = d[0]; p = d[1:]
    v = p[1:M + 1] + 1j*p[M + 1:2*M + 1]; v = v/np.linalg.norm(v)
    g = herm_from(gmax*np.tanh(p[2*M + 1:]), M)
    P = np.eye(M) - np.outer(v, v.conj())
    T = (np.sum(h(np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g))) - np.sum(np.maximum(np.linalg.eigvalsh(P @ g @ P), 0))
         - (1 - s)*max(np.real(v.conj() @ g @ v), 0))
    T50 = None
    if T < 1e-9:
        vm = to_mp(v.reshape(-1, 1)); gm = to_mp(g); sm = mp.mpf(s)
        E, _ = mp.eig(sm*(vm*vm.H) + 1j*gm)
        Pm = mp.eye(M) - vm*vm.H
        w, _ = mp.eighe((Pm*gm*Pm + (Pm*gm*Pm).H)/2)
        k = mp.re((vm.H*gm*vm)[0, 0])
        T50 = mp.fsum([h_mp(e) for e in E]) - mp.fsum([max(mp.re(e), 0) for e in w]) - (1 - sm)*max(k, 0)
    rows.append((fn, T, T50))
neg = 0
for fn, a, b in rows:
    bs = mp.nstr(b, 6) if b is not None else '-'
    if b is not None and b < 0: neg += 1
    print(f'{fn:45s} double {a: .3e}   50-digit {bs}')
print('points with NEGATIVE 50-digit value:', neg, 'of', len(rows))
