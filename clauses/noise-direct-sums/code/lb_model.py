"""lb_model.py -- explicit local models for S = DKZ_{k_1} (+) ... (+) DKZ_{k_r} (+) L_m (L_m = identity bases on an
m-dim block, i.e. m one-dimensional blocks), assembled and compared with v P + (1-v) u.

Parts (adapted variables of core.py inside DKZ blocks; equality links inside L):
  F_i  (weight q_i): all four outcomes in DKZ block i, link law phi_i = [(v k_i/d) G + (1-v) k_i/d^2 - Z_i d_0]/q_i,
       Z_i = (v k_i/d)(kappa_i - 1) - (1-v) k_i^2/d^2 (CGLMP mean), decomposed on compositions by LP;
  T_ij (weight t_ij, j a DKZ block or L): three outcomes in DKZ block i with the two within-block adapted variables 0,
       the odd one (A0, A1, B0, B1; 1/4 each) uniform in block j;
  T_Li (weight t_Li): three outcomes in L all equal, odd one uniform in DKZ block i;
  F_L : 'all four equal' (weight alpha = m(v/d + (1-v)/d^2) - Z_L) and 'a0 = a1 = p, b0 = b1 = q != p'
       (weight beta = (1-v) m (m-1)/d^2).
Orientation:
  mode A (v = v0 = (2d - K)/(d S/K + m)): t_ij = (w_ij/2)(1 + (kappa_i - kappa_j)/mu), mu = (S - K)/(K + 2m),
         t_iL = w_iL, t_Li = 0;
  mode B (any v, default v* = 1/kappa_d): t_ij = w_ij/2, t_iL = 2 Z_i - 2(1-v) k_i (K - k_i)/d^2, t_Li = w_iL - t_iL.
  (w_ij = 4 (1-v) k_i k_j / d^2.)
usage: python lb_model.py"""
import sys, os
import numpy as np
from scipy.linalg import block_diag
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import dkz_bases, behaviour          # noqa: E402
from ds_template import ime, G                 # noqa: E402
from ds_model import comp_law, add             # noqa: E402

kap = lambda n: ime(n) / 2


def target(blocks, m, v):
    As, Fs = [], []
    for k in blocks:
        A, F = dkz_bases(k); As.append(A); Fs.append(F)
    A = np.array([block_diag(*([a[x] for a in As] + [np.eye(m)])) for x in range(2)])
    F = np.array([block_diag(*([f[y] for f in Fs] + [np.eye(m)])) for y in range(2)])
    d = sum(blocks) + m
    return v * behaviour(A, F) + (1 - v) / d ** 2


def tpatterns(Pm, off, n, ooff, on, tau, equal=False):
    """three variables in the block (off, n) with the two links not containing the odd variable at adapted value 0
    (equal=True: all three equal, for L), odd variable uniform in block (ooff, on); total weight tau."""
    for odd in range(4):
        for p in range(n):
            if equal:
                a0 = a1 = b0 = b1 = p
            elif odd == 3: a0, b0, a1 = p, p, (p - 1) % n
            elif odd == 2: a0, b1, a1 = p, p, p
            elif odd == 1: a0, b0, b1 = p, p, p
            else:          b0, a1 = p, (p - 1) % n; b1 = a1
            for o in range(on):
                lam = [None] * 4
                for idx, val in ((0, 'a0'), (1, 'a1'), (2, 'b0'), (3, 'b1')):
                    lam[idx] = ooff + o if idx == odd else off + locals()[val]
                add(Pm, tuple(lam), tau / 4 / n / on)


def model(blocks, m, mode='A', v=None):
    r = len(blocks); K = sum(blocks); d = K + m
    ks = np.array(blocks, float); kp = np.array([kap(k) for k in blocks]); S = float(ks @ kp)
    v0 = (2 * d - K) / (d * S / K + m)
    if v is None:
        v = v0 if mode == 'A' else 1 / kap(d)
    w = lambda a, b: 4 * (1 - v) * a * b / d ** 2
    Z = (v * ks / d) * (kp - 1) - (1 - v) * ks ** 2 / d ** 2
    t = np.zeros((r, r)); tL = np.zeros(r); tLi = np.zeros(r)
    if mode == 'A':
        mu = (S - K) / (K + 2 * m)
        for i in range(r):
            for j in range(r):
                if i != j: t[i, j] = w(ks[i], ks[j]) / 2 * (1 + (kp[i] - kp[j]) / mu)
            tL[i] = w(ks[i], m)
    else:
        for i in range(r):
            for j in range(r):
                if i != j: t[i, j] = w(ks[i], ks[j]) / 2
            tL[i] = 2 * Z[i] - 2 * (1 - v) * ks[i] * (K - ks[i]) / d ** 2
            tLi[i] = w(ks[i], m) - tL[i]
    ZL = tLi.sum() / 2
    alpha = m * (v / d + (1 - v) / d ** 2) - ZL; beta = (1 - v) * m * (m - 1) / d ** 2
    zcheck = np.abs(0.5 * (t.sum(axis=1) + tL) - Z).max()
    offs = np.concatenate([[0], np.cumsum(blocks)]).astype(int); offL = K
    Pm = np.zeros((2, 2, d, d)); total = 0.0
    for i, (off, n) in enumerate(zip(offs[:-1], blocks)):
        q = v * n / d * G(n) + (1 - v) * n / d ** 2; q[0] -= Z[i]
        qi = q.sum(); phi = q / qi
        comps, wt = comp_law(phi)
        for c, x in zip(comps, wt):
            if x <= 0: continue
            n1, n2, n3, n4 = c
            for a0 in range(n):
                b0 = (a0 - n1) % n; b1 = (a0 + n2) % n; a1 = (b0 - 1 - n3) % n
                add(Pm, (off + a0, off + a1, off + b0, off + b1), qi * x / n)
        total += qi
        for j, (ooff, on) in enumerate(zip(offs[:-1], blocks)):
            if j != i:
                tpatterns(Pm, off, n, ooff, on, t[i, j]); total += t[i, j]
        tpatterns(Pm, off, n, offL, m, tL[i]); total += tL[i]
        if tLi[i]:
            tpatterns(Pm, offL, m, off, n, tLi[i], equal=True); total += tLi[i]
    for p in range(m):
        add(Pm, (offL + p,) * 4, alpha / m)
        for q_ in range(m):
            if q_ != p:
                add(Pm, (offL + p, offL + p, offL + q_, offL + q_), beta / (m * (m - 1)))
    total += alpha + beta
    err = np.abs(Pm - target(blocks, m, v)).max()
    mins = dict(t=t[~np.eye(r, dtype=bool)].min() if r > 1 else 0.0, tL=tL.min(), tLi=tLi.min(), Z=Z.min(),
                alpha=alpha, beta=beta)
    return v, v0, total, err, zcheck, mins


if __name__ == '__main__':
    cases_A = [((3,), 1), ((5,), 3), ((2, 2), 1), ((3, 2), 1), ((3, 2), 2), ((4, 2), 1), ((2, 2, 2), 1), ((3, 3), 1),
               ((4, 3, 2), 2), ((5, 2), 4), ((6, 3), 9), ((2, 3, 4, 5), 6)]
    cases_B = [((3, 2), 15), ((4, 2), 20), ((2, 3, 4), 25), ((6,), 30), ((2, 2), 9), ((5, 2), 18)]
    for mode, cases in (('A', cases_A), ('B', cases_B)):
        for blocks, m in cases:
            v, v0, tot, err, zc, mins = model(blocks, m, mode)
            d = sum(blocks) + m
            ok = min(mins.values()) >= -1e-15 and err < 1e-12 and abs(tot - 1) < 1e-12 and zc < 1e-14
            print(f"mode {mode} blocks {blocks} + L_{m} (d={d}): v={v:.10f} (v0={v0:.10f}, v*={1/kap(d):.10f}) "
                  f"total={tot:.14f} max|model-P_v|={err:.1e} Zid={zc:.1e} "
                  f"min weights {', '.join(f'{k}={x:.2e}' for k, x in mins.items())}  {'OK' if ok else 'FAIL'}",
                  flush=True)
