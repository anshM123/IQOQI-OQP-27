"""rc05: Theorem RI-B (s.3.5) for a general Hermitian B = sum_k b_k Pi_k, dps 40:
 (1) RI-B: (1/2pi) int_G sum |Im y_i| dtau = Tr H_+ - Tr (H_d)_+, H_d = sum_k Pi_k H Pi_k, on spectra with repeated and nearly
     coincident interior eigenvalues, degenerate Pi_k H Pi_k, partially commuting blocks, and the shifted form;
 (2) Psi_B(c) = E(c);
 (3) interior ends: the one-sided limits of Lam_+ - Lam0_+ at b_k (k interior) agree (difference -> 0 linearly);
 (4) bound (B') |S_+ - S0_+| <= M K (2/delta_l + sqrt(2/(d_- d_+))) and the C_+/C_- root bounds; kappa = 0 bound
     |S_pos - S0_+| <= (2/delta_l)||H||_F^2/(c0 - ||H||) for c0 > ||H||."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline

mp.mp.dps = 40
out = open('rc05_generalB.log', 'w')
rng = random.Random(31337)


def blockdiag_with(H, blocks, specs):
    """replace the diagonal blocks of H (index lists) by matrices with prescribed exact spectra."""
    H = sp.Matrix(H)
    for blk, sp_ in zip(blocks, specs):
        if sp_ is None:
            continue
        Hb = with_spectrum(rng, sp_)
        for a, i in enumerate(blk):
            for b, j in enumerate(blk):
                H[i, j] = Hb[a, b]
    return H


cases = []
cases.append(Inst(herm(rng, 3), [0, sp.Rational(3, 8), 1], [1, 1, 1], 'b=(0,3/8,1)'))
cases.append(Inst(herm(rng, 4), [-1, sp.Rational(1, 5), sp.Rational(1, 2), 2], [1, 1, 1, 1], 'b=(-1,1/5,1/2,2)'))
cases.append(Inst(herm(rng, 4), [0, sp.Rational(3, 5), 1], [1, 2, 1], 'b=(0,3/5^2,1)'))
cases.append(Inst(herm(rng, 5), [0, sp.Rational(3, 10), sp.Rational(31, 100), 1], [1, 2, 1, 1], 'b=(0,.3^2,.31,1)'))
cases.append(Inst(herm(rng, 6), [sp.Rational(-1, 2), sp.Rational(1, 10), sp.Rational(9, 10), 2], [1, 2, 1, 2],
                  'b=(-.5,.1^2,.9,2^2)'))
I0 = Inst(herm(rng, 5), [0, sp.Rational(1, 2), 1], [1, 3, 1], 'tmp')
Hdeg = blockdiag_with(I0.Hs, I0.blocks, [None, [1, 1, -1], None])
cases.append(Inst(Hdeg, [0, sp.Rational(1, 2), 1], [1, 3, 1], 'b=(0,1/2^3,1) Pi2HPi2 spec(1,1,-1)'))
# partially commuting: Pi_1 H Pi_3 = 0 and Pi_2 H Pi_3 = 0 (block 3 decouples) -> RI-B must reduce to the (1,2) part
Hp = herm(rng, 4)
for i in [0, 1, 2]:
    Hp[i, 3] = 0
    Hp[3, i] = 0
cases.append(Inst(Hp, [0, sp.Rational(2, 5), 1], [1, 2, 1], 'b=(0,2/5^2,1) block3 decoupled'))

# ---------------------------------------------------------------- (1) RI-B
logline(out, '(1) Theorem RI-B at c0 = 0 and shifted')
worst = mp.mpf(0)
for I in cases:
    I.mpready()
    for c0 in [0, sp.Rational(1, 3)]:
        t0 = time.time()
        Lv, err, nb, pcs = I.L(c0)
        Rv = I.R(mp.mpf(sp.Rational(c0).p)/sp.Rational(c0).q)
        d = abs(Lv - Rv)
        worst = max(worst, d)
        logline(out, '  %-36s M=%d c0=%-4s #bp=%2d pairs/piece=%s L_B=%s R=%s |L_B-R|=%s quad-err=%s (%.0fs)' % (
            I.name, I.M, str(c0), nb, pcs, mp.nstr(Lv, 24), mp.nstr(Rv, 24), mp.nstr(d, 3), mp.nstr(err, 3), time.time() - t0))
logline(out, 'max |L_B - R| = %s' % mp.nstr(worst, 3))

# ---------------------------------------------------------------- (2) Psi_B = E
logline(out, '\n(2) Psi_B(c) = E(c)')
worst = mp.mpf(0)
for I in cases:
    I.mpready()
    for c in [mp.mpc('0.3', '1.1'), mp.mpc('-0.7', '0.2')]:
        tot_g = mp.mpc(0)
        tot_t = mp.mpc(0)
        for ta, tb in zip(I.bmp[:-1], I.bmp[1:]):
            def f(th, ta=ta, tb=tb):
                dv, tau = I.dvec_piece(ta, tb, th)
                return (I.S_plus(dv, c) - I.S0_plus(dv, c))*(tb - ta)*mp.sin(2*th)
            tot_g += mp.quad(f, [0, mp.pi/4, mp.pi/2], method='gauss-legendre', maxdegree=8)
            tot_t += mp.quad(f, [0, mp.pi/4, mp.pi/2], method='tanh-sinh', maxdegree=8)
        d = abs(tot_g - I.E(c))
        worst = max(worst, d)
        logline(out, '  %-36s c=%-12s Psi_B=%s |Psi_B - E|=%s quad-err=%s' % (I.name, mp.nstr(c, 3), mp.nstr(tot_g, 20),
                                                                            mp.nstr(d, 3), mp.nstr(abs(tot_g - tot_t), 3)))
logline(out, 'max |Psi_B - E| = %s' % mp.nstr(worst, 3))

# ---------------------------------------------------------------- (3) interior one-sided limits
logline(out, '\n(3) interior b_k: Lam_+ - Lam0_+ at b_k - e and b_k + e')
for I in cases:
    I.mpready()
    c = mp.mpc('0.45', '0.6')
    for k in range(1, I.n - 1):
        row = []
        for ex in (6, 12, 24, 36):
            e = mp.mpf(10)**(-ex)
            bk = I.bmp[k]
            dl = [bj - bk + e if j != k else e for j, bj in enumerate(I.bmp)]      # tau = b_k - e
            dr = [bj - bk - e if j != k else -e for j, bj in enumerate(I.bmp)]     # tau = b_k + e
            vl = I.Lam_plus(dl, c) - I.Lam0_plus(dl, c)
            vr = I.Lam_plus(dr, c) - I.Lam0_plus(dr, c)
            row.append(abs(vl - vr))
        logline(out, '  %-36s b_%d=%-6s |left - right| at e=1e-6,-12,-24,-36: %s   (value %s)' % (
            I.name, k + 1, mp.nstr(I.bmp[k], 4), ', '.join(mp.nstr(x, 2) for x in row), mp.nstr(vl, 12)))

# ---------------------------------------------------------------- (4) bounds
logline(out, '\n(4) bounds (B\') and the kappa = 0 bound on random samples')
mxB = mp.mpf(0); mxroot = mp.mpf(0); mxk = mp.mpf(0); nfail = 0
for I in cases:
    I.mpready()
    M = I.M
    HF2 = mp.fsum(abs(I.H[i, j])**2 for i in range(M) for j in range(M))
    for _ in range(30):
        l = rng.randrange(I.n - 1)
        ta, tb = I.bmp[l], I.bmp[l + 1]
        u = mp.mpf(10)**(-rng.uniform(0, 12))
        tau = ta + (tb - ta)*(u if rng.random() < 0.5 else 1 - u)
        dv = I.dvec(tau)
        dm, dp_ = tau - ta, tb - tau
        dl = tb - ta
        c = mp.mpc(rng.uniform(-2, 2), 10**rng.uniform(-6, 0.5))
        up, dn, ys = I.split(dv, c)
        if len(up) != I.nplus(dv):
            nfail += 1
            continue
        K = I.normH + abs(c)
        Sp = mp.fsum(up)
        S0p = I.S0_plus(dv, c)
        mxB = max(mxB, abs(Sp - S0p)/(M*K*(2/dl + mp.sqrt(2/(dm*dp_)))))
        for z in (dn if dp_ <= dm else up):
            mxroot = max(mxroot, abs(z)*mp.sqrt(dm*dp_/2)/K)
        c0 = I.normH + mp.mpf(10)**rng.uniform(-1, 1)
        ys0 = [mp.re(z) for z in I.roots(tau, c0)]
        Spos = mp.fsum(z for z in ys0 if z > 0)
        S0 = I.S0_plus(dv, c0)
        mxk = max(mxk, abs(Spos - S0)/((2/dl)*HF2/(c0 - I.normH)))
logline(out, '  count failures %d; max |S_+ - S0_+|/(M K (2/delta_l + sqrt(2/(d_- d_+)))) = %s (<= 1); '
             'max |y| sqrt(d_- d_+/2)/K on the stated half-gap = %s (<= 1); max kappa-ratio = %s (<= 1)' % (
                 nfail, mp.nstr(mxB, 6), mp.nstr(mxroot, 6), mp.nstr(mxk, 6)))
out.close()
