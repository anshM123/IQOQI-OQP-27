"""rc02: Theorem RI-C (Psi(c) = E(c), Im c > 0), Lemma A (count/location), Lemma B (bounds, incl. the half-plane split),
the trace identity, Lemma E (boundary values) and Step 1 (Psi_delta' = boundary terms), at dps 40.
Psi is integrated with Gauss-Legendre on [0,1] (the integrand is analytic on [0,1] for Im c > 0), split near the real-c0
branch points when Im c is small; error estimate = |GL - tanh-sinh|.  S_+ - S0_+ is computed directly (no trace identity)."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline, fmt

mp.mp.dps = 40
out = open('rc02_complex.log', 'w')
rng = random.Random(777)


def block(PHP, BHB, X):
    r = BHB.shape[0]; q = PHP.shape[0]
    H = sp.zeros(r + q, r + q)
    H[:r, :r] = BHB; H[r:, r:] = PHP; H[r:, :r] = X; H[:r, r:] = X.H
    return H


def randX(q, r, nr=9, den=4, scale=1):
    return sp.Matrix(q, r, lambda i, j: (sp.Rational(rng.randint(-nr, nr), den)
                                         + sp.I*sp.Rational(rng.randint(-nr, nr), den))*scale)


insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'),
         Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'),
         Inst.proj(herm(rng, 5), 3, 'rand_M5_r3'),
         Inst.proj(herm(rng, 6), 1, 'rank1B_M6'),
         Inst.proj(herm(rng, 6), 5, 'corank1_M6'),
         Inst.proj(with_spectrum(rng, [1, 1, 1, -2, -2]), 2, 'degenH_M5'),
         Inst.proj(block(with_spectrum(rng, [1, 1]), with_spectrum(rng, [-1, -1]), randX(2, 2)), 2, 'degen_blocks_M4'),
         Inst.proj(block(herm(rng, 2), sp.zeros(2, 2), randX(2, 2)), 2, 'zero_BHB_M4'),
         Inst.proj(block(herm(rng, 3), herm(rng, 2), randX(3, 2, scale=sp.Rational(1, 10**6))), 2, 'near_comm_1e-6_M5'),
         Inst.proj((herm(rng, 4)*1000).applyfunc(sp.expand), 2, 'scale1e3_M4')]


def integrand(I, tau, c):
    dv = I.dvec(tau)
    return I.S_plus(dv, c) - I.S0_plus(dv, c)


def Psi(I, c, extra=()):
    cuts = sorted(set([mp.mpf(0), mp.mpf(1)/4, mp.mpf(1)/2, mp.mpf(3)/4, mp.mpf(1)] + [x for x in extra if 0 < x < 1]))
    f = lambda t: integrand(I, t, c)
    g = mp.quad(f, cuts, method='gauss-legendre', maxdegree=8)
    t = mp.quad(f, cuts, method='tanh-sinh', maxdegree=8)
    return g, abs(g - t)


# ---------------------------------------------------------------- (1) RI-C
logline(out, '(1) Theorem RI-C: Psi(c) = E(c)')
worst = mp.mpf(0)
for I in insts:
    I.mpready()
    s = float(I.normH)
    for (re_, im_) in [(sp.Rational(1, 3), 2), (sp.Rational(-1, 2), sp.Rational(1, 2)), (sp.Rational(1, 5), sp.Rational(1, 20)),
                       (sp.Rational(0), sp.Rational(1, 300))]:
        re_s = sp.Rational(re_*sp.Rational(s).limit_denominator(4))
        im_s = sp.Rational(im_*sp.Rational(s).limit_denominator(4))
        c = mp.mpc(mp.mpf(re_s.p)/re_s.q, mp.mpf(im_s.p)/im_s.q)
        extra = []
        if im_s < sp.Rational(1, 10)*sp.Rational(s).limit_denominator(4):
            pts, aux = I.branch_points(re_s, near_real=False)
            e = mp.im(c)
            for t0 in pts:
                for k in (-30, -10, -3, -1, 0, 1, 3, 10, 30):
                    extra.append(t0 + k*e)
        t0 = time.time()
        Pv, err = Psi(I, c, extra)
        Ev = I.E(c)
        d = abs(Pv - Ev)
        worst = max(worst, d/max(1, abs(Ev)))
        logline(out, '  %-22s c=%-28s Psi=%-50s |Psi-E|=%s quad-err=%s (%.0fs)' % (
            I.name, mp.nstr(c, 8), mp.nstr(Pv, 22), mp.nstr(d, 3), mp.nstr(err, 3), time.time() - t0))
logline(out, 'max |Psi - E|/max(1,|E|) = %s' % mp.nstr(worst, 3))

# ---------------------------------------------------------------- (2) Lemma A, B, trace identity on random samples
logline(out, '\n(2) Lemma A (count, Im bounds), Lemma B (i),(ii),(iii), trace identity: random samples')
cnt_fail = 0; nsamp = 0
mxA = mp.mpf(0); mxBi = mp.mpf(0); mxBii = mp.mpf(0); mxBwrong = mp.mpf(0); mxBiii = mp.mpf(0); mxtr = mp.mpf(0)
with mp.workdps(60):
    for I in insts:
        I._mp_dps = None
        I.mpready()
        M = I.M
        for _ in range(40):
            u = rng.random()
            tau = mp.mpf(10)**(-rng.uniform(0, 14)) if u < 0.3 else (1 - mp.mpf(10)**(-rng.uniform(0, 14)) if u < 0.6
                                                                       else mp.mpf(rng.random()))
            imc = mp.mpf(10)**rng.uniform(-25, 1)
            c = mp.mpc(rng.uniform(-2, 2)*float(I.normH), imc)
            dv = I.dvec(tau)
            up, dn, ys = I.split(dv, c)
            nsamp += 1
            if len(up) != I.nplus(dv) or len(up) + len(dn) != M:
                cnt_fail += 1
                continue
            K = I.normH + abs(c)
            for z in up:
                mxA = max(mxA, (imc/(1 - tau))/mp.im(z))          # Lemma A(a): Im y >= Im c/(1 - tau)  <=> ratio <= 1
                mxBi = max(mxBi, abs(z)*min(tau, 1 - tau)/K)
                if tau <= 0.5:
                    mxBii = max(mxBii, abs(z)*mp.sqrt(tau*(1 - tau))/K)
                else:
                    mxBwrong = max(mxBwrong, abs(z)*mp.sqrt(tau*(1 - tau))/K)
            for z in dn:
                mxA = max(mxA, (imc/tau)/(-mp.im(z)))               # Im y <= -Im c/tau
                mxBi = max(mxBi, abs(z)*min(tau, 1 - tau)/K)
                if tau >= 0.5:
                    mxBii = max(mxBii, abs(z)*mp.sqrt(tau*(1 - tau))/K)
            Sp, Sm = mp.fsum(up), mp.fsum(dn)
            S0p, S0m = I.S0_plus(dv, c), I.S0_minus(dv, c)
            mxtr = max(mxtr, abs(Sp + Sm - S0p - S0m)/max(1, abs(Sp) + abs(Sm)))
            mxBiii = max(mxBiii, abs(Sp - S0p)/(M*K*(2 + 1/mp.sqrt(tau*(1 - tau)))))
    for I in insts:
        I._mp_dps = None
logline(out, '  samples %d, count failures %d' % (nsamp, cnt_fail))
logline(out, '  Lemma A(a) max [Im c/(1-tau)]/Im y (C_+) and [Im c/tau]/|Im y| (C_-): %s  (must be <= 1)' % mp.nstr(mxA, 12))
logline(out, '  Lemma B(i)  max |y| min(tau,1-tau)/K: %s (<= 1)' % mp.nstr(mxBi, 12))
logline(out, '  Lemma B(ii) max |y| sqrt(tau(1-tau))/K on the stated half-plane/half-interval: %s (<= 1)' % mp.nstr(mxBii, 12))
logline(out, '  same ratio for C_+ roots with tau > 1/2 (NOT claimed bounded): %s' % mp.nstr(mxBwrong, 6))
logline(out, '  Lemma B(iii) max |S_+ - S0_+|/(M K (2 + (tau(1-tau))^-1/2)): %s (<= 1)' % mp.nstr(mxBiii, 12))
logline(out, '  trace identity max |S_+ + S_- - S0_+ - S0_-|/(|S_+|+|S_-|): %s' % mp.nstr(mxtr, 3))

# ---------------------------------------------------------------- (3) Lemma E boundary values
logline(out, '\n(3) Lemma E: Im S_+(tau, c0 + i eps) -> (1/2) sum |Im y_i(tau, c0)|')
for I in insts[:6]:
    I.mpready()
    for tau in [mp.mpf('0.137'), mp.mpf('0.5'), mp.mpf('0.861')]:
        c0 = mp.mpf('0.1')*I.normH
        ys0 = I.roots(tau, c0)
        target = mp.fsum(abs(mp.im(z)) for z in ys0)/2
        row = []
        for eps in [mp.mpf(10)**(-k) for k in (2, 5, 10, 20)]:
            dv = I.dvec(tau)
            row.append(abs(mp.im(I.S_plus(dv, mp.mpc(c0, eps))) - target))
        logline(out, '  %-22s tau=%-6s target=%s  |diff| at eps=1e-2,-5,-10,-20: %s' % (
            I.name, mp.nstr(tau, 4), mp.nstr(target, 12), ', '.join(mp.nstr(x, 2) for x in row)))

# ---------------------------------------------------------------- (4) Step 1: Psi_delta'(c) = boundary terms
logline(out, '\n(4) Step 1: d/dc Psi_delta = (Lam_+ - Lam0_+)(1-delta) - (Lam_+ - Lam0_+)(delta)')
for I in insts[:5]:
    I.mpready()
    c = mp.mpc('0.3', '0.7')*max(1, I.normH)
    for delta in [mp.mpf('0.1'), mp.mpf('0.01')]:
        Pd = lambda cc: mp.quad(lambda t: integrand(I, t, cc), [delta, mp.mpf(1)/2, 1 - delta], method='gauss-legendre')
        lhs = mp.diff(Pd, c)
        bt = lambda t: I.Lam_plus(I.dvec(t), c) - I.Lam0_plus(I.dvec(t), c)
        rhs = bt(1 - delta) - bt(delta)
        logline(out, '  %-22s delta=%-5s Psi_delta\' = %s  boundary = %s  diff %s' % (
            I.name, mp.nstr(delta, 3), mp.nstr(lhs, 18), mp.nstr(rhs, 18), mp.nstr(abs(lhs - rhs), 3)))
out.close()
