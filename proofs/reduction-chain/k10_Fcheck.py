"""Item 5: the programme's enclosures of F^(2j)(m) (verify_gauss.py head, run on a copy) vs an independent evaluation of
F(b) = E Ghat(d X_b) by direct quadrature over the Beta density (mpmath, 30 digits) and central finite differences."""
import sys, mpmath as mp
d = 60
src = open('spot/verify_gauss.py', encoding='utf-8').read().split('# ---------------------------------------------------------------- P_{v,r} by prefix sums')[0]
sys.argv = ['verify_gauss.py', str(d), '120']
g = {'__name__': 'x'}
exec(compile(src, 'vgh', 'exec'), g)
Fv = g['Fv']
mp.mp.dps = 30
N = 4 * d
pref = -(mp.mpf(N) ** 2) / (2 * mp.pi ** 2)
Gh = lambda u: pref * (mp.clsin(2, 2 * mp.pi * u / N) + mp.clsin(2, 2 * mp.pi * (2 * d - u) / N))
def F(b):
    b = mp.mpf(b); lb = mp.log(mp.beta(b, d - b))
    dens = lambda x: mp.exp((b - 1) * mp.log(x) + (d - b - 1) * mp.log(1 - x) - lb)
    mode = min(max((b - 1) / (d - 2), mp.mpf('0.01')), mp.mpf('0.99'))
    return mp.quad(lambda x: Gh(d * x) * dens(x), [0, mode / 2, mode, (1 + mode) / 2, 1])
for m in [1, 2, 7, 30, 59]:  # breakpoints clipped to (0,1) (first run had invalid breakpoints at m = 1, 59)
    h = mp.mpf('1e-3')
    f0 = F(m); fp = F(m + h); fm = F(m - h); fp2 = F(m + 2 * h); fm2 = F(m - 2 * h)
    d2 = (-fp2 + 16 * fp - 30 * f0 + 16 * fm - fm2) / (12 * h * h)
    d4 = (fp2 - 4 * fp + 6 * f0 - 4 * fm + fm2) / h ** 4
    enc = Fv[m]
    print(f"m={m}: F quad {mp.nstr(f0, 18)} vs enclosure mid {mp.nstr(enc[0].mid, 18)} (width {mp.nstr(enc[0].delta, 3)});  "
          f"F'' fd {mp.nstr(d2, 12)} vs {mp.nstr(enc[1].mid, 12)};  F'''' fd {mp.nstr(d4, 6)} vs {mp.nstr(enc[2].mid, 6)}", flush=True)
