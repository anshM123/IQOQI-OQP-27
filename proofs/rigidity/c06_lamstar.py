"""c06: lam* = log(2)/(2 pi) minimises f(lam) = lam/4 + h_lam(1/4), with f(lam*) = Phi_c(1/4,1/4) = G/pi^2 (Catalan G).
h_lam(x) = -(1/pi^2) Im Li2(e^{-pi lam} e^{-i pi x}) at the point x + 0i (40 digits)."""
import mpmath as mp
mp.mp.dps = 40
h = lambda lam, x: -mp.im(mp.polylog(2, mp.e ** (-mp.pi * lam) * mp.expjpi(-x))) / mp.pi ** 2
f = lambda lam: lam / 4 + h(lam, mp.mpf(1) / 4)
ls = mp.log(2) / (2 * mp.pi)
phic = (2 * mp.clsin(2, mp.pi / 2) + mp.clsin(2, mp.pi)) / (2 * mp.pi ** 2)
print("lam*            =", ls)
print("f(lam*)         =", f(ls))
print("Phi_c(1/4,1/4)  =", phic, "  G/pi^2 =", mp.catalan / mp.pi ** 2)
print("f'(lam*)        =", mp.diff(f, ls))
print("f''(lam*)       =", mp.diff(f, ls, 2), " (> 0: strict minimum)")
print("f(lam* +- 0.01) - f(lam*) =", f(ls + mp.mpf('0.01')) - f(ls), f(ls - mp.mpf('0.01')) - f(ls))
