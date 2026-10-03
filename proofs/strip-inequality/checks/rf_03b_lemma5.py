# rf_03b: Lemma 5 re-check: int_{-U}^{U} numerically (peak resolved) + tails |u| > U exactly from K_X(u) = sum_n sin(n pi X) e^{-n pi |u|}
import mpmath as mp
mp.mp.dps = 30
U = mp.mpf(2)
for X, a in [(0.05, 3.0 - 1.0j), (0.97, -3.1 + 0.2j), (0.01, 1.5 + 2.0j), (0.999, 0.5 - 0.5j), (0.5, 3.14 + 1.0j),
             (0.3, 0.7 + 0.4j), (0.8, -2.5 + 3.0j)]:
    X = mp.mpf(X); a = mp.mpc(a)
    K = lambda u: mp.sin(mp.pi*X)/(2*(mp.cosh(mp.pi*u) - mp.cos(mp.pi*X)))
    pts = [-U] + [-mp.mpf(10)**k for k in range(0, -6, -1)] + [0] + [mp.mpf(10)**k for k in range(-5, 1)] + [U]
    mid = mp.quad(lambda u: mp.exp(-a*u)*K(u), pts)
    tails = mp.nsum(lambda n: mp.sin(n*mp.pi*X)*(mp.exp(-(n*mp.pi + a)*U)/(n*mp.pi + a) + mp.exp(-(n*mp.pi - a)*U)/(n*mp.pi - a)), [1, mp.inf])
    rhs = mp.sin(a*(1 - X))/mp.sin(a)
    print(f"X={mp.nstr(X, 4)} a={mp.nstr(a, 4)}: |lhs - rhs| = {mp.nstr(abs(mid + tails - rhs), 3)}  rhs = {mp.nstr(rhs, 15)}")
