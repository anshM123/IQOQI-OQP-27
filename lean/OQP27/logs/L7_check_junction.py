# Numerical sanity checks (not part of any proof) for module L7 (OQP27/Classical*.lean).
# Checks, in 30-digit arithmetic, the statements of OQP27/ClassicalJunction.lean:
#   cot_le_kbarR:      cot(pi m/N) <= kbarR N m              (1 <= m, 2(m+1) <= N)
#   kbarR_sub_cot_le:  kbarR N m - cot(pi m/N) <= (N/pi)/(6 m (m^2-1))   (2 <= m, 2(m+1) <= N)
#   kbarR_one_sub_cot: (N/pi)(7/24) < kbarR N 1 - cot(pi/N)  (N >= 8)
#   junction_margin:   2 sc + fw < -e(1)                     (N >= 8)
#   oddness kbarR N (N-m) = -kbarR N m
# with kbarR N m = N^2/(2 pi^2) (2 Cl2(2 pi m/N) - Cl2(2 pi (m+1)/N) - Cl2(2 pi (m-1)/N)).
import sys
import mpmath as mp
mp.mp.dps = 30
def cl2(x): return mp.clsin(2, x)
def kbarR(N, m):
    N = mp.mpf(N); m = mp.mpf(m)
    return N**2/(2*mp.pi**2)*(2*cl2(2*mp.pi*m/N) - cl2(2*mp.pi*(m+1)/N) - cl2(2*mp.pi*(m-1)/N))
def cot(x): return mp.cot(x) if x != 0 else mp.mpf(0)
bad = 0
worst = {}
Ns = list(range(4, 81)) + [100, 101, 128, 200]
for N in Ns:
    for m in range(1, N):
        k = cot(mp.pi*m/N); kb = kbarR(N, m); e = k - kb
        if 2*(m+1) <= N and e > 0: bad += 1
        if 2*(m+1) <= N and m >= 2:
            bnd = (N/mp.pi)/(6*m*(m*m-1))
            r = -e/bnd
            worst['J2'] = max(worst.get('J2', 0), float(r))
            if -e > bnd: bad += 1
        if m != 0 and abs(kbarR(N, N-m) + kbarR(N, m)) > mp.mpf(10)**-20: bad += 1
    if N >= 8:
        e1 = cot(mp.pi/N) - kbarR(N, 1)
        if not ((N/mp.pi)*mp.mpf(7)/24 < -e1): bad += 1
        sc = sum((m-1)*(kbarR(N,m)-cot(mp.pi*m/N)) for m in range(2, N//2))
        fw = sum(m*(kbarR(N,m)-cot(mp.pi*m/N)) for m in range(2, N//2))
        if not (2*sc + fw < -e1): bad += 1
        worst['margin'] = max(worst.get('margin', 0), float((2*sc+fw)/(-e1)))
print("N range:", Ns[0], "...", Ns[-1], "; violations:", bad)
print("max ratio (kbarR - cot)/((N/pi)/(6m(m^2-1))) over 2 <= m, 2(m+1) <= N:", round(worst['J2'], 6))
print("max ratio (2 sc + fw)/(-e(1)) over N >= 8:", round(worst['margin'], 6))
