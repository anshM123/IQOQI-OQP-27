# Check of the exact Lean statement Hyp_ClassicalTheoremB d for small d:
#   clockFa a = sum_{j<k} Re[h_{k-j} * I^((a_k - a_j) mod 4)],  h_m = 1/cos(pi m/2d) - i/sin(pi m/2d)
#   FDKZ d   = sum_{m=1}^{d-1} (d-m)/cos(pi m/2d)
#   IsOneStep a <=> exists c in Z4, r < d with a_k = c + [r <= k]
import itertools, math, cmath
for d in range(2, 9):
    h = {m: 1/math.cos(math.pi*m/(2*d)) - 1j/math.sin(math.pi*m/(2*d)) for m in range(1, d)}
    FD = sum((d-m)/math.cos(math.pi*m/(2*d)) for m in range(1, d))
    onestep = set()
    for c in range(4):
        for r in range(d):
            onestep.add(tuple((c + (1 if r <= k else 0)) % 4 for k in range(d)))
    worst = -1e9; eqset = set(); viol = 0
    for a in itertools.product(range(4), repeat=d):
        F = sum((h[k-j] * (1j)**((a[k]-a[j]) % 4)).real for j in range(d) for k in range(j+1, d))
        if F > FD + 1e-9: viol += 1
        if abs(F - FD) < 1e-9: eqset.add(a)
        worst = max(worst, F - FD)
    print(f"d={d}: max F-FDKZ={worst:.2e}, violations={viol}, #equality={len(eqset)}, #onestep={len(onestep)}, equality==onestep: {eqset==onestep}")
