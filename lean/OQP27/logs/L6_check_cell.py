# Independent check of Hyp_CellIneqSingle with the exact Lean definitions:
#   cellFunctional ell C = sum_{x,y in Z_N} K(x,y) * Re Tr(Q_x Q_{y+d}) / M,
#   K(x,y) = G(L_{x+1}-L_y) - G(L_x-L_y) - G(L_{x+1}-L_{y+1}) + G(L_x-L_{y+1}),  L_n = sum_{i<n} ell[i % d],
#   G(u) = -(N^2/(2 pi^2)) Cl2(2 pi u/N),  windowValue = -2 G(d).
import numpy as np, mpmath as mp
rng = np.random.default_rng(7)
def cl2(t): return float(mp.clsin(2, t))
def haar(M):
    Z = (rng.standard_normal((M,M)) + 1j*rng.standard_normal((M,M)))/np.sqrt(2)
    Q, R = np.linalg.qr(Z); return Q*(np.diag(R)/abs(np.diag(R)))
def config(d, M):
    N = 4*d; Q = np.zeros((N,M,M), complex)
    for k in range(d):
        U = haar(M); labels = rng.integers(0,4,size=M)
        for a in range(4):
            P = U @ np.diag((labels==a).astype(float)) @ U.conj().T
            Q[(k - d*a) % N] = P
    return Q
worst = -1e9
for d in [3,4,5]:
    N = 4*d
    G = lambda u: -(N**2/(2*np.pi**2))*cl2(2*np.pi*u/N)
    W = -2*G(d)
    for trial in range(6):
        ell = d*rng.dirichlet(np.ones(d))
        L = [sum(ell[i % d] for i in range(n)) for n in range(N+1)]
        K = np.array([[G(L[x+1]-L[y]) - G(L[x]-L[y]) - G(L[x+1]-L[y+1]) + G(L[x]-L[y+1]) for y in range(N)] for x in range(N)])
        M = int(rng.integers(2,4)); Q = config(d, M)
        val = sum(K[x,y]*np.trace(Q[x]@Q[(y+d)%N]).real/M for x in range(N) for y in range(N))
        worst = max(worst, val - W)
    # window configuration: Q_x = 1 for x in [0,d) (label 0 at each site), tight
    ell = d*rng.dirichlet(np.ones(d))
    L = [sum(ell[i % d] for i in range(n)) for n in range(N+1)]
    K = np.array([[G(L[x+1]-L[y]) - G(L[x]-L[y]) - G(L[x+1]-L[y+1]) + G(L[x]-L[y+1]) for y in range(N)] for x in range(N)])
    Qw = np.zeros((N,1,1)); Qw[:d] = 1
    valw = sum(K[x,y]*Qw[x,0,0]*Qw[(y+d)%N,0,0] for x in range(N) for y in range(N))
    print(f"d={d}: window value {valw:.10f} vs -2G(d) {W:.10f}")
print("max cellFunctional - windowValue over random configurations:", worst)
