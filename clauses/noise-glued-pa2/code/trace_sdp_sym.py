"""trace_sdp_sym.py -- level-2 tracial moment relaxation of PA2 (see trace_sdp.py), reduced by the global outcome
shift Z_k (a -> a+1 for all four groups; c_k depends on b - a only).  A symmetrised optimal solution exists, so the
moment classes are taken modulo rotation, reversal and global shift, and the PSD constraint splits into k Hermitian
blocks (Fourier over the shift), each of size 4 + 12 k (orbit representatives of nonempty words of length <= 2).
usage: python trace_sdp_sym.py k [solver]"""
import sys, os, itertools, time
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from trace_sdp import cglmp_tensor, reduce_cyc   # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402


def canon_shift(w, k):
    n = len(w); best = None
    for s in (w, tuple(reversed(w))):
        for i in range(n):
            r = s[i:] + s[:i]
            o0 = r[0][1]
            key = tuple((g, (o - o0) % k) for g, o in r)
            if best is None or key < best:
                best = key
    return best


def build(k):
    reps = [((g, 0),) for g in range(4)]
    reps += [((g1, 0), (g2, dl)) for g1 in range(4) for g2 in range(4) if g2 != g1 for dl in range(k)]
    n = len(reps)
    cls = {}
    # entries: for each (i, j, r): value code
    code = np.zeros((n, n, k), dtype=np.int64)
    for i, u in enumerate(reps):
        ur = tuple(reversed(u))
        for j, v in enumerate(reps):
            for r in range(k):
                vs = tuple((g, (o + r) % k) for g, o in v)
                w = reduce_cyc(ur + vs)
                if w is None: c = -1
                elif len(w) == 1: c = -2
                else: c = cls.setdefault(canon_shift(w, k), len(cls))
                code[i, j, r] = c
    return reps, code, cls


def solve(k, solver='CLARABEL', verbose=False):
    t0 = time.time()
    reps, code, cls = build(k)
    n = len(reps); ncls = len(cls)
    y = cp.Variable(ncls)
    om = np.exp(2j * np.pi / k)
    cons = []
    blocks = []
    for s in range(k):
        ph = om ** (s * np.arange(k))
        # M_s[i,j] = sum_r ph[r] * val(i,j,r); val = y[c] (c>=0), 1 (c=-2), 0 (c=-1)
        rows, cols, data_re, data_im, ccol = [], [], [], [], []
        const = np.zeros((n, n), complex)
        for i in range(n):
            for j in range(n):
                for r in range(k):
                    c = code[i, j, r]
                    if c == -2: const[i, j] += ph[r]
                    elif c >= 0:
                        rows.append(i * n + j); ccol.append(c); data_re.append(ph[r].real); data_im.append(ph[r].imag)
        Are = sp.csr_matrix((data_re, (rows, ccol)), shape=(n * n, ncls))
        Aim = sp.csr_matrix((data_im, (rows, ccol)), shape=(n * n, ncls))
        Mre = cp.reshape(Are @ y, (n, n), order='C') + const.real
        Mim = cp.reshape(Aim @ y, (n, n), order='C') + const.imag
        big = cp.bmat([[Mre, -Mim], [Mim, Mre]])
        Bs = cp.Variable((2 * n, 2 * n), symmetric=True)
        cons += [Bs == big, Bs >> 0]
        blocks.append((Mre, Mim))
    C = cglmp_tensor(k)
    obj = 0
    for x, yy, a, b in itertools.product(range(2), range(2), range(k), range(k)):
        w = reduce_cyc(((x, a), (2 + yy, b)))
        obj = obj + C[x, yy, a, b] * y[cls[canon_shift(w, k)]]
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver=solver, verbose=verbose)
    target = k * core.ime(k)
    print(f"k={k}: blocks {k} x {n} (Hermitian), classes={ncls}  SDP bound = {prob.value:.10f}  "
          f"k*I_ME(k) = {target:.10f}  ratio-1 = {prob.value / target - 1:+.2e}  status={prob.status}  "
          f"({time.time() - t0:.0f}s)", flush=True)
    return prob, y, cls, reps, code


if __name__ == '__main__':
    k = int(sys.argv[1]); solver = sys.argv[2] if len(sys.argv) > 2 else 'CLARABEL'
    solve(k, solver)
