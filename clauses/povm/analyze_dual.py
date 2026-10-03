"""
analyze_dual.py -- structure of the tight POVM relaxation at the optimum (feasibility of an exact certificate).
For each PSD block b compare
   r_DKZ = rank of the block at the symmetrised DKZ functional,
   r_Z   = numerical rank of the IPM primal (moment) block (analytic-centre-like -> maximal rank on the optimal face),
   r_X   = numerical rank of the IPM dual Gram block.
Complementary slackness: X_b B_b(DKZ) = 0, so r_X <= n - r_DKZ.  An exact certificate by face restriction to
ker B_b(DKZ) (as for the PVM certificates) is expected to work if r_Z = r_DKZ and r_X = n - r_DKZ for all b.
usage: python analyze_dual.py d [h-list e.g. 1,3] [loc]
"""
import sys
import time
import numpy as np
from povm_sdp import build, dense_blocks, solve_ipm, S_to_I, I_ME
from validate_sdp import images, Evaluator
from povm_core import dkz_povms


def dkz_y(st, d):
    ev = Evaluator(images(dkz_povms(d, 1), d), d)
    y = np.zeros(st.nvar)
    for v, (rep, kind, f) in enumerate(st.var_info):
        val = ev.word(rep)
        y[v] = (val / f).real if kind == 'real' else (val.real if kind == 're' else val.imag)
    return y


def numrank(ev, tol):
    return int(np.sum(ev > tol))


if __name__ == "__main__":
    d = int(sys.argv[1])
    hs = tuple(int(t) for t in sys.argv[2].split(',')) if len(sys.argv) > 2 else (1, 3)
    loc = 'loc' in sys.argv[3:]
    adj = 'adj' in sys.argv[3:]
    t0 = time.time()
    st, blocks, obj, const = build(d, loc=loc, dbl=True, dbl_h=hs, verbose=False, adj=adj)
    db = dense_blocks(blocks, st.nvar)
    res = solve_ipm(db, obj, const, st.nvar)
    print(f"d={d} h={hs} loc={loc} adj={adj}: SOS bound S = {res['pobj_bound']:.13f}  I* - I_ME = "
          f"{S_to_I(res['pobj_bound'], d) - I_ME(d):+.2e}  (rp {res['rp']:.1e}, gap {res['gap']:.1e}) "
          f"[{time.time() - t0:.0f}s]")
    yD = dkz_y(st, d)
    SD = const + sum(c * yD[v] for v, c in obj.items())
    print(f"   S(DKZ) = {SD:.13f}")
    tot_ok = True
    for bi, (lab, H0, Hv) in enumerate(db):
        n = H0.shape[0]
        BD = H0 + sum(yD[v] * H for v, H in Hv.items())
        eD = np.linalg.eigvalsh((BD + BD.conj().T) / 2)
        Zb = res['Z'][bi]
        Xb = res['X'][bi]
        eZ = np.linalg.eigvalsh((Zb + Zb.conj().T) / 2)
        eX = np.linalg.eigvalsh((Xb + Xb.conj().T) / 2)
        rD = numrank(eD, 1e-8)
        rZ = numrank(eZ, 1e-5)
        rX = numrank(eX, 1e-5)
        ok = (rZ == rD) and (rX == n - rD)
        tot_ok &= ok
        # smallest "nonzero" eigenvalues to judge the gaps
        gZ = eZ[eZ > 1e-5].min() if rZ else 0
        gX = eX[eX > 1e-5].min() if rX else 0
        zX = eX[eX <= 1e-5].max() if rX < n else 0
        print(f"   block {bi:2d} {str(lab):16s} n={n:3d}  rank DKZ={rD:3d}  rank Z={rZ:3d}  rank X={rX:3d}  "
              f"n-rDKZ={n - rD:3d}  minpos eig Z {gZ:.1e} X {gX:.1e}  max small eig X {zX:.1e}  {'ok' if ok else '**'}")
    print(f"   strict complementarity w.r.t. DKZ on all blocks: {tot_ok}")
