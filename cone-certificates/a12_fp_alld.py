"""a12: certified lower bound of the derivative F'(u) of the scaled decoupled equation, over the same box plan as a10_pointwise.py
(all d >= 2001), for the Poincare-Miranda fixed-point step (CONE_PROOF.md, Lemma B).  Re-uses a10's check_box unchanged and records
Fp per box (Fp <= inf F'(u) on u in [0, U_box + 1e-3]).  In the half-boxes (x >= 0.45) F is divided by (1 - 2x) >= 1/d.
Output logs/alld/fp_alld.json: fpmin as an exact rational lower bound (string), every box record."""
import time, json
import mpmath
from mpmath import iv
import a10_pointwise as A
from a02_jets import lo_str, hi_str, thin_frac

t0 = time.time()
rec = []
fpmin = None
allok = True
for (kind, xb, wb, eb, scale, half, outer, xl, span) in A.box_plan():
    r = A.check_box(xb, wb, eb, scale, half, outer, xl)
    allok &= r['ok']
    fpmin = r['Fp'] if fpmin is None or r['Fp'] < fpmin else fpmin
    rec.append(dict(kind=kind, lo=str(thin_frac(span[0])), hi=str(thin_frac(span[1])), Fp=lo_str(r['Fp']), ok=r['ok'],
                    Umax=hi_str(r['R']), Fp_f=float(r['Fp'])))
print(f"boxes {len(rec)}; all ok = {allok};  min Fp = {float(fpmin):.6f} (exact lower bound {lo_str(fpmin)})  [{time.time()-t0:.0f}s]")
json.dump(dict(fpmin=lo_str(fpmin), fpmin_f=float(fpmin), ok=bool(allok), eps_hi=hi_str(A.EPS1), boxes=rec),
          open('logs/alld/fp_alld.json', 'w'), indent=0)
