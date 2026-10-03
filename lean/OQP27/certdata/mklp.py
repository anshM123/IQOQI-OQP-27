"""Write OQP27/CertLP.lean: the LP certificates QD2/certs/cert_d{d}.json (d = 2, 3) re-checked in Lean.
The certificate (q = 16, cells and float weights unchanged; R, eps, beta added) is checked with the Clausen table
assembled from chunks (OQP27/CertChunked.lean); every literal table is produced by leanemu.py (an exact
re-implementation of the Lean checker) and is proved equal to the computed one by the Lean kernel.
usage (from OQP27/certdata): python mklp.py 2 3"""
import sys, json, os
from fractions import Fraction as F
import mpmath as mp
import leanemu as E
import gencert as G

mp.mp.dps = 50
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QD2 = os.path.join(os.path.dirname(os.path.dirname(ROOT)), "cone-certificates")   # LP certificates of this repository
CHUNK = 12


def rs(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def qi(I):
    return f"⟨{rs(I.lo)}, {rs(I.hi)}⟩"


def lst(L, indent="    "):
    return "[" + (",\n" + indent).join(qi(I) for I in L) + "]"


def build_lp(d):
    c = json.load(open(os.path.join(QD2, "certs", f"cert_d{d}.json")))
    q = c['q']; cells = c['cells']; lamQ = [F(x) for x in c['lam']]
    gT = E.gTab(d, q)
    UT = [E.uList(d, gT, n) for n in cells]
    n = d - 1; K = len(cells)
    U = mp.matrix(n, K)
    for k in range(K):
        for i in range(n):
            I = UT[k][i]
            U[i, k] = (mp.mpf(I.lo.numerator) / I.lo.denominator + mp.mpf(I.hi.numerator) / I.hi.denominator) / 2
    Rm = mp.inverse(U * U.T)
    RQ = [[G.rat_sig(Rm[i, j], 22) for j in range(n)] for i in range(n)]
    ok, info, _, _ = E.fullCheck(d, q, cells, lamQ, RQ, F(1, 2), F(1, 10 ** 30))
    eps = G.nice_up(max(info['maxrow'] * 4, F(1, 10 ** 40)))
    beta = G.nice_up(max(info['maxRr'] * 4, F(1, 10 ** 40)))
    ok, info, _, _ = E.fullCheck(d, q, cells, lamQ, RQ, eps, beta)
    print(f"d={d}: K={K} ok={ok} min certified weight {float(info['mincol']):.4e}", file=sys.stderr)
    assert ok
    return dict(d=d, q=q, cells=cells, lam=lamQ, R=RQ, eps=eps, beta=beta)


def block(d):
    c = build_lp(d)
    q = c['q']; Q = 4 * d * q; nmax = 2 * d * q
    sT = E.sinTab(Q); hT = E.hTab(Q)
    out = []
    out.append(G.lean_cert(c, f"lpCert{d}").replace(f"/-- Certificate for `d = {d}`: {len(c['cells'])} integer cells. -/",
               f"/-- `QD2/certs/cert_d{d}.json` (`q = {q}`, {len(c['cells'])} cells, weights = the stored floats). -/"))
    out.append(f"/-- Enclosures of `sin(2π b/{Q})`, `b < {Q}`. -/\ndef sLit{Q} : List QI :=\n  {lst(sT)}\n")
    out.append(f"theorem sinTab{Q} : sinTab {Q} = sLit{Q} := qiListEqb_eq (by decide +kernel)\n")
    out.append(f"/-- Enclosures of `H({Q}, a+1)`, `a < {Q}`. -/\ndef hLit{Q} : List QI :=\n  {lst(hT)}\n")
    out.append(f"theorem hTab{Q} : hTab {Q} = hLit{Q} := qiListEqb_eq (by decide +kernel)\n")
    starts = list(range(0, nmax + 1, CHUNK))
    names = []
    for j, lo in enumerate(starts):
        ln = min(CHUNK, nmax + 1 - lo)
        L = [E.clEnc(Q, sT, hT, lo + i) for i in range(ln)]
        nm = f"clLit{Q}_{j}"
        names.append((nm, lo, ln))
        out.append(f"/-- Enclosures of `Cl₂(2π c/{Q})`, `c = {lo}, …, {lo + ln - 1}`. -/\ndef {nm} : List QI :=\n  {lst(L)}\n")
        out.append(f"theorem {nm}_ok : ClChunkOK {Q} {lo} {nm} :=\n"
                   f"  clChunkOK_of_eq (by norm_num) sinTab{Q} hTab{Q}\n"
                   f"    (lo := {lo}) (len := {ln}) (qiListEqb_eq (by decide +kernel))\n")
    # concatenation, right nested
    cat = " ++ (".join(nm for nm, _, _ in names) + ")" * (len(names) - 1)
    out.append(f"/-- The Clausen table `Cl₂(2π c/{Q})`, `c = 0, …, {nmax}`. -/\ndef clLit{Q} : List QI :=\n  {cat}\n")
    # proof of ClChunkOK for the concatenation
    def prf(k):
        nm, lo, ln = names[k]
        if k == len(names) - 1:
            return f"{nm}_ok"
        nxt = names[k + 1][1]
        return f"clChunkOK_append' (a := {ln}) (lo' := {nxt}) {nm}_ok rfl rfl\n    ({prf(k + 1)})"
    out.append(f"theorem clLit{Q}_ok : ClChunkOK {Q} 0 clLit{Q} :=\n  {prf(0)}\n")
    out.append(f"theorem gLP{d}_ok : GTabOK {d} {q} (gTabOf {d} {q} clLit{Q}) :=\n"
               f"  gTabOK_gTabOf (by norm_num) (by norm_num) clLit{Q}_ok (by decide +kernel)\n")
    out.append(f"/-- The rest of the check, with the `Ĝ` table computed from `clLit{Q}`. -/\n"
               f"theorem lpCert{d}_check : lpCert{d}.fullCheckU (lpCert{d}.uTableWith (gTabOf {d} {q} clLit{Q})) = true := by\n"
               f"  decide +kernel\n")
    out.append(f"/-- `ConeCert {d}` from the LP certificate `QD2/certs/cert_d{d}.json`. -/\n"
               f"theorem coneCert_{d}_lp : ConeCert {d} :=\n"
               f"  lpCert{d}.fullCheckWith_sound _ gLP{d}_ok lpCert{d}_check\n")
    return "\n".join(out)


def main():
    ds = [int(a) for a in sys.argv[1:]]
    head = f"""import OQP27.CertChunked

/-!
# The LP certificates of `QD2/certs/` for d = {", ".join(str(d) for d in ds)}, re-checked in Lean (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`cone-certificates/certs/cert_d<d>.json` (written by `QD2/run_verify.py`) store `q = 16`, the cells
`n^(k)` (`ℓ^(k) = n^(k)/16`, all `n_r ≥ 1`) and floating-point weights `λ̃`.  Here they become
`OQP27.ConeCertificate`s without change: same `q`, same cells, `λ̃` = the exact binary values of the stored
floats; only the approximate inverse `R` of `U Uᵀ` (which `verify_cone.py` recomputes at run time and does not
store) and the bounds `eps`, `beta` are added.  These certificates have more columns than rows, so they exercise
the minimum-norm correction `λ = λ̃ + Uᵀ y` of `OQP27.coneCheckCore` in the non-square case.

With `q = 16` the Clausen table (`Q = 64d` angles) is too large for one kernel evaluation; it is assembled from
chunks (`OQP27/CertChunked.lean`): the sine table, the `H` table and every chunk of the Clausen table are literal
lists proved equal to the computed ones by the kernel (`decide +kernel`).  No `native_decide`, no hypotheses.

Generated by `OQP27/certdata/mklp.py`.
-/

namespace OQP27

"""
    body = "\n".join(block(d) for d in ds)
    with open(os.path.join(ROOT, "CertLP.lean"), "w", encoding="utf-8") as fh:
        fh.write(head + body + "\nend OQP27\n")
    print("wrote CertLP.lean")


if __name__ == "__main__":
    main()
