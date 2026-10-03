"""
break_tests.py -- referee tamper tests: the P2 verifier must FAIL (or abort) on wrong inputs / wrong claims.
Each test copies the published theorem folder (noise-literal/) into a scratch directory, applies one modification, and runs the relevant verifier items in
a fresh Python process.  Expected outcome per test is printed next to the observed one.
usage: python break_tests.py <scratch_dir>
"""
import json
import os
import shutil
import subprocess
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
SNAP = os.path.join(HERE, "..")   # the published theorem folder (noise-literal/)
SCR = sys.argv[1]
ENV = dict(os.environ, OMP_NUM_THREADS="1", MKL_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")


def fresh(name):
    d = os.path.join(SCR, name)
    if os.path.exists(d):
        shutil.rmtree(d)
    shutil.copytree(SNAP, d)
    return d


def run(d, code):
    r = subprocess.run([sys.executable, "-c", code], cwd=d, env=ENV, capture_output=True, text=True, timeout=1800)
    out = (r.stdout + r.stderr).strip().splitlines()
    status = "FAIL" if any("[FAIL]" in l for l in out) else ("ABORT" if r.returncode != 0 else
                                                             ("PASS" if any("[PASS]" in l for l in out) else "?"))
    return status, out


def report(name, expect, status, out):
    good = (status in expect)
    print(f"[{'OK ' if good else 'BAD'}] {name}: expected {'/'.join(expect)}, observed {status}", flush=True)
    for l in out[-3:]:
        print("        " + l[:200])
    return good


results = []

# T1: move 1e-10 of mass between two support points of the d = 5 certificate
d = fresh("t1")
fn = os.path.join(d, "certificates", "dkz_d5.json")
c = json.load(open(fn))
c["support"][0][1] += 10 ** 6
c["support"][1][1] -= 10 ** 6
json.dump(c, open(fn, "w"))
s, o = run(d, "import verify_theorem as V; V.c8()")
results.append(report("T1 certificate d=5: 1e-10 of mu moved between two atoms", ["FAIL", "ABORT"], s, o))

# T2: claim a larger v1 (0.70 > 2/I_ME(4)) with the same mu, keeping v1 - v0
d = fresh("t2")
fn = os.path.join(d, "certificates", "dkz_d4.json")
c = json.load(open(fn))
v1, v0 = Fr(*c["v1"]), Fr(*c["v0"])
nv1 = Fr(70, 100)
nv0 = nv1 - (v1 - v0)
c["v1"], c["v0"] = [nv1.numerator, nv1.denominator], [nv0.numerator, nv0.denominator]
json.dump(c, open(fn, "w"))
s, o = run(d, "import verify_theorem as V; V.c8()")
results.append(report("T2 certificate d=4: v1, v0 raised above 2/I_ME(4)", ["FAIL", "ABORT"], s, o))

# T3: drop one CGLMP facet from facets223.txt
d = fresh("t3")
fn = os.path.join(d, "facets223.txt")
lines = open(fn).read().splitlines()
k = next(i for i, l in enumerate(lines) if l.strip().endswith("CGLMP"))
del lines[k]
open(fn, "w").write("\n".join(lines) + "\n")
s, o = run(d, "import verify_theorem as V; V.c1()")
results.append(report("T3 facets223.txt with one CGLMP facet removed: C1", ["FAIL", "ABORT"], s, o))
s, o = run(d, "import verify_theorem as V; V.c5()")
results.append(report("T3b same file: C5 alone (expected to still PASS -- C5 trusts the list; C1 guards it)",
                      ["PASS"], s, o))

# T4: replace one lifted-CHSH facet by a valid but non-facet inequality (h0 + 1)
d = fresh("t4")
fn = os.path.join(d, "facets223.txt")
lines = open(fn).read().splitlines()
k = next(i for i, l in enumerate(lines) if l.strip().endswith("CHSH"))
h, cls = lines[k].split(";")
h = [int(t) for t in h.split()]
h[0] += 1
lines[k] = " ".join(map(str, h)) + " ; " + cls.strip()
open(fn, "w").write("\n".join(lines) + "\n")
s, o = run(d, "import verify_theorem as V; V.c1()")
results.append(report("T4 facets223.txt with one facet replaced by a weaker inequality: C1", ["FAIL", "ABORT"], s, o))

# T5: wrong closed form for v_odd in the verifier (4 -> 3 in the denominator)
d = fresh("t5")
fn = os.path.join(d, "verify_theorem.py")
src = open(fn).read()
src = src.replace("vo = sp.simplify((2 - chsh_u) / (chsh_odd - chsh_u) - 4 / ((r2 - 1) * dd + 4))",
                  "vo = sp.simplify((2 - chsh_u) / (chsh_odd - chsh_u) - 4 / ((r2 - 1) * dd + 3))")
open(fn, "w").write(src)
s, o = run(d, "import verify_theorem as V; V.c3()")
results.append(report("T5 wrong v_odd closed form in C3", ["FAIL", "ABORT"], s, o))

# T6: wrong competitor (B_1 = (sz + sx)/sqrt2, i.e. B_0 = B_1): C2 must fail
d = fresh("t6")
fn = os.path.join(d, "verify_theorem.py")
src = open(fn).read()
src = src.replace("B = [(sz + sx) / sp.sqrt(2), (sz - sx) / sp.sqrt(2)]", "B = [(sz + sx) / sp.sqrt(2), (sz + sx) / sp.sqrt(2)]")
open(fn, "w").write(src)
s, o = run(d, "import verify_theorem as V; V.c2()")
results.append(report("T6 wrong competitor observables in C2", ["FAIL", "ABORT"], s, o))

# T7: the Bernstein machinery must reject a behaviour for which coarse-grained CHSH is NOT the optimal witness:
#     q = qutrit 'CGLMP PR box' p(a,b|x,y) = 1/3 [b - a = c_xy mod 3] (CGLMP value 4) -- CGLMP facets must give G_F < 0
d = fresh("t7")
code = r'''
from fractions import Fraction as Fr
import competitor as C
from exact import Poly, certify_nonneg
H, cls = C.load_facets()
hc = C.chsh_facet()
# NS box saturating the BRIEF CGLMP_3 form: links (0,0): a = b; (1,0): b = a + 1; (1,1): a = b; (0,1): b = a  (k = 0 terms)
shift = {(0, 0): 0, (1, 0): 1, (1, 1): 0, (0, 1): 0}
q = C.behaviour_zero()
for (x, y), c in shift.items():
    for a in range(3):
        q[(x, y, a, (a + c) % 3)] = Poly.const(Fr(1, 3))
n = C.noise_behaviour()
Xq, Xn = C.cg(q), C.cg(n)
fcq, fcn = C.facet_value(hc, Xq), C.facet_value(hc, Xn)
bad = 0
for h, c in zip(H, cls):
    G = fcn * C.facet_value(h, Xq) - C.facet_value(h, Xn) * fcq
    if not G.is_zero() and not certify_nonneg(G, 0, Fr(1, 3))[0]:
        bad += 1
print("[FAIL]" if bad else "[PASS]", "facets with G_F not certified >= 0:", bad)
'''
s, o = run(d, code)
results.append(report("T7 CGLMP-PR box: CHSH-based v* must be rejected by some facet", ["FAIL"], s, o))

# T8: certify_nonneg must reject a polynomial that dips below 0 inside [0, 1/3]
d = fresh("t8")
code = r'''
from fractions import Fraction as Fr
from exact import Poly, certify_nonneg
t = Poly.t()
p = (t - Fr(1, 6)) * (t - Fr(1, 6)) - Fr(1, 10 ** 9)
q = (t - Fr(1, 6)) * (t - Fr(1, 6))
print("[FAIL]" if not certify_nonneg(p, 0, Fr(1, 3))[0] else "[PASS]", "dip polynomial certified:", certify_nonneg(p, 0, Fr(1, 3)))
print("touching polynomial (t-1/6)^2 certified:", certify_nonneg(q, 0, Fr(1, 3)))
'''
s, o = run(d, code)
results.append(report("T8 certify_nonneg on (t-1/6)^2 - 1e-9 (must not certify)", ["FAIL"], s, o))

# T9: wrong 1/2-lemma model (P2 uses p01 twice) must fail C6
d = fresh("t9")
fn = os.path.join(d, "verify_theorem.py")
src = open(fn).read()
src = src.replace("p[(0, 1)][a0][b1] * p[(1, 0)][a1][b0]) / 2", "p[(0, 1)][a0][b1] * p[(0, 1)][a1][b0]) / 2")
open(fn, "w").write(src)
s, o = run(d, "import verify_theorem as V; V.c6()")
results.append(report("T9 broken 1/2-lemma construction in C6", ["FAIL", "ABORT"], s, o))

# T10: wrong comparison claim: r(9) = 0.5 (still >= v_comp?) -> replace by r(9) = 0.51 < v_comp(9) = 0.5176
d = fresh("t10")
fn = os.path.join(d, "verify_theorem.py")
src = open(fn).read()
src = src.replace("9: Fr(681, 1000)}", "9: Fr(51, 100)}")
open(fn, "w").write(src)
s, o = run(d, "import verify_theorem as V; import dkz_cert; v0s = {dd: dkz_cert.check(dd, verbose=False)[1] for dd in range(4, 10)}; V.c9(v0s)")
results.append(report("T10 false comparison r(9) = 0.51 < v_comp(9) in C9", ["FAIL", "ABORT"], s, o))

print(f"{sum(results)}/{len(results)} tamper tests behaved as expected")
