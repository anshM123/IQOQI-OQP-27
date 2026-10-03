"""Audit of CONE_d for EVERY d >= 2 (single run).
 d >= 2001 (CONE_ALLD_PROOF.md, RIGOR_ALLD.md): reads logs/alld/*.json (exact rational strings written by a06-a14, t35, test_exact)
   and checks, with EXACT rational comparisons or interval arithmetic (no float decisions, no tolerances, no hard-coded analytic
   constants): coverage + margins of the outer (Q_O) and inner (Lambda(R2)) D_B certificates and of the slack certificates (zone
   bookkeeping: every stencil of every m lies in a certified zone, every zone file covers eps up to 1/2001, inner x-ranges), A_2 >= 0,
   m = 1, 2, the pointwise lemma (and that its boxes cover the whole model domain, which certifies the uniqueness of the model root),
   the F_A tail term, Lemma P (A_min from t35), the slack perturbation (constants of a13), the identities (a14), the G6 tests, and
   the tail / fixed-point margins for every d >= 2001 (monotone in d, RIGOR_ALLD.md s.8).
 2 <= d <= 200: the LP certificates certs/cert_d{d}.json (exact structural checks + the matching VERIFIED record of verify_cone.verify
   in logs/verify_*.log); with --reverify-lp [NPROC] every certificate is re-verified by verify_cone.verify (lp_reverify.py).
 201 <= d <= 2000: calls audit_cert_g.py (unchanged; unified certificates logs/cert_g_d{d}.json of verify_cert.py).
Prints ALL-D CERTIFIED (every d >= 2) or the failing items.  Usage: python audit_alld.py [--reverify-lp [NPROC]]"""
import json, os, glob, math
from fractions import Fraction as Fr
import mpmath
from mpmath import iv
iv.prec = 200

L = 'logs/alld/'
fails = []
notes = []


def load(f):
    p = L + f
    if not os.path.exists(p):
        fails.append(f'missing {f}')
        return None
    return json.load(open(p))


def Q(s):
    return Fr(s)


def ivQ(q):
    q = Fr(q)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


E1 = Fr(1, 2001)


def cover(intervals, lo, hi, name):
    """exact: the union of the closed intervals contains [lo, hi]."""
    cur = Fr(lo)
    for a, b in sorted(intervals):
        if a > cur:
            fails.append(f'{name}: gap [{float(cur)}, {float(a)}]')
            return False
        cur = max(cur, b)
        if cur >= hi:
            return True
    fails.append(f'{name}: covered only up to {float(cur)} < {float(hi)}')
    return False


def zone(files, kind):
    """returns (list of (lo, hi, qlo) Fractions, XA or None, min eps_hi)"""
    out, xa = [], None
    for f in files:
        r = load(f)
        if not r:
            continue
        if not r.get('complete') or len(r['boxes']) != r['nb']:
            fails.append(f'{f}: incomplete')
        if Q(r['eps_hi']) < E1:
            fails.append(f'{f}: eps range below 1/2001')
        if 'XA' in r:
            xa = Q(r['XA']) if xa is None else min(xa, Q(r['XA']))
        for b in r['boxes']:
            lo_, hi_ = Q(b.get('xlo', b.get('lo'))), Q(b.get('xhi', b.get('hi')))
            out.append((lo_, hi_, Q(b['qlo'])))
            # inner boxes: the certified x-range [0, x1] must reach min(XA, E1 b_hi) (b-boxes) resp. min(XA, E1/w_lo) (w-boxes)
            if kind in ('Ib', 'Sb', 'Iw', 'Sw'):
                if b.get('x1') is None:
                    fails.append(f'{f}: x-range not recorded')
                else:
                    need = min(Q(r['XA']), E1 * hi_) if kind in ('Ib', 'Sb') else (Q(r['XA']) if lo_ == 0 else min(Q(r['XA']), E1 / lo_))
                    if Q(b['x1']) < need:
                        fails.append(f'{f}: x-range of box [{float(lo_)}, {float(hi_)}] too small')
    return out, xa


# ------------------------------------------------------------------ zone bookkeeping constants
XO = Fr(11, 1000)          # outer zones start here (D_B and slack)
XE = Fr(501, 1000)         # outer zones end here
# every stencil: D_B uses b in [m-2, m+2] (m >= 3 in zones), slack [m-1, m+1] (m >= 2 in zones); x = eps b, m <= d/2, d >= 2001
# ---- outer D_B zone: x in [0.011, 0.501]
outer, _ = zone(['zoneO_0a1.json', 'zoneO_0a2.json', 'zoneO_0b1.json', 'zoneO_0b2.json', 'zoneO_1.json', 'zoneO_2.json',
                 'zoneO_3a.json', 'zoneO_3b.json', 'zoneO_3c.json'], 'O')
cover([(a, b) for a, b, q in outer], XO, XE, 'outer D_B')
qO = min(q for a, b, q in outer) if outer else Fr(-1)
# ---- inner D_B zone: b in [1, 20] and w in [0, 0.05], x <= XA
inner_b, xa1 = zone(['zoneI_b1.json', 'zoneI_b2.json', 'zoneI_b3.json'], 'Ib')
inner_w, xa2 = zone(['zoneI_w1.json', 'zoneI_w2.json', 'zoneI_w3.json'], 'Iw')
cover([(a, b) for a, b, q in inner_b], 1, 20, 'inner D_B (b)')
cover([(a, b) for a, b, q in inner_w], 0, Fr(1, 20), 'inner D_B (w)')
XA = min(x for x in (xa1, xa2) if x is not None) if (xa1 or xa2) else Fr(0)
qI = min(q for a, b, q in inner_b + inner_w) if inner_b + inner_w else Fr(-1)
# overlap: if (m+2) eps > XA then (m-2) eps > XA - 4 eps >= XA - 4/2001 >= XO; top stencil (d/2 + 2) eps <= 1/2 + 2/2001 <= XE
if not (XA - 4 * E1 >= XO and Fr(1, 2) + 2 * E1 <= XE):
    fails.append('D_B zone bookkeeping (overlap / top)')
print(f"D_B zones: outer [0.011, 0.501] min Q_O >= {float(qO):.6f};  inner (x <= {float(XA):.4f}, b >= 1) min Lambda(R2) >= {float(qI):.6f}")

# ---- slack zones: outer x in [0.011, 0.501], inner b in [1, 20], w in [0, 0.05], m = 1
sl_o, _ = zone(['slackW_O0a.json', 'slackW_O0b.json', 'slackW_O1a.json', 'slackW_O1b.json'], 'SO')
sl_b, xs1 = zone(['slackW_I1.json', 'slackW_I2a.json', 'slackW_I2b.json'], 'Sb')
sl_w, xs2 = zone(['slackW_I3.json'], 'Sw')
cover([(a, b) for a, b, q in sl_o], XO, XE, 'slack outer')
cover([(a, b) for a, b, q in sl_b], 1, 20, 'slack inner (b)')
cover([(a, b) for a, b, q in sl_w], 0, Fr(1, 20), 'slack inner (w)')
XAs = min(x for x in (xs1, xs2) if x is not None) if (xs1 or xs2) else Fr(0)
if not (XAs - 2 * E1 >= XO and Fr(1, 2) + E1 <= XE):
    fails.append('slack zone bookkeeping')
m1 = load('slack_m1.json')
if m1 and Q(m1['eps_hi']) < E1:
    fails.append('slack_m1: eps range')
smin = min([q for a, b, q in sl_o + sl_b + sl_w] + ([Q(m1['m1_lo'])] if m1 else [])) if (sl_o and sl_b and sl_w) else Fr(-1)
print(f"slack: min density (Delta^2 W_e / eps) >= {float(smin):.6f}")

# ---- A_2, small m, pointwise, constants, QD2-L12, identities, G6 tests
a2 = load('A2.json')
if not (a2 and a2['ok'] and a2['A2pos'] and a2['part2']):
    fails.append('A_2 certificate')
sm = load('smallm.json')
if not (sm and sm['ok'] and Q(sm['eps_hi']) >= E1):
    fails.append('small-m certificate')
gamma = -Q(sm['DB1_lo']) if sm else Fr(10)           # D_B(1) >= -gamma eps^2
DB2 = Q(sm['DB2_lo']) if sm else Fr(-1)               # D_B(2) >= DB2 eps^3
pw = load('pointwise.json')
if not (pw and pw['ok'] and Q(pw['eps_hi']) >= E1):
    fails.append('pointwise lemma')
dmax = Q(pw['dmax_rel']) if pw else Fr(1)             # |Phi_* - Phi_e| <= dmax eps^2 for 1 <= m < d/2
# uniqueness domain {(x, eps): 0 <= eps <= 1/2001, x = eps b, b >= 1, x <= 0.501}: b-boxes cover b in [1, 30] (x <= E1 b_hi),
# w-boxes w in [0, 1/30] with x in [0, 0.015], x-boxes x in [0.015, 0.501]; every box ok (unique root, Fp > 0)
if pw:
    bx = [b for b in pw['boxes']]
    if not all(b['ok'] and b['uniq'] for b in bx):
        fails.append('pointwise boxes not all ok')
    bb = [(Q(b['lo']), Q(b['hi'])) for b in bx if b['kind'] == 'b']
    ww = [(Q(b['wr'][0]), Q(b['wr'][1])) for b in bx if b['kind'] == 'w']
    xx = [(Q(b['xr'][0]), Q(b['xr'][1])) for b in bx if b['kind'] in ('x', 'x*')]
    cover(bb, 1, 30, 'uniqueness: b-boxes')
    cover(ww, 0, Fr(1, 30), 'uniqueness: w-boxes')
    cover(xx, Fr(15, 1000), XE, 'uniqueness: x-boxes')
    if not all(Q(b['xr'][1]) >= Fr(15, 1000) and Q(b['xr'][0]) <= 0 for b in bx if b['kind'] == 'w'):
        fails.append('uniqueness: w-box x-range')
    if not all(Q(b['xr'][1]) >= E1 * Q(b['hi']) and Q(b['xr'][0]) <= 0 for b in bx if b['kind'] == 'b'):
        fails.append('uniqueness: b-box x-range')
    if not all(Q(b['wr'][0]) <= 1 / Q(b['hi']) and Q(b['wr'][1]) >= 1 / Q(b['lo']) for b in bx if b['kind'] == 'b'):
        fails.append('uniqueness: b-box w-range')
    if not all(Q(b['wr'][0]) <= 0 and Q(b['wr'][1]) >= E1 / Q(b['xr'][0]) for b in bx if b['kind'] in ('x', 'x*')):
        fails.append('uniqueness: x-box w-range')
    if not all(Q(b['er'][0]) <= 0 and Q(b['er'][1]) >= E1 for b in bx):
        fails.append('uniqueness: eps range')
co = load('constants.json')
if not co or Q(co['eps_hi']) < E1:
    fails.append('constants')
GG4, DTG4, Dd, TFA, SG1 = (Q(co['GG4']), Q(co['DTG4']), Q(co['Dd']), Q(co['TFA_eps3']), Q(co['SG1'])) if co else (Fr(10 ** 6),) * 5
pol = load('polya.json')
if not (pol and pol['ok']):
    fails.append('QD2-L12 (t35_polya)')
Amin = Q(pol['Amin']) if pol else Fr(0)
TAILC = Q(pol['tailc']) if pol else Fr(1)
idn = load('identities.json')
if not (idn and idn.get('all_ok') and idn['S']['ok'] and idn['N']['ok'] and idn['J']['ok']):
    fails.append('identities I1/I2/W0 (a14)')
txt = open(L + 'test_exact.log').read() if os.path.exists(L + 'test_exact.log') else ''
if 'TEST_EXACT: PASS' not in txt:
    fails.append('G6 tests (test_exact.py)')
print(f"m = 1, 2: D_B(1) >= -{float(gamma):.6f} eps^2, D_B(2) >= {float(DB2):.3f} eps^3;  pointwise |Phi_* - Phi_e| <= {float(dmax):.4e} eps^2")
print(f"constants (a13): |G - G_4| <= {float(GG4):.4f} eps^3, |d_t G_4| <= {float(DTG4):.4f} d, Dd = {float(Dd):.4f}, F_A tail <= {float(TFA):.3e} eps^3;"
      f"  A_min >= {float(Amin):.12f} (t35)")

# ------------------------------------------------------------------ Lemma P (worst case d = 2001: every term improves with d)
beta = min(qO - TFA, qI - TFA, DB2)                     # D_B(m) >= beta eps^3, 2 <= m <= d/2
A0 = iv.pi / 2 - 1
d = 2001
P = 16 * A0 * (ivQ(Amin) - 2 * ivQ(TAILC) / (d - 1))
atk = (P - 4 * ivQ(gamma) ** 2 / (ivQ(beta) * (d - 4))) / 8 - 2 * ivQ(dmax)
print(f"Lemma P: gamma = {float(gamma):.6f}, beta = {float(beta):.6f}, P >= {float(P.a):.9f};  at_k >= w_k eps^2 * {float(atk.a):.7f}")
if not (beta > 0 and atk.a > 0):
    fails.append('Lemma P margin')

# ------------------------------------------------------------------ slack perturbation (a13 constants)
pert = 4 * (ivQ(DTG4) * ivQ(dmax) + ivQ(GG4) * ivQ(E1) ** 2 + ivQ(Dd) * ivQ(E1) ** 3 / 8)
slack = ivQ(smin) - pert
print(f"slack: Delta^2 W / eps >= {float(smin):.6f} - {float(pert.b):.6f} = {float(slack.a):.6f}")
if not slack.a > 0:
    fails.append('slack after perturbation')

# ------------------------------------------------------------------ tail lemma + fixed point (Lemma B) for every d >= 2001
# Phi(1) <= eps phi1c on the Poincare-Miranda box (u_e(1) <= u_max_b1, |Phi - Phi_e| <= dmax eps^2 + rho, rho <= 1e-6 eps checked);
# log P(E^c) <= log(2d) - 9 d/(32 phi1c);  eps_t <= (3d/8) F1(d) P(E^c),  F1(d) = (4d/pi)(log d + 2) + d SG1 (SG1 <= 1.9);
# c = inf Hc_m' >= (4/pi) Fp_min/d (a12);  rho = 2 eps_t/c.  Each margin below is (const) - p log d - log log-terms + (9/(32 phi1c)) d
# with derivative >= 9/(32 phi1c) - 8/d > 0 for d >= 2001; so d = 2001 is the worst case (RIGOR_ALLD.md s.8).
fpa = load('fp_alld.json')
if not (fpa and fpa['ok'] and Q(fpa['eps_hi']) >= E1):
    fails.append('fixed-point derivative bound (d >= 2001)')
fpmin = Q(fpa['fpmin']) if fpa else Fr(0)
u1 = Q(pw['u_max_b1']) if pw else Fr(1)
phi1c = ivQ(u1) + ivQ(dmax) * ivQ(E1) + iv.mpf(10) ** -6
D = iv.mpf(d)
assert (iv.mpf(8) / D).b < (9 / (32 * phi1c)).a
logPEc = iv.log(2 * D) - 9 * D / (32 * phi1c)
F1 = 4 * D / iv.pi * (iv.log(D) + 2) + D * ivQ(SG1)            # sup |F'| on (0, d) (H_d <= log d + 1)
log_et = iv.log(3 * D / 8) + iv.log(F1) + logPEc
c_low = 4 / iv.pi * ivQ(fpmin) / D
log_rho = iv.log(2 / c_low) + log_et
# margins (Lemma B / Lemma R1): at_k margin absorbs 2 rho; slack margin absorbs 4 (eps_t + rho sup|d_t H|), sup|d_t H| <= d^2;
# rho <= 1e-6 eps (used in phi1c)
mg_at = iv.log(atk.a) - 2 * iv.log(D) - (iv.log(2) + log_rho)
mg_sl = iv.log(slack.a) - iv.log(D) - (iv.log(4) + iv.log(iv.exp(log_et) + iv.exp(log_rho) * D ** 2))
mg_rho = iv.log(iv.mpf(10) ** -6 / D) - log_rho
print(f"tail lemma (d = 2001, decreasing in d): log P(E^c) <= {float(logPEc.b):.2f}, log eps_t <= {float(log_et.b):.2f};"
      f"  fixed point: Fp_min >= {float(fpmin):.5f}, Hc' >= {float(c_low.a):.4e}, log rho <= {float(log_rho.b):.2f}")
print(f"   log-margins (> 0 needed): at_k vs 2 rho {float(mg_at.a):.1f}, slack vs 4(eps_t + rho d^2) {float(mg_sl.a):.1f}, rho vs 1e-6 eps {float(mg_rho.a):.1f}")
if not (fpmin > 0 and mg_at.a > 0 and mg_sl.a > 0 and mg_rho.a > 0 and log_et.b < -300):
    fails.append('tail / fixed-point margins (d >= 2001)')

ok_alld = not fails
print("d >= 2001:", "CERTIFIED" if ok_alld else f"INCOMPLETE {fails}")

# ------------------------------------------------------------------ 2 <= d <= 200: LP certificates (QD2-T1; read only)
# certs/cert_d{d}.json: exact structural checks (q = 16, every cell a list of d integers >= 1 with sum 16 d, one weight > 0 per cell,
# certified minimum weight > 0 in the note), and the verification record of verify_cone.verify (160-bit interval arithmetic) in
# logs/verify_*.log: a line 'd=<d>: attempt k: ... support K  VERIFIED True  <note>' with K = number of cells and the same note.
# Optional full re-verification:  python audit_alld.py --reverify-lp [NPROC]  (re-runs verify_cone.verify on every stored certificate).
import re, sys, subprocess
lp_fail = []
vlines = {}
for f in sorted(glob.glob('logs/verify_*.log')):
    for line in open(f, encoding='utf-8', errors='replace'):
        mt = re.match(r'd=(\d+): attempt \d+: ncols \d+ support (\d+)\s+VERIFIED True\s+(.*?)\s+\[\d+s\]\s*$', line)
        if mt:
            vlines.setdefault(int(mt.group(1)), []).append((int(mt.group(2)), mt.group(3)))
lp_min = None
for dd in range(2, 201):
    fn = f'certs/cert_d{dd}.json'
    if not os.path.exists(fn):
        lp_fail.append((dd, 'missing')); continue
    c = json.load(open(fn))
    cells, lam = c.get('cells', []), c.get('lam', [])
    okc = (c.get('d') == dd and c.get('q') == 16 and len(cells) == len(lam) and len(cells) >= dd - 1
           and all(len(n) == dd and all(isinstance(x, int) and x >= 1 for x in n) and sum(n) == 16 * dd for n in cells)
           and all(isinstance(x, (int, float)) and x > 0 for x in lam))
    mn = re.match(r'min certified lambda >= ([0-9.eE+-]+)', c.get('note', ''))
    if not okc or not mn or not Fr(mn.group(1)) > 0:
        lp_fail.append((dd, 'structure')); continue
    if not any(K == len(cells) and note == c['note'] for (K, note) in vlines.get(dd, [])):
        lp_fail.append((dd, 'no matching VERIFIED True record')); continue
    v = Fr(mn.group(1)) * dd
    lp_min = v if lp_min is None or v < lp_min else lp_min
if '--reverify-lp' in sys.argv:
    k = sys.argv.index('--reverify-lp')
    nproc = int(sys.argv[k + 1]) if len(sys.argv) > k + 1 else 8
    chunks = [[str(dd) for dd in range(2 + i, 201, nproc)] for i in range(nproc)]     # interleaved: balanced cost
    procs = [subprocess.Popen([sys.executable, 'lp_reverify.py'] + ch, stdout=subprocess.PIPE, text=True) for ch in chunks]
    seen = set()
    for p in procs:
        for line in p.communicate()[0].splitlines():
            parts = line.split(' ', 3)
            if len(parts) >= 3 and parts[0] == 'LPCHECK':
                seen.add(int(parts[1]))
                if parts[2] != 'True':
                    lp_fail.append((int(parts[1]), 'reverify: ' + (parts[3] if len(parts) > 3 else '')))
    lp_fail += [(dd, 'reverify: no result') for dd in range(2, 201) if dd not in seen]
    print(f"LP certificates re-verified with verify_cone.verify (160-bit intervals, {len(seen)} values of d): "
          f"failures {[x for x in lp_fail if str(x[1]).startswith('reverify')]}")
print(f"2 <= d <= 200 (LP certificates, QD2-T1): {199 - len(lp_fail)}/199 valid with a matching VERIFIED record"
      + (f"; min d * certified weight = {float(lp_min):.4f}" if lp_min else '') + (f"; FAIL {lp_fail[:5]}" if lp_fail else ''))
if lp_fail:
    fails.append(f'LP certificates: {len(lp_fail)} failing, first {lp_fail[:3]}')

# ------------------------------------------------------------------ 201 <= d <= 2000: unified certificates logs/cert_g_d{d}.json
# audited by audit_cert_g.py (owned by that regime; called unchanged): every condition of Lemma B and Lemma R1 (ii) re-checked
# from the exact decimal strings, code hash of verify_cert.py.
pr = subprocess.run([sys.executable, 'audit_cert_g.py', '201', '2000'], capture_output=True, text=True)
out = pr.stdout.strip().splitlines()
for line in out:
    if line.startswith(('verify_cert.py sha256', 'certificates 201..2000', 'margins', '  (D)', '  tails')):
        print('   [audit_cert_g] ' + line)
ok_g = pr.returncode == 0 and bool(out) and out[-1].strip() == 'ALL CERTIFIED' and any(
    l.startswith('certificates 201..2000: 1800/1800 OK') for l in out)
print("201 <= d <= 2000 (cert_g, audit_cert_g.py):", "ALL CERTIFIED" if ok_g else "INCOMPLETE")
if not ok_g:
    fails.append('201..2000: audit_cert_g.py did not report 1800/1800 ALL CERTIFIED')

print("FAILS:", fails if fails else "none")
print("ALL-D CERTIFIED (every d >= 2)" if not fails else "INCOMPLETE")
