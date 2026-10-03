"""Audit of the unified Gaussian-regime certificates logs/cert_g_d{d}.json (201 <= d <= 2000), written by verify_cert.py.

For every d the audit reads the exact decimal strings (Fraction, no floats), turns them into mpmath intervals with outward rounding,
recomputes the tail bound from the stored box, and checks every condition of Lemma B (CONE_PROOF.md) and of Lemma R1 (ii) by interval
comparisons; tiny quantities are compared through logarithms (no underflow anywhere):
  code      code == verify_cert.py, code_sha256 == SHA-256 of the current verify_cert.py, iv_prec == 160, the certifier's verdict ok;
  box       r = 2^r_log2 exactly; lo_1 <= a_1 - r, hi_1 >= b_1 + r, a_1 <= b_1 (exact rationals); min_m lo_m > 0;
  tails     log P(E^c) <= log(2d) - 9/(32 hi_1) and log eps_t <= log(3d/8) + log(sup|F'|) + log P(E^c), recomputed here
            (sup|F'| = max(stored, (4d/pi)(H_d + 1) + d S_1 recomputed));  S_1, S_16 <= 8 and identical in all files;
  (B1)      min_k at_k > 0 on the box;
  (B3)      sign changes: max_m [Hc_m(a_m) - tau_m] < 0 < min_m [Hc_m(b_m) - tau_m];
  (D)       c_D > 0 and log c_D + log r > log 2 + log eps_t   (=> (B3) on the widened box);
  (B3')     directly on the faces: max_m [Hc_m(lo_m) - tau_m] < -2 eps_t and min_m [Hc_m(hi_m) - tau_m] > 2 eps_t;
  (ii)      min Delta^2 W > 4 eps_t on the box.
It also prints the minimum margins and a comparison with the previous logs logs/vg_d{d}.json, logs/fp_d{d}.json (read only; display).
Usage: python audit_cert_g.py [d0 d1]
"""
import sys
import os
import json
import hashlib
from fractions import Fraction

import mpmath
from mpmath import iv, mp
from mpmath.libmp import mpf_lt, mpf_gt, fzero

HERE = os.path.dirname(os.path.abspath(__file__))
iv.prec = 200
mp.prec = 200
d0, d1 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (201, 2000)


def LO(x):
    return x._mpi_[0]


def HI(x):
    return x._mpi_[1]


def pos(x):
    """certified x > 0 (every element)."""
    return mpf_gt(LO(x), fzero)


def neg(x):
    return mpf_lt(HI(x), fzero)


def ivq(s):
    """enclosure of the exact decimal string / rational s."""
    q = Fraction(s)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def widen(x):
    e = HI(abs(x) * iv.ldexp(iv.mpf(1), -190))
    return x + iv.make_mpf((mpmath.libmp.mpf_neg(e), e))


def ilog(x):
    return widen(iv.log(x))


PI = widen(+iv.pi)
LN2, LN4 = ilog(iv.mpf(2)), ilog(iv.mpf(4))
LN10 = ilog(iv.mpf(10))
code_path = os.path.join(HERE, 'verify_cert.py')
CODE_SHA = hashlib.sha256(open(code_path, 'rb').read()).hexdigest()

Hd = {}
acc = iv.mpf(0)
for n in range(1, d1 + 1):
    acc += 1 / iv.mpf(n)
    Hd[n] = acc


def f2(x):
    return float(mp.make_mpf(x))


bad, missing = [], []
consts = {}
M = dict(at_even=None, at_odd=None, slack=None, ratio=None, D=None, faces=None, sl_eps=None, eps=None, secs=0.0)
argM = {}
CMP = {}                                                                # (label) -> lists of new/old - 1 (display)
OLDMIN = {}
fallbacks = 0


def upd(key, val, d, smaller=True):
    if M[key] is None or (val < M[key] if smaller else val > M[key]):
        M[key] = val
        argM[key] = d


for d in range(d0, d1 + 1):
    fn = os.path.join(HERE, 'logs', f'cert_g_d{d}.json')
    if not os.path.exists(fn):
        missing.append(d)
        continue
    try:
        r = json.load(open(fn))
        B = r['bounds']
        fails = []
        if r.get('d') != d or r.get('code') != 'verify_cert.py':
            fails.append('identity')
        if r.get('code_sha256') != CODE_SHA:
            fails.append('code hash')
        if r.get('iv_prec') != 160:
            fails.append('precision')
        if r.get('ok') is not True or not all(r['checks'].values()):
            fails.append('certifier verdict')
        # ---- box
        R = Fraction(B['r'])
        if R != Fraction(2) ** int(B['r_log2']):
            fails.append('r')
        a1, b1 = Fraction(B['phi1_root'][0]), Fraction(B['phi1_root'][1])
        lo1, hi1 = Fraction(B['phi1_box'][0]), Fraction(B['phi1_box'][1])
        if not (lo1 <= a1 - R and hi1 >= b1 + R and a1 <= b1):
            fails.append('widened box')
        if not Fraction(B['box_lo_min']) > 0:
            fails.append('box positivity')
        # ---- constants
        for key in ('S1_hi', 'S16_hi', 'tail_gr1_hi'):
            consts.setdefault(key, B[key])
            if consts[key] != B[key]:
                fails.append('constant ' + key)
        if not (Fraction(B['S1_hi']) <= 8 and Fraction(B['S16_hi']) <= 8):
            fails.append('S_k <= 8')
        # ---- tails, recomputed from the stored box
        D = iv.mpf(d)
        supF1 = (4 * D / PI) * (Hd[d] + 1) + D * ivq(B['S1_hi'])
        supF1 = iv.make_mpf((HI(supF1), HI(supF1)))
        if Fraction(B['supF1_hi']) > 0 and mpf_gt(HI(ivq(B['supF1_hi'])), HI(supF1)):
            supF1 = iv.make_mpf((HI(ivq(B['supF1_hi'])), HI(ivq(B['supF1_hi']))))
        logP = ilog(2 * D) - 9 / (32 * ivq(B['phi1_box'][1]))
        logE = ilog(3 * D / 8) + ilog(supF1) + logP
        stored = HI(ivq(B['log_eps_tail_hi']))
        top = HI(logE) if mpf_gt(HI(logE), stored) else stored           # the larger of the two upper bounds of log eps_t
        logE = iv.make_mpf((top, top))
        # ---- (B1)
        at = ivq(B['at_min_lo'])
        if not pos(at):
            fails.append('B1')
        # ---- (B3) sign changes
        if not (neg(ivq(B['signchange_left_max_hi'])) and pos(ivq(B['signchange_right_min_lo']))):
            fails.append('sign change')
        # ---- (D)
        cD = ivq(B['D_cD_lo'])
        mD = None
        if pos(cD):
            mD = ilog(cD) + ilog(ivq(B['r'])) - LN2 - logE
            if not pos(mD):
                fails.append('(D) c_D r > 2 eps_t')
        else:
            fails.append('(D) c_D > 0')
        # ---- (B3') faces
        fl, fr = ivq(B['face_left_max_hi']), ivq(B['face_right_min_lo'])
        mF = None
        if neg(fl) and pos(fr):
            mF = min(LO(ilog(-fl) - LN2 - logE), LO(ilog(fr) - LN2 - logE), key=lambda v: mp.make_mpf(v))
            if not mpf_gt(mF, fzero):
                fails.append('faces vs 2 eps_t')
        else:
            fails.append('faces sign')
        # ---- (ii)
        sl = ivq(B['slack_min_lo'])
        mS = None
        if pos(sl):
            mS = ilog(sl) - LN4 - logE
            if not pos(mS):
                fails.append('slack > 4 eps_t')
        else:
            fails.append('slack > 0')
        if fails:
            bad.append((d, fails))
            continue
        # ---- margins (display)
        d2at = mp.make_mpf(LO(at)) * d * d
        upd('at_even' if d % 2 == 0 else 'at_odd', d2at, d)
        upd('slack', mp.make_mpf(LO(sl)) * d, d)
        ratio = mp.make_mpf(LO(cD)) / (mp.make_mpf(LO(ivq(B['c1min_lo']))) / 4)
        upd('ratio', ratio, d)
        upd('D', mp.make_mpf(LO(mD)) / mp.make_mpf(LO(LN10)), d)
        upd('faces', mp.make_mpf(mF) / mp.make_mpf(LO(LN10)), d)
        upd('sl_eps', mp.make_mpf(LO(mS)) / mp.make_mpf(LO(LN10)), d)
        upd('eps', mp.make_mpf(HI(logE)) / mp.make_mpf(LO(LN10)), d, smaller=False)
        M['secs'] += float(r.get('secs', 0))
        fallbacks += r['stats']['trunc_fallback'] + r['stats']['mj_fallback']
        # ---- previous logs (display only): current vg/fp logs, and the superseded 100-bit runs in logs/backup_prec100
        for tag, sub in (('vg/fp', ''), ('100-bit backup', 'backup_prec100')):
            fv = os.path.join(HERE, 'logs', sub, f'vg_d{d}.json')
            ff = os.path.join(HERE, 'logs', sub, f'fp_d{d}.json')
            if not (os.path.exists(fv) and os.path.exists(ff)):
                continue
            v, fp = json.load(open(fv)), json.load(open(ff))
            label = f"{tag} {'201-600' if d <= 600 else '601-2000'}"
            c = CMP.setdefault(label, dict(at=[], sl=[], ratio=[]))
            c['at'].append(f2(LO(at)) / v['min_at'] - 1)
            c['sl'].append(f2(LO(sl)) / v['wmin'] - 1)
            c['ratio'].append(float(ratio) / fp['ratio_min'] - 1)
            o = OLDMIN.setdefault(tag, dict(at_even=9.9, at_odd=9.9, sl=9.9, ratio=9.9))
            k = 'at_even' if d % 2 == 0 else 'at_odd'
            o[k] = min(o[k], v['min_at'] * d * d)
            o['sl'] = min(o['sl'], v['wmin'] * d)
            o['ratio'] = min(o['ratio'], fp['ratio_min'])
    except Exception as ex:                                              # malformed file
        bad.append((d, [f'exception {ex!r}']))

n_tot = d1 - d0 + 1
n_ok = n_tot - len(bad) - len(missing)
print(f"verify_cert.py sha256 = {CODE_SHA}")
print(f"certificates {d0}..{d1}: {n_ok}/{n_tot} OK; missing {len(missing)} {missing[:20]}{'...' if len(missing) > 20 else ''}; "
      f"failed {len(bad)} {bad[:10]}")
if n_ok:
    s = lambda k: mpmath.nstr(M[k], 6)                                  # noqa: E731
    print(f"margins (lower endpoints; argmin d):  d^2 min at_k = {s('at_even')} (even d, d = {argM['at_even']}), "
          f"{s('at_odd')} (odd d, d = {argM['at_odd']});  d min Delta^2 W = {s('slack')} (d = {argM['slack']})")
    print(f"  (D): min inf Hc'/(c1min/4) = {s('ratio')} (d = {argM['ratio']});  min log10[c_D r/(2 eps_t)] = {s('D')} "
          f"(d = {argM['D']});  min log10[|face value|/(2 eps_t)] = {s('faces')} (d = {argM['faces']})")
    print(f"  tails: max log10 eps_t = {s('eps')} (d = {argM['eps']});  min log10[min Delta^2 W/(4 eps_t)] = {s('sl_eps')} "
          f"(d = {argM['sl_eps']});  truncation-moment fallbacks used: {fallbacks}")
    print(f"  constants: S_1 <= {consts['S1_hi'][:12]}, S_16 <= {consts['S16_hi'][:12]}, g_r(1) tail <= "
          f"{mpmath.nstr(mp.mpf(Fraction(consts['tail_gr1_hi']).numerator) / Fraction(consts['tail_gr1_hi']).denominator, 4)}")
    print(f"  total certifier time {M['secs'] / 3600:.2f} h")
    for tag, o in OLDMIN.items():
        print(f"previous logs [{tag}]: min d^2 at_k = {o['at_even']:.4f} (even) / {o['at_odd']:.4f} (odd), min d w = {o['sl']:.4f}, "
              f"min (D) ratio = {o['ratio']:.4f}")
    for label, c in sorted(CMP.items()):
        rng = lambda xs: f"[{min(xs):+.2e}, {max(xs):+.2e}]"                # noqa: E731
        print(f"  new/old - 1 vs {label} ({len(c['at'])} d): min at_k {rng(c['at'])}, min Delta^2 W {rng(c['sl'])}, "
              f"(D) ratio {rng(c['ratio'])}")
print("ALL CERTIFIED" if n_ok == n_tot else "INCOMPLETE")
