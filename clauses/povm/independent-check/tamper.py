"""
tamper.py -- tamper tests: every modified certificate must be REJECTED by both checkers
(P1 verify_povm.py and the referee's ref_verify.py).  Modified pickles are written to REF_povm/tamper/.
usage: python tamper.py d
"""
import sys
import os
import copy
import pickle
import io
import contextlib
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
P1 = os.path.join(HERE, "..", "P1_povm_numerics")
sys.path.insert(0, P1)
import verify_povm as THEIRS          # noqa: E402  (their checker, used only as a black box)
import ref_verify as MINE              # noqa: E402


def add_rational(x, q_num, q_den):
    """x = (a, den) in power basis; add the rational q_num/q_den to the constant coefficient"""
    a, den = x
    a = list(a)
    # a/den + q_num/q_den = (a*q_den + q_num*den)/(den*q_den)
    a = [t * q_den for t in a]
    a[0] += q_num * den
    return (tuple(a), den * q_den)


def run_theirs(d, path, mode_iv=False):
    THEIRS.INTERVAL_CHOLESKY = mode_iv
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            THEIRS.verify(d, path)
        return "ACCEPTED"
    except AssertionError as e:
        return "rejected (" + (str(e)[:60] or "assert") + ")"
    except Exception as e:
        return "rejected (" + type(e).__name__ + ")"


def run_mine(d, path, pd_only=False):
    cert = pickle.load(open(path, "rb"))
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            log = lambda s: print(s)
            if pd_only:
                MINE.pd_check(d, cert, log)
                return "ACCEPTED"
            R = MINE.Lazy(4 * d)
            orb = MINE.Orbits(d)
            ok1 = MINE.lam_check(d, cert, log)
            ok2, _ = MINE.verify_identity(d, cert, R, orb, log)
            if not (ok1 and ok2):
                return "rejected (lam %s identity %s)" % (ok1, ok2)
            MINE.pd_check(d, cert, log)
            MINE.eq_check(d, cert, log)
        return "ACCEPTED"
    except AssertionError as e:
        return "rejected (" + (str(e)[:60] or "assert") + ")"
    except Exception as e:
        return "rejected (" + type(e).__name__ + ": " + str(e)[:40] + ")"


def main():
    d = int(sys.argv[1])
    src = os.path.join(P1, "certs", f"cert_povm_d{d}.pkl")
    base = pickle.load(open(src, "rb"))
    os.makedirs(os.path.join(HERE, "tamper"), exist_ok=True)
    cases = []

    # T0: untouched copy (must be accepted)
    cases.append(("T0 untouched copy", copy.deepcopy(base)))
    # T1: Hermitian perturbation of one off-diagonal Y entry by 2^-60 (M block 1)
    c = copy.deepcopy(base)
    b = c["keep"][1]
    Y = [list(r) for r in c["Y"][b]]
    Y[0][1] = add_rational(Y[0][1], 1, 2 ** 60)
    Y[1][0] = add_rational(Y[1][0], 1, 2 ** 60)
    c["Y"][b] = Y
    cases.append(("T1 Y[0][1] += 2^-60 (Hermitian kept)", c))
    # T2: diagonal perturbation of a D-block Y entry by 2^-60
    c = copy.deepcopy(base)
    b = [bb for bb in c["keep"] if c["bdata"][bb][0][0] == 'D'][0]
    Y = [list(r) for r in c["Y"][b]]
    Y[2][2] = add_rational(Y[2][2], 1, 2 ** 60)
    c["Y"][b] = Y
    cases.append(("T2 D-block Y[2][2] += 2^-60", c))
    # T3: kernel entry changed
    c = copy.deepcopy(base)
    b = c["keep"][0]
    ker = [list(col) for col in c["kernels"][b]]
    a, den = ker[0][0]
    ker[0][0] = (tuple([a[0] + den] + list(a[1:])), den)
    c["kernels"][b] = ker
    cases.append(("T3 kernel[0][0] += 1", c))
    # T4: lam shifted by 10^-12
    c = copy.deepcopy(base)
    c["lam"] = add_rational(c["lam"], 1, 10 ** 12)
    cases.append(("T4 lam += 1e-12", c))
    # T5: one letter inside an M-block element changed (n -> n+1)
    c = copy.deepcopy(base)
    b = c["keep"][1]
    lab, els, ent = c["bdata"][b]
    els = copy.deepcopy(els)
    cf, w = els[1][0]
    w = list(w)
    g, n = w[0]
    w[0] = (g, n % (d - 1) + 1)
    els[1][0] = (cf, tuple(w))
    c["bdata"][b] = (lab, els, ent)
    cases.append(("T5 letter changed in an M element", c))
    # T6: a D block relabelled to another outcome c
    c = copy.deepcopy(base)
    b = [bb for bb in c["keep"] if c["bdata"][bb][0][0] == 'D'][0]
    lab, els, ent = c["bdata"][b]
    c["bdata"][b] = (('D', 1, (lab[2] + 1) % d), els, ent)
    cases.append(("T6 D block outcome label shifted", c))
    # T7: one block dropped from 'keep'
    c = copy.deepcopy(base)
    c["keep"] = list(c["keep"])[1:]
    cases.append(("T7 first block dropped", c))
    # T8: merging relation smuggled in: a length-2 same-party word replaced by its 'group-law' merge is not
    #      possible in the data format; instead swap the two letters of a two-letter word in an M element
    c = copy.deepcopy(base)
    b = c["keep"][1]
    lab, els, ent = c["bdata"][b]
    els = copy.deepcopy(els)
    for i, el in enumerate(els):
        if any(len(w) == 2 for (_, w) in el):
            k = next(k for k, (_, w) in enumerate(el) if len(w) == 2)
            cf, w = el[k]
            el[k] = (cf, (w[1], w[0]))
            break
    c["bdata"][b] = (lab, els, ent)
    cases.append(("T8 two letters swapped in an M element", c))

    for name, cert in cases:
        path = os.path.join(HERE, "tamper", f"d{d}_" + name.split()[0] + ".pkl")
        pickle.dump(cert, open(path, "wb"))
        r1 = run_theirs(d, path)
        r2 = run_mine(d, path)
        print(f"d={d} {name:45s}  P1 verify_povm: {r1:40s}  referee: {r2}", flush=True)

    # positivity-only tamper: make one block indefinite (Y -> Y - 10*I) and run ONLY the positivity parts
    c = copy.deepcopy(base)
    b = c["keep"][2]
    Y = [list(r) for r in c["Y"][b]]
    for i in range(len(Y)):
        Y[i][i] = add_rational(Y[i][i], -10, 1)
    c["Y"][b] = Y
    path = os.path.join(HERE, "tamper", f"d{d}_T9.pkl")
    pickle.dump(c, open(path, "wb"))
    r2 = run_mine(d, path, pd_only=True)
    # their positivity code is inline after the identity check; run a copy with the identity assertion removed
    harness = os.path.join(HERE, "tamper", "verify_povm_noident.py")
    srcv = open(os.path.join(P1, "verify_povm.py")).read()
    assert srcv.count("    assert not bad\n") == 1
    open(harness, "w").write(srcv.replace("    assert not bad\n", "    pass  # identity assertion removed for the positivity tamper test\n"))
    sys.path.insert(0, os.path.join(HERE, "tamper"))
    import verify_povm_noident as H     # noqa: E402
    res = []
    for iv in (False, True):
        H.INTERVAL_CHOLESKY = iv
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                H.verify(d, path)
            res.append("ACCEPTED")
        except AssertionError as e:
            res.append("rejected (" + str(e)[:50] + ")")
    print(f"d={d} T9 Y_b - 10 I (indefinite), positivity only: P1 exact-LDL: {res[0]};  P1 iv-Cholesky: {res[1]};  "
          f"referee: {r2}", flush=True)


if __name__ == "__main__":
    main()
