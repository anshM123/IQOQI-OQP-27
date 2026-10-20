"""run_verify.py -- run verify_X.verify for n in [n0, n1], print FAIL lines immediately and a summary per block of
1000 values (worst ratios, worst positivity margins).  usage: python run_verify.py n0 n1"""
import sys, time
from verify_X import verify
n0, n1 = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time(); allpass = True
blk = None
def flush(b):
    print(f"[{b['lo']}..{b['hi']}] all_pass={b['ok']} worst_ratio={b['w']:.4f} (n={b['wn']}) "
          f"min_Qrel={b['q']:.3e} (n={b['qn']}) min_a={b['a']:.6f}  t={time.time()-t0:.0f}s", flush=True)
for n in range(n0, n1 + 1):
    o = verify(n)
    w = max(o.get('maxL', 0), o.get('maxU', 0), o.get('ratioM', 0)); q = o.get('Qmin_rel', 1e9)
    if blk is None:
        blk = dict(lo=n, hi=n, ok=True, w=0.0, wn=n, q=1e18, qn=n, a=1e9)
    blk['hi'] = n; blk['ok'] &= o['pass']
    if w > blk['w']: blk['w'], blk['wn'] = w, n
    if q < blk['q']: blk['q'], blk['qn'] = q, n
    blk['a'] = min(blk['a'], o['a'][0])
    if not o['pass']:
        allpass = False
        print("FAIL", o, flush=True)
    if (n - n0 + 1) % 1000 == 0:
        flush(blk); blk = None
if blk is not None: flush(blk)
print(f"RANGE {n0}..{n1}: {'ALL PASS' if allpass else 'SOME FAIL'}  total time {time.time()-t0:.0f}s", flush=True)
