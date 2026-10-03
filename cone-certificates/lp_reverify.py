"""lp_reverify.py: re-run the rigorous LP certificate check verify_cone.verify (160-bit interval arithmetic, unchanged) on the stored
certificates certs/cert_d{d}.json for the given d (QD2-T1).  Used by `python audit_alld.py --reverify-lp [NPROC]`.
Usage: python lp_reverify.py d1 d2 ...   prints one line 'LPCHECK d ok msg' per d."""
import sys, json
from verify_cone import verify, ghat_grid

for d in [int(a) for a in sys.argv[1:]]:
    try:
        c = json.load(open(f'certs/cert_d{d}.json'))
        ok, msg = verify(d, c['cells'], c['lam'], ghat_grid(d, c['q']))
        print(f"LPCHECK {d} {bool(ok)} {msg}", flush=True)
    except Exception as ex:
        print(f"LPCHECK {d} False exception {ex!r}", flush=True)
