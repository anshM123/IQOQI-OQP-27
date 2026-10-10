# DKZ's white-noise threshold against all Bell inequalities, every d

The statement and proof are in [`THEOREM.md`](THEOREM.md). The result holds for every d ≥ 3:
- **Exact threshold.** The critical visibility of DKZ against all Bell inequalities of the (2,2,d) scenario is exactly
  2/I_ME(d). So CGLMP is an optimal Bell inequality for DKZ under white noise.
- **Strict local optimality.** DKZ is a strict local optimum: near DKZ, v_c(p) = 2/I′(p).

**Status:** proved.
- **Computer-assisted part:** d ≤ 2001, with two separately written implementations.
- **Written proof:** d ≥ 2002.
- **Review:** no separate re-verification report yet; not reviewed by outside experts.

## Files and commands

Run from this folder with `OMP_NUM_THREADS=1`. The scripts need python-flint, mpmath, numpy and scipy.

| Command | Time | What it checks | Log |
|---|---|---|---|
| `python lemmaM_verify.py 3 2001` | seconds | (P1)–(P3) of the construction for d = 3..2001, ball arithmetic, κ_d from its definition | `logs/lemmaM_verify_3_2001_def.log` |
| `python lemmaM_verify_iv.py B 3 2001` | 2 min | the same, separately written code, mpmath intervals | `logs/lemmaM_verify_iv_B_def.log` |
| `python lemmaM_verify_iv.py A 3 150` | 15 s | the full pairing coupling for d = 3..150, checked directly without the core lemma | `logs/lemmaM_verify_iv_A_def.log` |
| `python lemmaM_constants.py` | seconds | every constant of the written proof for d ≥ 2002 | `logs/lemmaM_constants.log` |
| `python cert_local.py 3 100` | minutes | earlier certificate of CLAIM_d (relative interior of the CGLMP face), d = 3..100 | `logs/cert_local_*.log` |
| `python verify_local.py 3 30 4` | minutes | the same, separately written with Python fractions; exact facet check for d = 3, 4 | `logs/verify_local_3_30.log` |
| `python dkz_vc_lp.py` | minutes | numerical: the LP over all deterministic points gives v_c(DKZ_d) = 2/I_ME(d), d = 3..10 | `logs/dkz_vc_lp.log` |

**Other logs.**
- `lemmaM_verify_3_2001.log`, `lemmaM_verify_iv_A.log` and `lemmaM_verify_iv_B.log` come from earlier runs that took κ_d
  from its closed form. They agree with the `_def` runs.
- `lemmaM_verify_large_spot.log` has the spot checks at d = 5000, 10000 and 40000.
- `lemmaM_anti.py` builds the construction.
- `lemmaM_pairing.py`, `lemmaM_structure.py`, `lemmaM_core.py` and `lemmaM_margin.py` are the exploration that led to it.
- `core.py` and `facet_lib.py` are helpers for `verify_local.py`. They are identical to the copies in
  `../noise-complete-vn/`.
