# The noise clause for covariant strategies, d = 5, 6, 7

The statements and proofs are in [`THEOREM.md`](THEOREM.md). For d = 5, 6, 7, DKZ has the lowest white-noise critical
visibility against all Bell inequalities among all balanced maximally entangled strategies with covariant behaviour. That
includes every DFT + diagonal-phase strategy, any local dimension, and their relabellings. DKZ is the only optimum.

**Status:** proved, computer-assisted, with a separately written re-check of the facet lists and of the ratio bounds.
Not reviewed by outside experts.

## Files and commands

Run from this folder with `OMP_NUM_THREADS=1`. The scripts need numpy, scipy, cvxpy (SCS), python-flint and numba.

| Command | What it does | Log |
|---|---|---|
| `python kd_facets.py d` (d = 2..6) | facets of K_d by exact double description, grouped into classes; writes `kd_facets_d{d}.json` and `kd_facets_d{d}_raw.npy` | `logs/kd_facets_d*.log` |
| `python kd_adjacency.py d` (d = 4..7) | facets of K_d by exact symmetric adjacency decomposition with the Theorem V completeness check | `logs/kd_adjacency_d*.log` (`_numba`: ridge double descriptions done by `dd_numba.py`) |
| `python kd_adj_tables.py 7` | class tables for d = 7 from the decomposition; writes `kd_facets_d7.json` | `logs/kd_adj_tables_d7.log` |
| `python kd_cert_run.py d classes` | certified ratio bounds (exact dual certificates) for the listed classes | `logs/kd_cert_d5.log`, `kd_cert_d6.log`, `kd_cert_d7.log` |
| `python kd_check.py d [classes]` | separately written re-check: naive exact double description, and the projector-word relaxation with rational certificates | `logs/kd_check_d5.log`, `kd_check_d6*.log`, `kd_check_d7.log` |
| `python kd_check_sets.py d` (d = 4, 5) | the naive facet set equals the double-description facet set | `logs/kd_check_sets.log` (rerun 2026-10-10) |
| `python kd_check_orbits.py d`, `python kd_cglmp_ident.py d FACETFILE` (d = 6, 7; FACETFILE = `kd_facets_d{d}.json`) | orbit sizes from a separate relabelling code; the CGLMP class contains the CGLMP Π-form facet | `logs/kd_check_orbits.log`, `logs/kd_cglmp_ident.log` |
| `python kd_ratio.py d [starts]`, `python kd_lower67.py d starts` | lower bounds on the ratios from DFT + phase strategies, numerical (`starts` random starts; default 20) | `logs/kd_ratio_d*.log`, `logs/kd_lower_d*.log` |

**Other files.**
- `kd_sdp.py` is the level-2 relaxation used by `kd_cert_run.py`.
- `kd_float6.py` and `kd_sdp_d*_float.log` are floating-point runs, used only to choose certificates.
- `kd_check6.py` is the d = 6 driver of the re-check.
- `IND_dd.py`, `dd_numba.py` and `dd_exact.py` are the double-description codes. They are identical to the copies in
  `../noise-complete-vn/`.
- `kd_adjacency_d8.log` is a run for d = 8 that was stopped by hand. It is not part of any proof.
- The adjacency runs for d = 6 and 7 take hours. The other scripts take seconds to minutes.
