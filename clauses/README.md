# The noise and Kullback–Leibler clauses of OQP 27B, and POVMs

This folder contains our results on the clauses of Problem 27B that go beyond the optimality and uniqueness theorem of the
papers, and one strengthening of that theorem (POVMs, d = 3..8). [`LEDGER.md`](LEDGER.md) has the exact wording of the
problem and the status of every clause; several of these clauses are only partly settled.

| Folder | Clause | Result | Checks |
|---|---|---|---|
| [`noise-cglmp/`](noise-cglmp/) | 27B(ii), noise resistance of the CGLMP violation (white noise on Phi_d) | proved for every d (computer-assisted for d >= 21); DKZ is the unique optimum | Lean: `../lean/OQP27/CglmpNoise.lean`, `../formal-conjectures-27/27.lean` |
| [`noise-literal/`](noise-literal/) | 27B(ii), violation of local realism (all Bell inequalities) under Gill's uniform outcome noise | false for every d >= 4 when measurements may have unused outcomes (zero projectors) or be POVMs; for complete von Neumann measurements on Phi_d proved for d = 3 (d = 4: `noise-complete-vn/`) and open for d >= 5 | `python verify_theorem.py` (17 checks, about 3 min); two re-verifications |
| [`noise-complete-vn/`](noise-complete-vn/) | 27B(ii), violation of local realism (all Bell inequalities), complete von Neumann measurements, d = 4 | true: DKZ has the lowest critical visibility, 2/I_ME(4), and is the only optimum; via the complete facet list of L(2,2,4) (11 665 992 facets, 34 classes) | `python CLOSE_verify.py 4 --skip-polar`, `python IND_summary.py`; an independent re-implementation |
| [`noise-dkz-threshold/`](noise-dkz-threshold/) | 27B(ii), violation of local realism (all Bell inequalities), white noise: DKZ's own threshold | for every d: DKZ's critical visibility against all Bell inequalities is exactly 2/I_ME(d) (CGLMP is optimal for DKZ), and DKZ is a strict local optimum | `python lemmaM_verify.py 3 2001`, `python lemmaM_verify_iv.py B 3 2001`, `python lemmaM_constants.py`; two implementations of the computer part |
| [`noise-covariant/`](noise-covariant/) | 27B(ii), violation of local realism, covariant strategies (every DFT + diagonal-phase strategy, any local dimension) | true for d = 5, 6, 7: DKZ is the unique optimum; via the complete facet lists of the cyclic local polytope K_d | `python kd_cert_run.py d ...`, `python kd_check.py d`; separately written re-check of facets and ratio bounds |
| [`kl-divergence/`](kl-divergence/) | 27B(iii), Kullback-Leibler discrimination | false for every d >= 4 (complete von Neumann competitors on Phi_d); d = 3 open, DKZ_3 a strict local maximum, and the global optimum inside the Fourier-shift family F3 (`fourier-family/`) | `python verify_main.py` and the scripts listed in THEOREM.md; one re-verification; `fourier-family/`: certificate re-check and interval checks |
| [`povm/`](povm/) | strengthening of 27B(i): arbitrary POVMs instead of projective measurements | DKZ optimal and unique among all POVMs for d = 3..8 (every local dimension) | `cd certs && python ../verify_povm.py 3 4 5 6 7 8` (exact; add `iv` first for the interval check); one re-verification |

Each theorem is stated and proved in the folder's `THEOREM.md`. Every computational input is checked in exact
rational/algebraic arithmetic or with rigorous interval enclosures; no decision rests on a floating-point comparison.
The re-verifications re-derived the proofs and re-checked the computations with separately written code; their reports
are `INDEPENDENT_VERIFICATION*.md`, and their scripts and logs are in the `independent-check*` subfolders. They are
internal checks, not peer review.

Requirements: Python 3 with numpy, scipy, sympy and mpmath. Run each script from its own folder with
`OMP_NUM_THREADS=1`.
