# Independent verification: noise clause on direct sums

Four independent re-checks were done on 2026-10-20. Each used separately written scripts, and none edited the
material under review. The re-check scripts themselves are not part of this folder. Below, "proved" means a
pen-and-paper argument was checked, "certified" means interval or exact arithmetic, and "numerical" means floating
point.

## 1. Two-block law DS (2 <= m <= k <= 100), from the first version of the template
- CLAIM(phi_inf(n)) was certified by an independent re-implementation for every n = 2..100. Re-runs of the original
  certificates passed, including n = 83, 99 and 100.
- CLAIM(Q_n) (Theorem M) was re-certified for every 3 <= n <= 100.
- kappa_n was certified strictly increasing on 2..400. The smallest certified gap is >= 9.5e-7.
- The witness's local bound was checked in exact rational arithmetic for (2,2) .. (6,2), and by a re-run for (5,5),
  (7,4) and (9,3).
- Verdict: OK.

## 2. Theorem PHI (all n), multi-block law DS_r, Lemma K
- **Theorem PHI.** OK.
  - Construction X was checked in exact rational arithmetic and end to end.
  - The interval verifier (`code/ia.py`, `code/verify_X.py`) is rigorous, and was re-run over 4 <= n <= 50000.
  - The large-n argument was checked for structure, Lemma D analytically, the region-A allowances and the envelope
    assembly to leading order. The remaining constants were checked numerically, at four values of n with
    comfortable slack.
- **DS_r.** OK (proved). The bookkeeping and t_ij >= 0 hold in general, and independent LPs agree with the law.
- **Lemma K.** OK. The analytic bound has a factor-5 margin, and the interval part covers n <= 2000. THEOREM.md now uses
  a different, fully analytic proof (convexity of y/sin y plus a mean-preserving spread). That proof was checked line
  by line in a separate pre-publication review.
- Minor findings, none affecting the conclusions:
  - `code/lemma_sanity.py` tests looser constants than the written proof states. A separate check with the stated
    constants passes.
  - The large-n write-up is terse.

## 3. Theorem LB
- **(i), the witness.** PASS. The local bounds of the coarse-grained functionals were brute-forced over all d^4
  points: 162 combinations of U, coarse-graining block and point, with J = I and random J. F(P_v) = 2 exactly at
  v0(U), to 9e-16.
- **Template and bookkeeping lemma.** PASS.
  - All four adapted link laws equal G_n, checked for n = 2..10.
  - Every cell type matches to 9e-16, including C x C and the cross cells for J != I.
  - Ten models were assembled independently, including three in the large-m regime (d = 66, 73, 77). Each reproduces
    v P + (1 - v) u to <= 1.5e-16.
- **(ii).** PASS. There are 54 identities, checked in sympy and at exact rational points. The exact threshold for
  F's orientation condition is m/K <= 2.42963.
- **(iii).** PASS. A scan of 7,447,200 configurations (m <= 200) found no counterexample.
  - One intermediate constant was wrong for d >= 20253: 0.4849 must be 0.4850, because kappa_oo - 1 = 0.4849075.
    It is corrected in THEOREM.md, and the conclusion is unaffected.
- **Independent LPs.** 52 LPs (d <= 9, J = I and random J) give v_c = v0 to 5.6e-16.

## 4. LB+, LB-exact and LB*
- **LB+.** PASS.
  - With every mode-A part except F_C assembled, what is left over is v_T P_T + (1 - v_T) u_m on the T-block, to
    1e-16, and zero elsewhere.
  - In LP tests, v_c(T) only 0.03-0.04% below v_T already gives v_c < v0.
- **LB-exact.** PASS. The Gale/Hall condition and the subset algebra were verified in sympy. An orientation LP agrees
  with the subset criterion in 1500/1500 random configurations (222 of them failing it).
- **LB\*.** PASS. The key inequality was verified in sympy. In 2500 random compositions (707 with a proper minimiser),
  every recursive condition held: 3578 Hall LPs, 3343 LB+ conditions and 4260 f-inequalities. An exhaustive scan puts
  the first proper minimiser at d = 42.

## Checked in the pre-publication review
- **Lemma TH.** Proof checked by hand. It agrees with brute force in all 2500 compositions of the LB* scan.
- **Lemma U and Corollary P.** Proofs checked by hand. `code/nbhd_check.py` (Lemma U on 120 random cases): 0 failures.
