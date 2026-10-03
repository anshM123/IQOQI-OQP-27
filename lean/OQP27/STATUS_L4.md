# STATUS of module L4 (`OQP27/Cert*.lean`): CONE_d

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.  Status as of 2026-10-02.

## 1. Summary

* `OQP27.ConeCert d` (file `CertDefs.lean`) is the Lean statement of CONE_d; the skeleton of module L1
  (`Skeleton.lean`) imports it and also uses its strengthening `OQP27.ConeCertPos d` (one all-positive cell vector
  carries positive weight).
* **Proved in Lean, with no hypotheses, for every 2 <= d <= 20:** `OQP27.coneCert_le_twenty` (file `CertAll.lean`)
  and `OQP27.coneCertPos_le_twenty` (file `CertPos.lean`).  Each case is an explicit certificate checked by the
  Lean kernel (`decide +kernel`, no `native_decide`).  `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]` for every main theorem (`CertAxioms.lean`, log `logs/CertAxioms.log`).
* **Verified interface** (`OQP27.ConeCertificate.sound`, file `CertCheck.lean`): a certificate (rational cells,
  rational approximate weights, the residual-correction data of `QD2/verify_cone.py`) that passes the stated
  rational inequalities, for any rational interval enclosures of the entries of `U` and `v` supplied as inputs,
  implies `ConeCert d` (`sound_strong`: moreover every weight is positive).  The complete checker
  `OQP27.ConeCertificate.fullCheck` also computes the enclosures; `fullCheck_sound : c.fullCheck = true -> ConeCert c.d`.
* For d >= 21, CONE_d enters only as the named hypotheses `OQP27.Hyp_ConeCert_large` (`CertAll.lean`) and
  `OQP27.Hyp_ConeCertPos_large` (`CertPos.lean`), with `OQP27.coneCert_all`, `OQP27.coneCertPos_all` (every d >= 2).
  Section 7 states exactly what the Python interval computations behind them check, and how their output gives
  the finite statement `ConeCert d` / `ConeCertPos d`.
* The original LP certificates `QD2/certs/cert_d2.json`, `cert_d3.json` (q = 16, more columns than rows) are
  re-checked in Lean unchanged (`OQP27.coneCert_2_lp`, `OQP27.coneCert_3_lp`, file `CertLP.lean`).

No `sorry`, `admit`, `axiom` or `native_decide` in `OQP27/Cert*.lean`.

## 2. Definitions (`CertDefs.lean`), checked against `QD2/cells.py`

`Skeleton.lean` (module L1) did not exist when `CertDefs.lean` was written; the CONE_d objects are therefore defined
here (namespace `OQP27`, names prefixed `cone`), and `Skeleton.lean` now imports them.

| Lean | mathematics | Python (`QD2/cells.py`) |
|---|---|---|
| `clausen2 θ = ∑' k, sin((k+1)θ)/(k+1)^2` | Cl2(θ) = sum_{k>=1} sin(kθ)/k^2 | `cl2` (Im Li2(e^{iθ})) |
| `coneG d u = -((4d)^2/(2π^2)) * clausen2 (2πu/(4d))` | G(u), N = 4d | `Gfun` |
| `coneGhat d u = coneG d u + coneG d (2d - u)` | Ĝ(u) | `Ghat_vec` |
| `coneWindowSum d ℓ r m = ∑_{i<m} ℓ((r+i) mod d)` | S_r(m) | `cs[r+m]-cs[r]` in `u_window` |
| `coneP d ℓ m = (∑_{r<d} Ĝ(S_r(m)))/d` | P(m) | `P` in `u_window` |
| `coneU d ℓ m = P(m+1) - 2P(m) + P(m-1)` | u^ℓ_m (QD2-L2), m = 1..d-1 | `u_window` |
| `coneV d m = 2/sin(πm/(2d))` | v_m = 2 csc(πm/(2d)) | `v_vector` |
| `IsConeCell d ℓ`: `ℓ r >= 0` (r < d), `∑_{r<d} ℓ r = d` | cell vector | — |
| `ConeCert d`: ∃ K, cells ℓ^(k), λ_k >= 0 with ∑_k λ_k u^{ℓ^(k)}_m = v_m (1 <= m <= d-1) | CONE_d | — |

A cell vector is a function `ℕ → ℝ` of which only `ℓ 0, …, ℓ (d-1)` are used.  Cells may have zero entries
(QD2-L1 assumes only ℓ_r >= 0); the Lean certificates for d <= 20 use integer cells, some with zeros, and all
contain the uniform cell (1, …, 1).  Numerical cross-check (`certdata/crosscheck_defs.py`): for random integer
cells (d = 2..12, q = 1, 2) the enclosures computed by an exact re-implementation of the Lean checker
(`certdata/leanemu.py`) contain the float values of both `u_window` (window form) and `u_vector` (the original
cell-pair kernel K^ℓ(x, y)), to float rounding (max relative deviation 7e-14), and the enclosures of v contain
`v_vector`.  (`Skeleton.lean` proves the window form equal to the kernel form: `OQP27.cellDirection_eq_coneU`.)

## 3. Lean declarations

Build logs: `OQP27/logs/<File>.log` (stdout of `leanrun.sh`).

| Lean name | statement | status | file |
|---|---|---|---|
| `OQP27.clausen2_summable`, `clausen2_hasSum` | the Clausen series converges absolutely | PROVED | CertDefs |
| `OQP27.QI.Mem.add/neg/sub/smul/mul/inv/round/widen`, `QI.mem_sumRange`, `QI.Mem.abs_le_mag` | soundness of rational interval arithmetic with outward rounding to 2^-k | PROVED | CertInterval |
| `OQP27.piLo_lt_pi`, `OQP27.pi_lt_piHi` | 3.14159265358979323846 < π < 3.14159265358979323847 (Mathlib `Real.pi_gt_d20`, `pi_lt_d20`) | PROVED | CertTrig |
| `OQP27.sinTaylor_le_sin`, `sin_le_sinTaylor`, `cosTaylor_le_cos`, `cos_le_cosTaylor` | for 0 <= x <= 1, Taylor partial sums of sin, cos with an even (odd) number of terms are lower (upper) bounds | PROVED | CertTrig |
| `OQP27.mem_sinSmall`, `mem_cosSmall`, `mem_sinPi` | enclosures of sin(πr), cos(πr); `sinPi r` is sound for every rational r | PROVED | CertTrig |
| `OQP27.g7_tele`, `g5_tele`, `tail_bounds` | g5(y) <= ∑_{i>=0} 1/(i+y)^2 <= g7(y) for y >= 1 | PROVED | CertClausen |
| `OQP27.hurwitzQ_split`, `mem_hEnc` | enclosure of H(Q,b) = ∑_{i>=0} 1/(b+Qi)^2 | PROVED | CertClausen |
| `OQP27.clausen2_rat` | Cl2(2πc/Q) = ∑_{a<Q} sin(2πc(a+1)/Q) H(Q, a+1) | PROVED | CertClausen |
| `OQP27.mem_clEnc`, `mem_clTab`, `mem_factorEnc`, `coneGhat_rat`, `mem_gEnc` | enclosures of Cl2(2πc/Q) and of Ĝ(J/q), 0 <= J <= 2dq | PROVED | CertClausen |
| `OQP27.winN_le`, `mem_gTab`, `mem_pEnc`, `mem_uList`, `mem_vEnc` | enclosures of P(m), u^ℓ_m (cells n/q with ∑ n = dq) and v_m | PROVED | CertPipeline |
| `OQP27.exists_solve_of_approx_inverse` | ‖I - RW‖_∞ <= eps < 1 and ‖Rb‖_∞ <= beta give y with Wy = b, ‖y‖_∞ <= beta/(1-eps) | PROVED | CertCheck |
| `OQP27.coneCheckCore_sound` | residual-correction check (Section 4) gives x > 0 with Ux = v | PROVED | CertCheck |
| `OQP27.ConeCertificate.sound`, `sound_strong` | **interface**: valid cells + passing check for supplied enclosures give `ConeCert d` (all weights > 0) | PROVED | CertCheck |
| `OQP27.ConeCertificate.fullCheck_sound`, `fullCheck_sound_strong` | `fullCheck c = true` gives `ConeCert c.d` (all weights > 0) | PROVED | CertPipeline |
| `OQP27.ConeCertificate.fullCheckU_sound`, `fullCheck_of_fullCheckU`, `OQP27.qiTableEqb_eq` | two-stage check (literal u-table proved equal to the computed one) | PROVED | CertStaged |
| `OQP27.ClChunkOK`, `clChunkOK_append`, `clChunkOK_of_eq`, `gTabOK_gTabOf`, `mem_uList_of`, `ConeCertificate.fullCheckWith_sound` | Clausen table assembled from separately checked chunks | PROVED | CertChunked |
| `OQP27.coneCert_2` … `OQP27.coneCert_20`, `OQP27.cert<d>_check` | CONE_d for d = 2, …, 20 | PROVED (kernel-checked certificates) | CertSmall (2-8), CertMid (9-12), CertD13 … CertD20 |
| `OQP27.coneCert_le_twenty` | CONE_d for all 2 <= d <= 20 | PROVED | CertAll |
| `OQP27.Hyp_ConeCert_large` | CONE_d for every d >= 21 | HYPOTHESIS (computer-assisted in Python; Section 7) | CertAll |
| `OQP27.coneCert_all` | `Hyp_ConeCert_large` gives CONE_d for every d >= 2 | PROVED | CertAll |
| `OQP27.ConeCertificate.coneCertPos_of_check` | a passing certificate with an all-positive cell gives `ConeCertPos d` | PROVED | CertPos |
| `OQP27.coneCertPos_2` … `coneCertPos_20`, `OQP27.coneCertPos_le_twenty` | `ConeCertPos d` for 2 <= d <= 20 | PROVED | CertPos |
| `OQP27.Hyp_ConeCertPos_large` | `ConeCertPos d` for every d >= 21 | HYPOTHESIS (Section 7) | CertPos |
| `OQP27.coneCertPos_all` | `Hyp_ConeCertPos_large` gives `ConeCertPos d` for every d >= 2 | PROVED | CertPos |
| `OQP27.coneCert_2_lp`, `OQP27.coneCert_3_lp` | CONE_2, CONE_3 from the unchanged LP certificates `QD2/certs/cert_d2.json`, `cert_d3.json` | PROVED | CertLP |
| (`#print axioms` of the main theorems) | — | all `[propext, Classical.choice, Quot.sound]` | CertAxioms |

For the integration: given `h : OQP27.Hyp_ConeCertPos_large`, the term `fun d _ hd => OQP27.coneCertPos_all h d hd`
is the `hcone` argument of `OQP27.maxEntClause_all_d` (`Skeleton.lean`); for a single `d <= 20`,
`OQP27.coneCertPos_le_twenty d h2 h20` needs no hypothesis.

## 4. The certificate format and the verified interface (`CertCheck.lean`)

`OQP27.ConeCertificate`: `d`; a denominator `q > 0`; cells `n^(1..K)` (lists of naturals, ℓ^(k) = n^(k)/q, checked
∑_{r<d} n^(k)_r = d q); rational approximate weights `λ̃_k`; a rational (d-1)×(d-1) matrix `R`; rationals `eps`,
`beta`.  With U the real (d-1)×K matrix U_{m,k} = u^{ℓ^(k)}_{m+1} and rational interval enclosures `UI`, `vI` of U
and v, the check (`coneCheckCore`, exact rational interval arithmetic) is the scheme of `QD2/verify_cone.py`
(function `verify`):
1. 0 <= eps < 1 and 0 <= beta;
2. for every row i: ∑_j |I - R W|_{ij} <= eps, where W = U Uᵀ is enclosed entrywise;
3. for every row i: |R (v - U λ̃)|_i <= beta;
4. for every column k: λ̃_k - (∑_m |U_{m,k}|) · beta/(1-eps) > 0.

Soundness: by (2), RW is injective, so W is invertible (finite dimension); the solution y of W y = v - U λ̃
satisfies y = (I - RW) y + R(v - U λ̃), hence ‖y‖_∞ <= beta/(1-eps); then λ = λ̃ + Uᵀ y solves U λ = v exactly, and
λ_k > 0 by (4).  (`verify_cone.py` writes the same bound as |y| <= |R res|/(1 - |I - RW|); here the two maxima are
certificate data checked row by row.)

## 5. Rigorous enclosures (`CertTrig.lean`, `CertClausen.lean`, `CertPipeline.lean`)

All arithmetic is exact over ℚ with outward rounding of intermediate results to the grid 2^-100.
* π: 20 correct digits (Mathlib).
* sin(πr), cos(πr) for 0 <= r with πr <= 1: monotonicity of sin/cos on [0, π/2] and the alternating Taylor bounds
  (10 / 11 terms) at the rational endpoints piLo·r, piHi·r; other r are reduced to [0, 1/4] by periodicity and
  sin(x+π) = -sin x, sin(π-x) = sin x, sin x = cos(π/2-x).  Width about 1e-20.
* Cl2(2πc/Q): grouping the series by residues mod Q (`Nat.sumByResidueClasses`) gives exactly
  Cl2(2πc/Q) = ∑_{a=0}^{Q-1} sin(2πc(a+1)/Q) H(Q, a+1); H(Q,b) = ∑_{i<20} 1/(b+Qi)^2 + Q^-2 ∑_{i>=0} 1/(i+y)^2 with
  y = 20 + b/Q, and the tail lies between g5(y) and g7(y), g5(t) = 1/t + 1/(2t^2) + 1/(6t^3) - 1/(30t^5),
  g7 = g5 + 1/(42t^7), by the exact telescoping identities
  g7(t) - g7(t+1) - 1/t^2 = (63t^4+126t^3+98t^2+35t+5)/(210 t^7 (t+1)^7) and
  1/t^2 - g5(t) + g5(t+1) = (5t^2+5t+1)/(30 t^5 (t+1)^5).
* Ĝ(J/q) = -(N^2/2π^2)(Cl2(2πJ/Q) + Cl2(2π(2dq-J)/Q)), Q = 4dq (`coneGhat_rat`), 0 <= J <= 2dq.
* u^ℓ_m: window sums of integer cells are integers J_r(m) <= dq (`winN_le`); P and Δ² in interval arithmetic.
* v_m = 2/sin(πm/(2d)): reciprocal of a positive enclosure (positivity of its lower end is part of `fullCheck`).

The checkers are computable functions; for a concrete certificate the Boolean check is proved `true` by
`decide +kernel` (kernel evaluation of the rational arithmetic; no `native_decide`, no axioms beyond the three
standard ones).  For d >= 13 the evaluation is split into two declarations to bound memory (`CertStaged.lean`:
the table of u-enclosures is a literal proved equal to the computed table); for the LP certificates (q = 16) the
Clausen table is assembled from separately checked chunks (`CertChunked.lean`).

## 6. The certificates for 2 <= d <= 20

Generated by `certdata/explore.py` (exhaustive, d <= 7), `certdata/explore2.py` / `certdata/explore3.py` (random
integer cells; `explore3` forces the uniform cell into the basis): square bases of d-1 *integer* cells (q = 1,
zero entries allowed) with v = U λ, λ > 0.  `certdata/gencert.py` computes λ̃ (22 digits), R = (U Uᵀ)^{-1}
(22 digits), and eps, beta (4x the values found by `certdata/leanemu.py`, an exact re-implementation of the Lean
checker, rounded up); `certdata/mkfiles.py` (d <= 12) and `certdata/mkstaged.py` (d >= 13) write the Lean files and
`certdata/cert_d<d>.json`; the cells are in `certdata/cells_d2_d20.json`.  The data are untrusted: only the kernel
check counts.

| d | cells (K) | eps | beta | certified min λ_k | file | build of the file (s) |
|---|---|---|---|---|---|---|
| 2 | 1 | 23/1000000000000 | 23/10000000000000 | 0.7395 | CertSmall | 43 |
| 3 | 2 | 17/10000000000 | 31/500000000000 | 0.3747 | CertSmall | 43 |
| 4 | 3 | 3/2000000000 | 1/31250000000 | 0.1651 | CertSmall | 43 |
| 5 | 4 | 53/10000000000 | 3/50000000000 | 0.1461 | CertSmall | 43 |
| 6 | 5 | 1/156250000 | 23/500000000000 | 0.093 | CertSmall | 43 |
| 7 | 6 | 59/1000000000 | 33/100000000000 | 0.06685 | CertSmall | 43 |
| 8 | 7 | 67/10000000000 | 33/1000000000000 | 0.04585 | CertSmall | 43 |
| 9 | 8 | 21/500000000 | 1/6250000000 | 0.02371 | CertMid | 122 |
| 10 | 9 | 19/500000000 | 11/100000000000 | 0.02006 | CertMid | 122 |
| 11 | 10 | 11/100000000 | 23/100000000000 | 0.01957 | CertMid | 122 |
| 12 | 11 | 7/25000000 | 1/2000000000 | 0.01548 | CertMid | 122 |
| 13 | 12 | 53/10000000 | 29/5000000000 | 0.01669 | CertD13 | 66 |
| 14 | 13 | 3/2000000 | 13/10000000000 | 0.008439 | CertD14 | 82 |
| 15 | 14 | 67/100000000 | 13/20000000000 | 0.005353 | CertD15 | 102 |
| 16 | 15 | 17/1000000 | 11/1000000000 | 0.008422 | CertD16 | 163 |
| 17 | 16 | 21/10000000 | 7/5000000000 | 0.006808 | CertD17 | 209 |
| 18 | 17 | 21/5000000 | 1/400000000 | 0.006897 | CertD18 | 259 |
| 19 | 18 | 3/20000 | 67/1000000000 | 0.007977 | CertD19 | 475 |
| 20 | 19 | 63/1000000 | 1/40000000 | 0.003398 | CertD20 | 543 |

"certified min λ_k" is λ̃_k - colsum·beta/(1-eps) from the exact emulation (the kernel check establishes > 0).
Build times are wall-clock for the whole file on the shared machine (the files for d >= 19 ran under memory
pressure); `CertSmall` and `CertMid` are single-stage, `CertD13` … `CertD20` two-stage.

## 7. CONE_d for d >= 21: what the Python interval computations check (not formalised)

**UPDATE (2026-10-02, after this audit): every gap listed below has been closed in code.**  201 <= d <= 2000: new single-run
certifier `QD2/verify_cert.py` (one precision, one code version, one box per d; G1-G7 fixed), 1800/1800 certified
(`QD2/RIGOR_GAUSS.md`, `logs/audit_cert_g_final.log`).  d >= 2001: identity I2 and the other paper-only items written out in full, the
hard-coded constants computed in interval arithmetic, G6/G7 fixed, full re-run (`QD2/RIGOR_ALLD.md`).  `python audit_alld.py` prints
ALL-D CERTIFIED (every d >= 2).  The text below is kept as the record of the audit.

All paths relative to `cone-certificates/`.  This section is an audit of the code and logs as they are
on 2026-10-02; the "gaps" listed are places where the code does not literally enclose a quantity.  None of them
changes a conclusion (the margins exceed the possible errors by large factors), but they are not closed in code.

### 7.1 LP regime, 2 <= d <= 200 (QD2-T1)
* Files: `verify_cone.py` (`verify`), drivers `run_verify.py`, `run_verify_rev.py`; certificates
  `certs/cert_d{d}.json` (d, q = 16, cells n^(k) with every n_r >= 1 and ∑ n = 16d, float weights λ̃, a text
  note); logs `logs/verify_2_100.log`, `verify_101_145.log`, `verify_146_178.log`, `verify_179_200.log`,
  `verify_rev_168_178.log`, `verify_rev_192_200.log`.
* Interval arithmetic: `mpmath.iv` at 160 bits.  Cl2(t), 0 < t <= π, by
  t - t log t + ∑_{n<=70} |B_2n| t^{2n+1}/(2n(2n+1)!) + [0, t(π^2/6)4^-71/((3/4)·71·143)] (exact rational coefficients
  from `mpmath.bernfrac`; tail from ζ(2n) <= π^2/6); Cl2(0) = Cl2(π) = 0 exactly.  Ĝ(j/16) on the grid, u^ℓ by the
  window-sum form with exact integer window indices, v_m = 2/iv.sin(πm/(2d)).
* Linear algebra: the scheme of Section 4, with R = `mp.inverse(mid W)` (untrusted; any R is admissible) and
  the maxima computed instead of checked against given eps, beta.  The column search (scipy HiGHS, float Clausen
  values) is untrusted and only proposes candidates.
* Certified statement, for each d: explicit cells with all n_r >= 1 and λ_k > 0 with ∑_k λ_k u^{ℓ^(k)} = v exactly.
  This is literally `ConeCert d`, and `ConeCertPos d`.
* Status: every 2 <= d <= 200 verified on the first attempt; certified d·min λ_k in [0.0816, 0.2572];
  |y| <= 2.1e-11, ‖I - RW‖ <= 9.4e-34.  The JSON files do not store R or any interval; re-verification means
  re-running `verify`.  `crosscheck_certs.py` is an independent 50-digit (non-interval) residual check.
* Cross-check in Lean: `cert_d2.json` and `cert_d3.json` pass the Lean checker unchanged (`CertLP.lean`).
* Trusted: Python 3.14, mpmath 1.3.0 (`iv` arithmetic, `iv.log`, `iv.sin`, `iv.pi`, `iv.matrix`; `bernfrac`).

### 7.2 Gaussian regime, 201 <= d <= 2000 (QD2-T2)
* Construction (`CONE_PROOF.md`): the cell process Π_Φ: ℓ = d·Dir(1 + η) on E = {max_r |η_r| < 3/4} and
  ℓ = d·Dir(1, …, 1) on the complement, η a stationary Gaussian field on Z_d with ∑ η_r = 0 and window-sum
  variance Φ(m) (Φ symmetric, Φ(0) = Φ(d) = 0, cosine coefficients at_k >= 0).  Lemma R1: E_{Π_Φ}[u^ℓ] + Δ²W = v
  (scale c = 1) splits into (i) decoupled scalar equations Hc_m(Φ(m)) + e_m(Φ) = τ_m for the antisymmetric part
  (m < d/2; e_m = effect of the complement of E) and (ii) Δ²W >= 0 for the symmetric part, and
  Δ²W = ∑_s w_s t_s with t_s = e_s + e_{d-s}.
* `verify_gauss.py` (intervals, 100 bits for d <= 600, 160 bits above) encloses: F^(2j)(m), j <= 7, where
  F(b) = E Ĝ(d X_b), X_b ~ Beta(b, d-b) (singular part exactly through polygamma values = zeta values minus harmonic
  sums; regular part by an exact series plus derivative bounds); the targets τ_m; root boxes [a_m, b_m] of
  Hc_m(t) = τ_m with a certified sign change (Gaussian smoothing expanded to order 14 plus an order-16 Lagrange
  remainder); every cosine coefficient at_k > 0; the slack Δ²W > 0; the tail bounds
  P(E^c) <= 2d·exp(-9/(32 Φ(1))), ε_t, r.  Output `logs/vg_d{d}.json`.
* `verify_fixedpoint.py` certifies inf Hc_m' >= c1min/4 on the widened boxes [a_m - r, b_m + r] (condition (D) of
  Lemma B) and a bound on sup |∂_t H|.  Output `logs/fp_d{d}.json`.
* Lemma B (`CONE_PROOF.md`, Poincaré-Miranda): (D), the sign changes and |e_m| <= 2ε_t give Φ# in the boxes with
  (i) exactly; with the slack bound, (ii) holds.  Hence E_{Π_{Φ#}}[u^ℓ] + ∑_s w_s t_s = v with w_s >= 0.
* Margins (all 1800 values of d): d^2 min_k at_k >= 0.0285 (even d) / 0.0798 (odd d); d·min Δ²W >= 0.6336;
  P(E^c) <= 4.2e-37; (D) holds with ratio >= 4.001 (1 needed).  Sweeps complete: 1800 `vg` and 1800 `fp` files,
  all ok; `logs/audit_certs_final.log`: ALL CERTIFIED.
* Gaps (not closed in code): (G1) `fp` certifies (D) and the sign changes on its own boxes, while `min at_k` and
  `min Δ²W` are taken from the `vg` files, computed on boxes of another run (other precision / series length); the
  boxes are not nested (shifts up to 7.9e-14 at d = 201, against min at_k = 3.2e-6 there), so one extra
  perturbation step is needed; it would pass with a huge margin, but no script performs it.  (G2) the series for
  g_r(1) is truncated without a tail bound (omitted error about 3e-34 in τ_m).  (G3) a fallback bound in
  `trunc_mom` is invalid at j = 8 but is never triggered for d >= 201 (not checked).  (G4) a non-rigorous
  perturbation term in `verify_gauss.py`, superseded by the certified bound of `verify_fixedpoint.py`.
  (G5) 840 `vg` files predate the last edit of `verify_gauss.py`.  (G6) factorials and binomials are rounded to
  53 bits (mpmath default precision) before entering intervals in `a03_special.py`, `a10_pointwise.py` (and at
  PREC + 40 bits in `verify_gauss.py:42`); e.g. `iv.mpf(mpmath.factorial(25))` does not contain 25!; the relative
  errors (<= 2^-52) are not enclosed.  (G7) a few decisions use floats (tail blocks, JSON storage of min at_k and
  min Δ²W, constants in `audit_alld.py`).

### 7.3 Analytic regime, d >= 2001 (QD2-T3)
* `CONE_ALLD_PROOF.md`: smooth model Φ_e = ε b^2 u_e (ε = 1/d); Lemma P (from QD2-L11, QD2-L12) gives
  at_k(Φ) >= w_k [(ε^2/8)(P - 4γ^2/(βd(1 - 4/d))) - 2δ_max] from D_B[Φ_e](1) >= -γε^2,
  D_B[Φ_e](m) >= βε^3 (2 <= m <= d/2) and |Φ - Φ_e| <= δ_max.
* Interval Taylor models (`a01`-`a12`, `iv.prec` = 120, `a08` at 160), uniform in ε ∈ [0, 1/2001]: Q_O >= 7.4192,
  Λ(R2) >= 6.0224, A_2(1) ∈ [-2.75594562462218, -2.75594562462217], A_2(m) > 0 for m >= 2,
  D_B(1) >= -2.765192 ε^2, D_B(2) >= 206.884 ε^3, |Φ* - Φ_e| <= 6.645e-4 ε^2 (unique model root), slack densities
  >= 0.6509, F' >= 0.15204.  `audit_alld.py` prints ALL-D CERTIFIED (`logs/audit_alld_final.log`):
  at_k >= 0.118695 w_k ε^2, slack >= 0.617 ε, tail lemma and fixed point (log ρ <= -837).
* On paper only: Lemma P, QD2-L11, the Fejér/Pólya step of QD2-L12, identity I1, **identity I2 (b^3 U1 = φ_2;
  only a first-order sketch plus interval jets at five values of b; an error would enter at order ε^2)**, the
  section-4 decomposition and zone bookkeeping, the constants of `a10`, the bound |G - G_4| <= 137.7 ε^3 (computed
  numerically, hard-coded in `audit_alld.py`), monotonicity in d of the tail lemma, and A_min >= 0.105487899757
  (from `t35_polya.py`; no archived log; hard-coded).  Gaps G6, G7 apply here too.

### 7.4 From the Python output to `ConeCert d` and `ConeCertPos d`
* d <= 200: direct (explicit cells, all weights > 0, all cells with n_r >= 1).
* d >= 201: the output is v = E_Π[u^ℓ] + ∑_s w_s t_s with Π = Π_{Φ#} a probability measure on cell vectors and
  w_s >= 0.  The finite statement follows by an argument not written in `QD2` (supplied here):
  (a) t_s = u^{ℓ(s)}/κ_s for the two-residue cell ℓ(s) (mass on residues 0 and s), κ_s > 0 (QD2-R2; κ_s >= 0
  since u_m = ∫ Ĝ'' p_m with Ĝ'' > 0 (QD2-L5), and ≠ 0; numerically κ = 3.91, 6.59, 2.43 for s = 1, 2, 3 at d = 7);
  (b) ℓ ↦ u^ℓ is continuous and bounded on the simplex, Π is carried by the open simplex (Dirichlet laws), and the
  mean of a probability measure on R^{d-1} carried by a set A lies in conv(A) (finite dimension: induction on the
  dimension with a supporting hyperplane); by Carathéodory, E_Π[u^ℓ] = ∑_{j<=d} α_j u^{ℓ_j} with α_j >= 0,
  ∑ α_j = 1 and every ℓ_j strictly positive.  Hence v = ∑_j α_j u^{ℓ_j} + ∑_s (w_s/κ_s) u^{ℓ(s)}: `ConeCert d`;
  and some all-positive ℓ_j has α_j > 0: `ConeCertPos d`.  The cells are not explicit (existence only).
  (`CONE_PROOF.md` defines CONE_d as membership in the *closed* convex cone; this step gives the finite form.)

## 8. Reproduction

From `lean/`, each file separately and in this order (see `LEAN_BRIEF.md`):
`CertDefs, CertInterval, CertTrig, CertClausen, CertCheck, CertPipeline, CertStaged, CertChunked, CertSmall,
CertMid, CertD13, …, CertD20, CertAll, CertPos, CertLP, CertAxioms`, each with
`bash OQP27/leanrun.sh OQP27/<File>.lean -o .lake/build/lib/lean/OQP27/<File>.olean -i .lake/build/lib/lean/OQP27/<File>.ilean`.
The certificate files need 1-9 minutes and up to about 6 GB of memory each (d >= 18); build them one or two at
a time.  `CertLP` (q = 16, 64d Clausen angles) took 50 minutes (2994 s) and about 5 GB.
Regenerating the certificate data (from `OQP27/certdata/`, with `python`; needs mpmath,
numpy, scipy): `python mkfiles.py cells_d2_d20.json CertSmall 2 3 4 5 6 7 8`,
`python mkfiles.py cells_d2_d20.json CertMid 9 10 11 12`, `python mkstaged.py cells_d2_d20.json <d>` (d >= 13),
`python mklp.py 2 3`.
