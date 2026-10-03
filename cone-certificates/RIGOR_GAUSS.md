# CONE_d for 201 <= d <= 2000: the Gaussian-modulation certificates made literal in code

Date: 2026-10-02.  Authors: Ansh Mishra, Aryan Senthilkumar.  All paths are relative to `iqoqi/programs/oqp27B_all/QD2/`.

This note closes, for the regime 201 <= d <= 2000, the code gaps G1-G7 listed in `formal-conjectures/OQP27/STATUS_L4.md`
section 7.2 and gap G2 of `../Q_chain_check/REPORT.md`, and records a second review of `verify_gauss.py`.  The mathematics
(Lemmas R1-R4 and Lemma B of `CONE_PROOF.md`) is unchanged.  What changed is the code: one certifier, one precision, one code
version, one box, every quantity literally enclosed, every decision an interval comparison.

| file | role |
|---|---|
| `verify_cert.py` | the unified certifier (one run per d), writes `logs/cert_g_d{d}.json` |
| `test_verify_cert.py` | 22 tests of the constants and enclosures; output `logs/test_verify_cert.log` |
| `audit_cert_g.py` | re-checks every condition of Lemma B / Lemma R1 (ii) from the JSON strings; output `logs/audit_cert_g_final.log` |
| `run_cert.sh`, `start_cert.sh` | driver (one worker per residue class of d) and launcher (nohup, PIDs in `logs/run_cert_pids.txt`) |
| `logs/cert_g_d{d}.json` | 1800 certificates, d = 201..2000 |

The previous files `verify_gauss.py`, `verify_fixedpoint.py`, `audit_certs.py` and the logs `logs/vg_d*.json`, `logs/fp_d*.json`,
`logs/backup_prec100/` are unchanged; they are used below only for comparison.

## 1. Result

**SHA-256 of `verify_cert.py`: `ff56740d15d40a07c99deb6433fb1b0f40b5a2d5b356b3ec9da0270ff1fab6a7`** (stored in every
certificate and checked by the audit).

For every d with 201 <= d <= 2000, one run of `verify_cert.py` certifies all hypotheses of Lemma B and of Lemma R1 (ii) of
`CONE_PROOF.md` on one explicit Poincare-Miranda box (section 2).  Hence **CONE_d holds for every 201 <= d <= 2000**
(computer-assisted: 160-bit interval arithmetic; the lemmas themselves are on paper).  The audit `audit_cert_g.py` re-checks every
condition from the stored exact strings: **1800/1800 OK, ALL CERTIFIED** (section 7).  Minimum margins over all 1800 values
(lower endpoints of certified enclosures):

| quantity | certified minimum | where |
|---|---|---|
| d^2 min_k at_k on the box (B1) | 0.0631932 (even d), 0.126387 (odd d) | d = 2000 (k = 1000), d = 1999 |
| d min_m Delta^2 W on the box (ii) | 0.660025 | d = 201 |
| inf Hc_m' on the widened box / (c1min/4) | 4.00099 | d = 2000 |
| c_D r / (2 eps_t)  (condition (D)) | 10^0.6169 = 4.14 | d = 201 |
| (B3') face values / (2 eps_t) | 10^16.78 | d = 201 |
| eps_t (Lemma R4) | <= 10^-31.17 (d = 201), <= 10^-369.05 (d = 2000) | |
| min Delta^2 W / (4 eps_t) | 10^28.08 | d = 201 |
| truncation-moment fallback used | never | |

## 2. What one run certifies

For a given d, `verify_cert.py d` computes in one process, with `iv.prec = 160` throughout:

1. Enclosures of F^(2j)(m), j = 0..7, at every integer 1 <= m <= d-1, of tau_m = Dlt(m) - Dlt(d-m), and of the functions
   Hc_m(t) and d/dt H(b,t) (sections 4.2-4.6).
2. Root boxes [a_m, b_m] (1 <= m < d/2) with a certified sign change Hc_m(a_m) < tau_m < Hc_m(b_m).  The search (Newton on
   midpoints, step doubling) is untrusted; only the two interval evaluations at the end count.
3. The tail quantities of Lemma R4 in logarithms, and a box radius r = 2^e (e an integer, r >= 8 eps_t/c1min, r >= 2^-100).
4. The Poincare-Miranda box of Lemma B, Q = prod_{1 <= m < d/2} [lo_m, hi_m] with lo_m = lower endpoint of the interval
   a_m - r and hi_m = upper endpoint of b_m + r (so [a_m - r, b_m + r] is contained in [lo_m, hi_m]); for even d, Phi(d/2) is a
   fixed exact number (the antisymmetric equation is vacuous there; same choice as before: a smooth extrapolation).
5. ON Q (Phi(m) ranges over the whole interval [lo_m, hi_m] in every evaluation; no margin is taken from another run):
   * (B1)  min_k at_k(Phi) > 0 for all Phi in Q (interval DFT, all k = 1..d/2);
   * (D)   c_D := min_m inf_{t in [lo_m, hi_m]} Hc_m'(t) > 0 and c_D r > 2 eps_t; with the sign changes and a_m - lo_m >= r this
           gives (B3): Hc_m(lo_m) <= Hc_m(a_m) - c_D r < tau_m - 2 eps_t, and symmetrically at hi_m;
   * (B3') (B3) also directly: Hc_m(lo_m) - tau_m < -2 eps_t and Hc_m(hi_m) - tau_m > 2 eps_t, by interval evaluation at the faces;
   * (ii)  min_m Delta^2 W_H > 4 eps_t on Q, W_H = (P_v - H(., Phi))_S, so that W = (P_v - P)_S of the exact process (|P - H| <= eps_t
           pointwise, Lemma R4) has Delta^2 W > 0;
   * all boxes lie in t > 0, and P(E^c) is bounded with Phi(1) <= hi_1 (the upper end of the widened box).
   By Lemma B there is Phi# in Q solving the exact equations (i) of Lemma R1; (B1) makes Pi_{Phi#} a well-defined cell process,
   and (ii) holds for it.  Lemma R1 gives CONE_d.

The JSON file stores each certified bound as the EXACT decimal expansion of the binary interval endpoint (strings; a binary
fraction has a finite decimal expansion), together with the code hash, the precisions (`iv_prec` 160, search 200 bits, NSER 70,
KMAX 14, Euler-Maclaurin N = 64, K = 40), the Python/mpmath versions and a SHA-256 of the exact endpoints of all root and widened
boxes (`box_sha256`; `python verify_cert.py d --dump-boxes` also writes all boxes to `logs/boxes/`).  Fields of `bounds`:
`r` (= 2^`r_log2`), `phi1_root` = [a_1, b_1], `phi1_box` = [lo_1, hi_1], `phi_half`, `box_lo_min` = min_m lo_m, `c1min_lo`,
`signchange_left_max_hi` = max_m sup(Hc_m(a_m) - tau_m), `signchange_right_min_lo`, `D_cD_lo` = c_D, `face_left_max_hi`,
`face_right_min_lo`, `at_min_lo`, `slack_min_lo`, `supF1_hi`, `S1_hi`, `S16_hi`, `log_ptail_hi`, `log_eps_tail_hi`, and, for
information, `dHmax_hi`, `root_width_max`, `tail_gr1_hi`, `tail_Fr_hi`.  The field `approx` holds rounded display strings only.

## 3. The gaps and how they are closed

| gap | what it was | fix in `verify_cert.py` |
|---|---|---|
| G1 | min at_k and min Delta^2 W came from the `vg` run, the derivative condition (D) from the `fp` run, on boxes of different runs (not nested; shift 7.9e-14 at d = 201); the perturbation to one box was not performed by any script. | One run computes the root boxes, the widened box Q, and then min at_k, min Delta^2 W, (D), (B3) and the tails ON Q.  The audit checks the code hash of every file. |
| G2 | P_{v,r}(d) = d^2 g_r(1) used the truncated series sum_{i <= IMAX} g_i without a tail (omitted error about 3e-34 in tau_m for NSER = 60). | g_r(1) = sum_{i <= 141} g_i + [0, T], T = (2 pi/3) sum_{n > 70} 4^-n/(n(2n+1)) <= 4.93e-47 (all g_i > 0 for i >= 3; section 4.1); test: the enclosure contains -16 G/pi^2 (G Catalan's constant). |
| G3 | `trunc_mom` returned t^j 10^6 when a^2 <= 2j; this is below the full moment t^8 15!! = 2027025 t^8 at j = 8. | The fallback is the full moment t^j (2j-1)!!, valid for every j; the formula branch is used only when a^2 > 2j.  Fallback uses are counted in the JSON: 0 in all 1800 runs. |
| G4 | `verify_gauss.py` used the non-certified slack perturbation 4(r sup|F''| + eps_t). | No perturbation term: the slack is evaluated on Q.  The only correction is 4 eps_t (exact process vs H, Lemma R4). |
| G5 | 840 `vg` files predated the last edit of `verify_gauss.py`. | All 1800 certificates come from one file version; the audit compares the stored SHA-256 with the current `verify_cert.py`. |
| G6 | Factorials entered intervals after rounding to the mpmath working precision (`iv.mpf(mpmath.factorial(2n+1))` at 200 bits is inexact from 57!; at 140 bits, in the 100-bit runs, from 45!). | Every integer (n!, (2j-1)!!, 2^j j!, C(i,k), (d)_k, the Euler-Maclaurin and Bernoulli data) is a Python integer or Fraction, converted with outward rounding (`iv.mpf(int)` rounds outward; p/q is the interval quotient).  Tests check containment of the exact values (2431 integers, 2000 random rationals, all certifier tables); a regression test shows that the old pattern does not contain 25! at 53 bits. |
| G7 | Decisions on floats; `min_at`, `wmin`, `ptail` stored as floats (ptail underflowed to 0.0 for d >~ 1865, so the old audit's ptail filter was vacuous there). | All decisions are exact comparisons of interval endpoints (mpmath `mpf_lt`/`mpf_gt` on raw endpoints).  P(E^c) and eps_t are carried as logarithms; every bound is stored as an exact decimal string; the audit works with Fractions and intervals, and compares tiny quantities through logarithms. |

Further items found in a second review of `verify_gauss.py` / `verify_fixedpoint.py` (all closed in `verify_cert.py`):

| item | in the old code | now |
|---|---|---|
| zeta values | `mp.zeta(s)` at PREC+40 bits widened by a relative 2^-PREC: relies on mpmath's accuracy claim, not an enclosure. | zeta(s), 2 <= s <= 17, by Euler-Maclaurin in exact rational arithmetic with its remainder bound (section 4.3); width <= 5.5e-48; tests against 1200-bit values and, for even s, the Bernoulli formula. |
| Bernoulli numbers | `mpmath.bernfrac` (exact in practice). | Exact Fraction recurrence; test: identical to `bernfrac` for B_0..B_140. |
| regular part F_r^(k), k <= 8 | Bell polynomials in the logarithmic derivatives of (b)_i; tail with the float `max(1, i/mm)` and an ad hoc cut-off of the tail sum at i < IMAX + 600 plus 2^-(IMAX+500) (valid: the omitted part is smaller than 2^-(IMAX+500) by a factor > 250 for IMAX = 121 and 141, but this was not justified in code). | Exact truncated products for the Taylor coefficients of (m+h)_i/(d)_i (no cancellation, all terms >= 0) for k <= 14; tail bound from p_i^(k) <= k! C(i,k)/(d)_k and a ratio test in exact rationals (section 4.2).  Test: the coefficients contain the exact rationals for 6 (d, m) pairs. |
| F_r^(k), k = 10, 12, 14 | the crude bound 8 k! d^2/(d)_k. | the exact series (k <= 14). |
| sup|F_r^(k)| <= 8 k! d^2/(d)_k (k = 1, 16) | stated without proof in the code and logs. | Proved in section 4.2 with the sharper computed constant S_k = sum_i |g_i| C(i,k): S_1 <= 1.88838, S_16 <= 0.00531 (asserted <= 8 at run time). |
| transcendental functions | mpmath `iv.sin/cos/exp/log/sqrt`, `iv.pi` as returned. | Same functions, each result widened outward by a further 16 units in the last place (guards against a last-bit error of directed rounding); tests against 1200-bit values. |
| tail block | eps_t, P(E^c) and r computed in `mp` (round to nearest); c rho = 2 eps_t held with equality at the design point; `lo = a - r` rounded to nearest, so the box need not contain [a - r, b + r]. | All tail quantities in interval arithmetic and logarithms; r = 2^e exact; lo_m, hi_m rounded outward; (D) is checked as c_D r > 2 eps_t with c_D the certified infimum (margin >= 10^0.61 = 4.1). |
| t^(3/2) | `tl ** iv.mpf(1.5)` (through exp/log). | `tl * sqrt(tl)`. |
| F_r(m) in Dlt | recovered as (F_s + F_r) - F_s (rigorous but widened). | the series value directly. |

## 4. The bounds used by the code, with proofs

Notation as in `CONE_PROOF.md`: F(b) = E Ghat(d X_b), X_b ~ Beta(b, d-b); F = F_s + F_r with F_s(b) = (4d/pi) b [psi(b+1) - psi(d+1)],
F_r(b) = d^2 E g_r(X_b); p_i(b) := (b)_i/(d)_i = E X_b^i.

### 4.1 The coefficients of g_r
g_r(x) = -(8/pi^2)[Cl2(pi x/2) + Cl2(pi - pi x/2)] - (4/pi) x log x = sum_{i odd} g_i x^i on |x| < 2, with g_1 = -(4/pi)(1 + log(4/pi))
and, for n >= 1, g_{2n+1} = 8 |B_2n| (1/2 - 4^-n) pi^(2n-1)/(2n (2n+1)!) = (8/pi) zeta(2n)(1/2 - 4^-n)/(4^n n(2n+1)).
Hence 0 < g_{2n+1} < (2 pi/3) 4^-n/(n(2n+1)) (zeta(2n) <= pi^2/6, 1/2 - 4^-n < 1/2).  The code forms the rational factor
|B_2n|(1/2 - 4^-n)/(2n(2n+1)!) exactly and multiplies by the enclosure of pi^(2n-1).

### 4.2 The regular part
p_i(b) = prod_{q<i} (b+q)/(d+q) is a polynomial in b with nonnegative coefficients, so for 0 <= b <= d and k >= 0:
0 <= p_i^(k)(b) <= p_i^(k)(d) = k! e_k(1/d, 1/(d+1), ..., 1/(d+i-1)) <= k! C(i,k)/(d)_k,
because each of the C(i,k) products in e_k has factors 1/(d+q_1) ... 1/(d+q_k) with q_j >= j-1.
(a) Taylor coefficients at integers: [h^k] p_i(m+h) is computed for k <= 14 by the recurrence
    c^(i+1)_k = (c^(i)_k (m+i) + c^(i)_{k-1})/(d+i) (exact truncated products; all terms >= 0, so no cancellation), and
    F_r^(k)(m) = d^2 sum_{i odd <= 141} g_i k! [h^k] p_i(m+h) + theta d^2 k!/(d)_k sum_{i > 141, odd} |g_i| C(i,k), |theta| <= 1.
(b) Tail: with u_n = 4^-n C(2n+1,k)/(n(2n+1)), u_{n+1}/u_n <= rho_k := (1/4)(2N0+3)(2N0+2)/((2N0+3-k)(2N0+2-k)) for n >= N0 = 71
    (x/(x-k) decreases in x; n(2n+1)/((n+1)(2n+3)) <= 1), so sum_{n >= N0} u_n <= u_{N0}/(1 - rho_k), an exact rational.
    For k = 0 the tail of F_r(m) is <= d^2 (2 pi/3) sum_{n > 70} 4^-n/(n(2n+1)) (p_i <= 1).
(c) Uniform bound: |F_r^(k)(b)| <= k! d^2 S_k/(d)_k on [0, d], S_k := sum_{i odd} |g_i| C(i,k) (explicit sum to 141 plus (b)).
    This proves the bound "8 k! d^2/(d)_k" quoted in `LOG.md` (QD2-T2) and used by the old code; the code uses the computed
    S_1 <= 1.888378 (sup|F'|) and S_16 <= 0.005306 (order-16 remainder) and asserts S_k <= 8.
    Term-by-term differentiation is justified by the same domination.

### 4.3 zeta(s) by Euler-Maclaurin
For integers s >= 2, N >= 1, K >= 1 (Concrete Mathematics (9.67) with m = 2K, b -> infinity):
zeta(s) = sum_{n<N} n^-s + N^(1-s)/(s-1) + N^-s/2 + sum_{j=1}^{K} B_2j/(2j)! (s)_{2j-1} N^(-s-2j+1) + R,
|R| <= |B_2K|/(2K)! int_N^inf |f^(2K)| = |B_2K|/(2K)! (s)_{2K-1} N^(-s-2K+1)
(f(x) = x^-s, |B_2K(x)| <= |B_2K| on [0,1], f^(2K) > 0, f^(2K-1)(inf) = 0).  All terms are exact rationals; N = 64, K = 40.
The polygamma values at integers are psi^(n)(m+1) = (-1)^(n+1) n! [zeta(n+1) - H^(n+1)_m] with interval harmonic sums.

### 4.4 The singular part of F^(16)
|psi^(n)(z)| = n! sum_{k>=0} (z+k)^-(n+1) <= n!/z^(n+1) + (n-1)!/z^n (z > 0), hence for b >= 0
|kappa_16(b)| = |16 psi^(15)(b+1) + b psi^(16)(b+1)| <= 31 * 14!/(b+1)^15 + 32 * 15!/(b+1)^16  (b/(b+1) <= 1).
F_s^(16) = (4d/pi) kappa_16.  With 4.2(c): S(rad) = sup_{|z| <= rad} |F^(16)(m+z)| is bounded with b >= m - rad >= m/4.

### 4.5 H(m,t) - F(m) and its t-derivative
H(m,t) - F(m) = E[(F(m+z) - F(m)) 1{|z| < L}], z ~ N(0,t), L = (3/4) min(m, d-m).  Taylor to order 15 with Lagrange remainder
|R16(z)| <= S |z|^16/16!; odd terms vanish by symmetry; E[z^(2j) 1{|z|<L}] = t^j (2j-1)!! - T_j.  The code encloses
sum_{j<=7} t^j F^(2j)(m)/(2^j j!) (interval in t) and bounds the rest by
sum_j |F^(2j)(m)| T_j/(2j)! + [S_near 15!! t^8 + S_far T_8(L_near)]/16!,  L_near = min(m, d-m)/2,
with T_j <= t^j 2/sqrt(2 pi) a^(2j-1) e^(-a^2/2)/(1 - (2j-1)/a^2), a = L/sqrt(t), when a^2 > 2j (integration by parts:
I_n(a) = a^(n-1) e^(-a^2/2) + (n-1) I_{n-2}(a) and I_{n-2} <= I_n/a^2), and T_j <= t^j (2j-1)!! otherwise.  Every error term
increases with t, so it is evaluated at the upper end of the t-interval.
For (D): d/dt E[z^(2j) 1{|z|<L}] = j t^(j-1)(2j-1)!! - T_j' with 0 <= T_j' <= j t^(j-1) m_j(a) + L^(2j+1) phi(a)/t^(3/2), and,
by d/dt phi_t = phi_t''/2 and two integrations by parts on [-L, L],
|d/dt E[R16(z) 1{|z|<L}]| <= (1/2)[S t^7 13!!/14! + phi_t(L)(S L^16/16! 2L/t + 2 S L^15/15!)];
on a t-interval the code uses a = L/sqrt(t_hi), phi(a) at that a, and 1/t at t_lo (all worst cases).

### 4.6 Tails (Lemma R4) in logarithms
sup_{(0,d)} |F'| <= (4d/pi)(H_d + 1) + d S_1 (F_s'(b) = (4d/pi)[psi(b+1) - psi(d+1) + b psi'(b+1)], -H_d <= psi(b+1) - psi(d+1) <= 0,
0 <= b psi'(b+1) <= 1; |F_r'| <= d S_1 by 4.2(c)).  log P(E^c) <= log(2d) - 9/(32 Phi(1)) with Phi(1) <= hi_1;
log eps_t <= log(3d/8) + log sup|F'| + log P(E^c).  All in interval arithmetic; mpmath numbers have no exponent limit, and the
JSON stores the logarithms (no underflow at d = 2000, where eps_t ~ 10^-369).

## 5. Tests (`python test_verify_cert.py`, `logs/test_verify_cert.log`)

Every exact constant is checked to be CONTAINED in its interval (exact rational comparison of the endpoints), every transcendental value against a 1200-bit mpmath value, the tail bounds against exact partial sums, and the enclosures of F, F'' and H - F against direct quadrature (consistency checks; the quadrature is not rigorous).  The last test runs the previous implementation (`verify_gauss.py` up to the root boxes, 160 bits, d = 203: Bell polynomials, harmonic-sum logarithmic derivatives) and checks that its enclosures of F^(2j)(m), j <= 4, and of tau_m overlap the new ones for every m: an independent code path for the regular part.  The H - F test agrees to 1.1e-16, the size of the first omitted Gaussian term t^8 F^(16)/(2^8 8!) at m = 6, t = 0.05 (the enclosure contains it through the remainder bound).

```
PASS  integers -> intervals contain the exact integer (factorials to 200!, n!!, C(i,k), (d)_k, 2^j j!)  2431 values
PASS  certifier tables FACT, TCO, DFF, FACT2J, 13!!, 15!! contain the exact integers
PASS  rationals -> intervals contain the exact rational
PASS  regression (G6): iv.mpf(mpmath.factorial(25)) at 53 bits does NOT contain 25! (the old pattern)
PASS  Bernoulli numbers (exact recurrence) agree with mpmath.bernfrac  B_0..B_140
PASS  zeta(s), 2 <= s <= 17: Euler-Maclaurin enclosures contain zeta(s) (1200-bit reference; even s also B_2n formula)  max width 5.5e-48
PASS  pi, sqrt(2 pi), sin, cos, exp, log, sqrt (widened) contain the 1200-bit values  300 random arguments
PASS  g_i (i <= 141) contain (8/pi) zeta(2n)(1/2 - 4^-n)/(4^n n(2n+1)); bound |g_i| <= (2pi/3)4^-n/(n(2n+1)) holds
PASS  g_r(1) enclosure (series + tail) contains -16 G/pi^2  width 2.3e-46
PASS  g_r(0.7) by the series contains the Clausen-function value
PASS  tail sums: sum_{n>NSER} 4^-n C(2n+1,k)/(n(2n+1)) <= gtail_frac(k), k = 0..16 (exact partial sums)
PASS  S_1, S_16 <= 8 (the constant of |F_r^(k)| <= 8 k! d^2/(d)_k)  S_1 <= 1.888378, S_16 <= 5.305e-03
PASS  fr_series: truncated-product coefficients contain the exact [h^k] (m+h)_i/(d)_i (k <= 14)  6 (d,m)
PASS  F_r tail bound and p_i^(k)(m) <= k! C(i,k)/(d)_k hold (exact p_i^(k), i up to IMAX + 40)
PASS  |F_r^(k)(b)| <= k! d^2 S_k/(d)_k at non-integer b (k = 1, 16; numerical)
PASS  psi^(n)(m+1) = (-1)^(n+1) n! [zeta(n+1) - H^(n+1)_m] and kappa_k enclosures contain the 1200-bit values (d = 300)
PASS  |psi^(n)(z)| <= (n-1)!/z^n + n!/z^(n+1) and the kappa_16 bound (spot values)
PASS  E[z^(2j) 1{|z| >= L}] <= trunc_mom_ub and m_j(a) <= mj_ub, j = 1..8, incl. the fallback branch (G3)  20 fallback cases tested
PASS  raw_to_dec gives the exact value of the endpoint (3000 random intervals, round trip through Fraction)
PASS  F(m), F''(m) at d = 201 agree with direct Beta-density quadrature (40 digits)  deviations 8.3e-39 1.8e-39 3.4e-37 5.2e-40 1.0e-36 1.1e-40 1.5e-37 3.2e-40
PASS  H(m,t) - F(m) (order-14 expansion + remainders) agrees with Gauss-Hermite x Beta quadrature (d = 201, m = 6, t = 0.05)  deviation 1.1e-16
PASS  previous implementation (verify_gauss.py head, 160 bits, d = 203): F^(2j)(m), j <= 4, and tau_m enclosures overlap
22/22 tests passed  [105s]
```

## 6. The run

`bash start_cert.sh 14 201 2000` started 14 workers (`run_cert.sh w 14`, worker w takes d = w mod 14) with nohup; their PIDs are in
`logs/run_cert_pids.txt`.  Before that, 26 values of d spread over the whole range (201, 202, 203, 250, 299, 300, 301, 400, 451,
500, 599, 600, 601, 700, 800, 999, 1000, 1001, 1200, 1499, 1500, 1501, 1750, 1998, 1999, 2000) were run with the same file
(`logs/run_cert_sample.log`); all certified, and the sweep skipped them.  The workers ran from 05:30 to 06:22 (52 minutes wall
clock, 14 processes); the run time of one d under that load was 3.3 s (d = 202) to 62 s (d = 1667), 11.9 h in total.  A single
unloaded run takes 3 s at d = 201 and 26 s at d = 2000 (`verify_gauss.py` alone took 23 s and 171 s, and
`verify_fixedpoint.py` repeated its first part).  No run failed, timed out or wrote an error file
(`logs/cert_g_err_d*.txt`: none); every line of `logs/run_cert_w*.log` reads `CERTIFIED=True`.  Determinism: rerunning d = 201
and d = 1000 in a separate process reproduces the stored certificates exactly, `box_sha256` included.

## 7. Final audit (`python audit_cert_g.py`, `logs/audit_cert_g_final.log`)

```
verify_cert.py sha256 = ff56740d15d40a07c99deb6433fb1b0f40b5a2d5b356b3ec9da0270ff1fab6a7
certificates 201..2000: 1800/1800 OK; missing 0 []; failed 0 []
margins (lower endpoints; argmin d):  d^2 min at_k = 0.0631932 (even d, d = 2000), 0.126387 (odd d, d = 1999);  d min Delta^2 W = 0.660025 (d = 201)
  (D): min inf Hc'/(c1min/4) = 4.00099 (d = 2000);  min log10[c_D r/(2 eps_t)] = 0.616942 (d = 201);  min log10[|face value|/(2 eps_t)] = 16.7768 (d = 201)
  tails: max log10 eps_t = -31.1695 (d = 201);  min log10[min Delta^2 W/(4 eps_t)] = 28.0838 (d = 201);  truncation-moment fallbacks used: 0
  constants: S_1 <= 1.8883784297, S_16 <= 0.0053051640, g_r(1) tail <= 4.933e-47
  total certifier time 11.86 h
previous logs [vg/fp]: min d^2 at_k = 0.0632 (even) / 0.1264 (odd), min d w = 0.6600, min (D) ratio = 4.0010
previous logs [100-bit backup]: min d^2 at_k = 0.0285 (even) / 0.0798 (odd), min d w = 0.6336, min (D) ratio = 4.0033
  new/old - 1 vs 100-bit backup 201-600 (400 d): min at_k [-1.11e-04, +1.22e+00], min Delta^2 W [+3.10e-06, +4.87e-02], (D) ratio [+1.31e-10, +5.90e-09]
  new/old - 1 vs vg/fp 201-600 (400 d): min at_k [-1.11e-04, +1.21e-04], min Delta^2 W [+1.49e-06, +2.13e-05], (D) ratio [+1.31e-10, +5.90e-09]
  new/old - 1 vs vg/fp 601-2000 (1400 d): min at_k [+2.59e-06, +7.23e-05], min Delta^2 W [+4.93e-07, +7.76e-06], (D) ratio [+3.78e-12, +2.65e-10]
ALL CERTIFIED
```

## 8. Comparison with the previous logs

`STATUS_L4.md` section 7.2 quotes d^2 min at_k >= 0.0285 (even d) / 0.0798 (odd d) and d min Delta^2 W >= 0.6336.  These
numbers come from the 100-bit runs of 2026-10-01 for 201 <= d <= 600 (now in `logs/backup_prec100/`; at 100 bits the harmonic-sum
accumulation in psi^(n)(m+1) = zeta - H_m widens the enclosures).  Those logs were regenerated at 160 bits on 2026-10-02
(`run_redo160.sh`), and the present `vg`/`fp` logs give 0.0632 / 0.1264 / 0.6600 (`python audit_certs.py 2000`, read only).  The
new certificates give 0.0631932 / 0.126387 / 0.660025.  The audit compares, for every d, the new lower bounds with the old
logged values (`new/old - 1`):

| reference | d | min at_k | min Delta^2 W | (D) ratio |
|---|---|---|---|---|
| current `vg`/`fp` logs | 201-600 | [-1.11e-4, +1.21e-4] | [+1.49e-6, +2.13e-5] | [+1.3e-10, +5.9e-9] |
| current `vg`/`fp` logs | 601-2000 | [+2.59e-6, +7.23e-5] | [+4.93e-7, +7.76e-6] | [+3.8e-12, +2.7e-10] |
| 100-bit backups | 201-600 | [-1.11e-4, +1.22] | [+3.10e-6, +4.87e-2] | [+1.3e-10, +5.9e-9] |

The (D) ratio agrees to 6e-9 everywhere (the derivative enclosure is the same mathematics, now on one box).  The slack lower bounds
are slightly higher than before (F_r^(10..14) from the exact series instead of crude bounds; F_r(m) used directly).  The at_k
lower bounds differ by at most 1.2e-4 relative, in both directions for d <= 600: the lower endpoint is the value at the box
centre minus about (2/d) sum_m width_m, and the root boxes come from different (untrusted) searches, which stop at slightly
different points; for d > 600 the old enclosures were wider (crude F^(10..14) bounds) and the new bounds are higher.  The widening
by r <= 1.01e-28 is invisible at this scale.  The new minimum is attained at k = floor(d/2) for every d and the slack minimum at
m = floor(d/2); the old logs have k = (d-3)/2 for 273 odd d >= 1455, where the two neighbouring frequencies agree to within the
enclosure widths (e.g. d = 1999: old 0.12638616 at k = 998, new 0.12638653 at k = 999).  Selected values (old = `vg_d{d}.json` / `fp_d{d}.json`, new = `cert_g_d{d}.json`):

| d | d^2 min at_k old | new | d min Delta^2 W old | new | (D) ratio old | new | r | log10 eps_t |
|---|---|---|---|---|---|---|---|---|
| 201 | 0.1273229 | 0.1273211 | 0.6600148 | 0.6600246 | 4.0094582 | 4.0094583 | 2^-94 | -31.1695 |
| 202 | 0.0636273 | 0.0636316 | 0.6600530 | 0.6600559 | 4.0095791 | 4.0095791 | 2^-95 | -31.3522 |
| 300 | 0.0635145 | 0.0635200 | 0.6622035 | 0.6622055 | 4.0065511 | 4.0065511 | 2^-100 | -49.3899 |
| 600 | 0.0633343 | 0.0633385 | 0.6644297 | 0.6644308 | 4.0032958 | 4.0032958 | 2^-100 | -105.314 |
| 601 | 0.1266769 | 0.1266775 | 0.6644312 | 0.6644349 | 4.0032900 | 4.0032900 | 2^-100 | -105.501 |
| 1000 | 0.0632532 | 0.0632563 | 0.6653231 | 0.6653239 | 4.0019808 | 4.0019808 | 2^-100 | -180.442 |
| 1001 | 0.1265121 | 0.1265126 | 0.6653227 | 0.6653254 | 4.0019788 | 4.0019788 | 2^-100 | -180.630 |
| 1500 | 0.0632122 | 0.0632143 | 0.6657706 | 0.6657710 | 4.0013216 | 4.0013216 | 2^-100 | -274.668 |
| 1999 | 0.1263862 | 0.1263865 | 0.6659932 | 0.6659945 | 4.0009921 | 4.0009921 | 2^-100 | -368.864 |
| 2000 | 0.0631914 | 0.0631932 | 0.6659944 | 0.6659948 | 4.0009916 | 4.0009916 | 2^-100 | -369.053 |

The old box radius was r = max(8 eps_t/c1min, 1e-30) (7.7e-29 at d = 201); the new one is the next power of two
(2^-94 = 5.0e-29 at d = 201, since the new sup|F'| bound uses S_1 = 1.89 instead of 8), with the floor 2^-100 = 7.9e-31.

## 9. Trusted base and scope

* Trusted: Python 3.14.3 integers and `fractions.Fraction`; mpmath 1.3.0 (gmpy backend) interval arithmetic: outward-rounded
  +, -, *, /, integer powers, conversion of Python integers, and the interval elementary functions `iv.sin`, `iv.cos`,
  `iv.exp`, `iv.log`, `iv.sqrt`, `iv.pi` (whose results are additionally widened by 16 ulp).  Floats occur nowhere in the
  certified path; the untrusted root search uses 200-bit mpmath numbers only to propose candidate points.
* On paper (unchanged): Lemmas R1-R4 and Lemma B of `CONE_PROOF.md` (including continuity of Phi -> Pi_Phi on Q and the
  Poincare-Miranda theorem), and the bounds of section 4 (written out here).
* Scope: 201 <= d <= 2000 only.  The LP certificates for d <= 200 and the analytic regime d >= 2001 (`a01`-`a12`,
  `audit_alld.py`, `CONE_ALLD_PROOF.md`) are not touched by this note.

## 10. Reproduction

From `QD2/` with Python 3.14 (mpmath 1.3.0):
`python test_verify_cert.py` (about 2 minutes); `python verify_cert.py d` for one d (3 s at d = 201, 26 s at d = 2000);
`bash start_cert.sh 14 201 2000` for the sweep (skips existing `logs/cert_g_d{d}.json`); `python audit_cert_g.py`.
A rerun reproduces the stored `box_sha256` and all bounds exactly (deterministic code; same mpmath version).
