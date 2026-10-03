# Re-verification report B: from-scratch re-check of the noise theorem of OQP 27B (Gill's uniform-outcome noise)

Date 2026-10-02. Independence: `noise-literal/` was opened only after steps 1-5 were completed with independent code
(order recorded in ). Overall verdict: **CONFIRMED -- no error, no gap.** DKZ does not have the
highest resistance to Gill's literal uniform-outcome noise on Phi_d, for every d >= 4.

## 0. Verdicts
| # | Claim | Verdict | Status | Evidence |
|---|---|---|---|---|
| i-a | C_d is a valid quantum behaviour on Phi_d (PVMs, zero effects allowed, ranks as stated) | CONFIRMED | PROVED (exact) | build_behaviours.py |
| i-b | coarse-grained CHSH valid on L(2,2,d); violated iff v > v_even(d) (even) / v_odd(d) (odd) | CONFIRMED | PROVED | sec. 2.1-2.2 |
| i-c | v_c(C_d) equals that threshold exactly (CHSH witness optimal) | CONFIRMED for every d >= 2 by a NEW explicit local model | PROVED | sec. 2.3-2.5 |
| ii-a | DKZ_d valid on Phi_d; CGLMP(DKZ_d) = I_ME(d); v_c(DKZ_d) <= 2/I_ME(d) | CONFIRMED | PROVED | build_behaviours.py |
| ii-b | 1/2-lemma | CONFIRMED; the constant 1/2 is sharp (PR_d box) | PROVED | sec. 3 |
| ii-c | the lemma settles exactly the d with threshold < 1/2, i.e. every d >= 10 | CONFIRMED | PROVED | sec. 3.3 |
| ii-d | v_c(DKZ_d) > threshold for d = 4..9 | CONFIRMED by independent certificates | PROVED | sec. 4 |
| main | v_c(DKZ_d) > v_c(C_d) for every d >= 4 | CONFIRMED | PROVED | sec. 5 |

## 1. Behaviours
Conventions: x, y in {0,1}; a, b in Z_d; L_d = convex hull of the d^4 deterministic behaviours; u = 1/d^2;
v_c(p) = max{v in [0,1] : v p + (1-v) u in L_d} (attained, L_d closed); local post-processing preserves locality.
Competitor: real qubit projectors, outcome 0 = |theta><theta| with theta_A0 = 0, theta_A1 = pi/4, theta_B0 = pi/8,
theta_B1 = -pi/8 (entries in Q(sqrt2)); even d: P (x) 1_{d/2} on outcomes 0, 1; odd d: the block construction (extra
dimension on outcome 1). Exact checks over Q(sqrt2), d = 2..9: real symmetric idempotent effects summing to 1_d; ranks
(d/2, d/2, 0, ...) / ((d-1)/2, (d+1)/2, 0, ...); even d: p_C = P_CHSH with P_CHSH(a,b|x,y) = (1 + (-1)^{a+b+xy}/sqrt2)/4
on {0,1}^2 and 0 elsewhere; odd d: p_C = ((d-1)/d) P_CHSH + (1/d) delta_(1,1).
DKZ_d: |k>_{A,x} = d^{-1/2} sum_j w^{j(k+alpha_x)}|j>, |l>_{B,y} = d^{-1/2} sum_j w^{j(-l+beta_y)}|j>, alpha = (0, 1/2),
beta = (1/4, -1/4); p(k,l|x,y) = 1/(2 d^3 sin^2(pi(k - l + alpha_x + beta_y)/d)); checked exactly in Q(zeta_{4d}) for
d = 2..9; CGLMP value = I_ME(d) to 30 digits (d = 3..9); hence v_c(DKZ_d) <= 2/I_ME(d).

## 2. Competitor
2.1 Validity: pi(0) = 0, pi(n) = 1 (n >= 1), E_xy = sum (-1)^{pi(a)+pi(b)} p(a,b|x,y), S = E00 + E01 + E10 - E11. On a
deterministic strategy S = A0(B0 + B1) + A1(B0 - B1) = +-2; S is linear, so S <= 2 on L_d (also checked on all d^4
deterministic strategies for d = 2..12).
2.2 Threshold: S(u) = 2c with c = (d-2)^2/d^2; S(P_CHSH) = 2 sqrt2; S(delta_(1,1)) = 2. S(v p_C + (1-v) u) is affine
in v with positive slope; violation iff v > v_thr, v_thr = 4(d-1)/(4(d-1) + (sqrt2-1) d^2) (even d) and
4/(4 + (sqrt2-1) d) (odd d; uses d^2 - 5d + 4 = (d-1)(d-4)); verified symbolically.
2.3 Reduction to three outcomes: merging outcomes 2..d-1 (Gamma) and re-randomising them uniformly (Ref) are local
post-processings with q_v = Ref(Gamma(q_v)); hence locality of q_v is equivalent to locality of
R_v = v P + (1-v) nu (x) nu in L_3, nu = (s, s, 1-2s), s = 1/d.
2.4 Theorem (explicit local model at the threshold). For s in (0, 1/2] let T(s) = 4s(1-s)/(sqrt2 - (1-2s)^2); at
v = T(s) put rho = (1-v)(1-2s), sig = (1-v)(1-2s)^2. The mixture of
 (1) weight sig: all four outputs *;
 (2) weight (rho - sig)/2 for each of the 4 single-star patterns and each root r in {0,1}: A0 = *: (A1, B0, B1) =
     (r, r, 1-r); A1 = *: (A0, B0, B1) = (r, r, r); B0 = *: (A0, A1, B1) = (r, 1-r, r); B1 = *: (A0, A1, B0) = (r, r, r);
 (3) weight pi0/8 for each of the 8 deterministic {0,1} strategies with sum_xy s_xy (-1)^{a_x + b_y} = 2,
     s = (1, 1, 1, -1), pi0 = 1 - 4 rho + 3 sig,
is a local model of R_{T(s)} with P = P_CHSH. Link-by-link: (*,*) only in (1) with weight sig = target; (*, b) only in
the pattern with the star at A_x, weight (rho - sig)/2 = (1-v)(1-2s)s = target; for (a,b) in {0,1}^2 the entry is
[v + 4(1-v)s^2]/4 + (-1)^{a+b} s_xy (1 - sig)/8 versus the target v(1 + (-1)^{a+b} s_xy/sqrt2)/4 + (1-v)s^2: equal iff
1 - (1-v)(1-2s)^2 = sqrt2 v iff v = T(s). Nonnegativity: sig >= 0; rho - sig = 2s(1-v)(1-2s) >= 0;
pi0 = 4s[(1-s) - (sqrt2-1)(1-3s)]/(sqrt2 - (1-2s)^2) > 0 (for s <= 1/3, (sqrt2-1)(1-3s) < 1-3s <= 1-s; for s > 1/3 the
bracket's second term is negative). QED
2.5 Corollary: v_c(C_d) = v_thr(d) exactly for every d >= 2. Even d: T(1/d) = v_even(d). Odd d:
R_v = v s delta_(1,1) + (1 - vs)[v'' P_CHSH + (1 - v'') nu (x) nu], v'' = v(1-s)/(1 - vs), and
v_odd (1-s)/(1 - v_odd s) = T(s) identically; the delta term is deterministic. Independent exact full-scenario check
(not using 2.3), d = 2..12: model weights in Q(sqrt2), all >= 0; entry-by-entry equality with v_thr p_C + (1 - v_thr) u;
coarse CHSH exactly 2 at v_thr. Float LP cross-check (full polytope d = 3..8, reduction d = 3..9): agreement to 3e-16.
v_thr: d = 4: 0.644212, 5: 0.658863, 6: 0.572874, 7: 0.579753, 8: 0.513670, 9: 0.517604, 10: 0.464988, 11: 0.467489.

## 3. The 1/2-lemma
3.1 Lemma: for every no-signalling p, (p + p_A (x) p_B)/2 is local; with uniform marginals p_A (x) p_B = u, so
v_c(p) >= 1/2. Proof: M1 draws (A0, B0) ~ p(.,.|0,0) and (A1, B1) ~ p(.,.|1,1) independently (links 01, 10 become
products of marginals, well defined by no-signalling); M2 does the same with links 01 and 10; (M1 + M2)/2 equals
(p + p_A (x) p_B)/2 link by link. For v <= 1/2, v p + (1-v) u = 2v (p+u)/2 + (1-2v) u. QED (exact check on random
rational behaviours, d = 2..5).
3.2 Sharp: PR_d(a,b|x,y) = [b - a = x(1-y) mod d]/d has uniform marginals and CGLMP value 4, so v_c(PR_d) = 1/2
(checked d = 2..9).
3.3 Even d: v_even(d) < 1/2 iff (sqrt2-1) d^2 - 4d + 4 > 0 iff d > 8.524; odd d: v_odd(d) < 1/2 iff d > 4(sqrt2+1)
= 9.657. So the lemma covers exactly d >= 10 (exact sign test d = 2..199); remaining d = 4..9.

## 4. Independent lower bounds on v_c(DKZ_d)
4.1 Cyclic reduction: p_DKZ(a,b|x,y) = f_xy(b-a)/d, f_xy(n) = 1/(2 d^2 sin^2(pi(n - g_xy)/d)), g = (1/4, -1/4, 3/4, 1/4)
for xy = 00, 01, 10, 11; C_d = {k in Z_d^4 : k00 + k11 = k01 + k10 mod d}. Any distribution W on C_d with marginals
T_xy = v f_xy + (1-v)/d gives a local model (hidden variable (g, k), g uniform independent of k: alpha_0 = g,
alpha_1 = g + k00 - k10, beta_0 = g + k00, beta_1 = g + k01; then beta_y - alpha_x = k_xy).
4.2 Cyclic 1/2-lemma: for any link distributions g_xy, (g + unif)/2 is realised on C_d.
4.3 Certificate theorem: W >= 0 rational, t = sum W < 1, T - AW >= (1-t)/(2d) entrywise => T realised on C_d =>
v DKZ + (1-v) u local. Lower bounds on f computed two independent ways (mpmath intervals; pure fractions with pi to 50
decimals and alternating Taylor series for sin).
4.4 Results (stand-alone verifier: ALL CERTIFICATES VALID): certified v = 863/1250 (d = 4), 687/1000 (5), 6847/10000
(6), 6831/10000 (7), 6819/10000 (8), 6809/10000 (9), each > v_thr(d) (exact comparison); tight certificates within 2e-6
of 2/I_ME(d) for d = 3..12; cyclic and full LP agree (float) for d = 3..7.

## 5. Conclusion
Theorem: for every d >= 4, v_c(DKZ_d) > v_c(C_d) = v_thr(d) (d >= 10 by sec. 3; d = 4..9 by sec. 4.4). For Gill's
literal noise, the DKZ measurements do not give the highest noise resistance on Phi_d, for every d >= 4.
Remarks: C_d uses zero PVM effects (unused outcomes); on Phi_d requiring every outcome to occur forces rank-one PVMs,
for which u = white noise (ledger C2, not covered); with local dimension > d every outcome can occur and DKZ is still
beaten (`remark_full_support.py`). d = 3 (not part of the claim): on Phi_3 the block competitor gives 0.762974 >
0.696152; on Phi_2 the embedded CHSH box gives T(1/3) = 8/(9 sqrt2 - 1) = 0.682133 < v_c(DKZ_3) (certified >= 0.696151).
Odd d on an even local dimension: the embedded construction achieves the even formula, below v_odd(d).

## 6. Comparison with P2_literal_noise (after steps 1-5)
No mathematical discrepancy. P2's verify_theorem.py re-run: 15 items, 0 failures, 133 s, OVERALL PASS; all numbers agree
to every printed digit. D1 (labelling): extra odd-d dimension on outcome 0 (P2) vs outcome 1 (here): same v_c by the
global 0<->1 flip, both proved. D2 (convention): the beta conventions describe the same vectors. D3: exact optimality of
the witness now has a short facet-free proof (sec. 2.4), so Theorem 1(a) no longer depends on the computer-assisted
facet list (still used for P2's S1, d = 3 on Phi_3). D4: P2's certificates (two-sided absorption, v0 = 2/I_ME(d) -
1.0e-7) re-derived; all 18 (d = 3..20) VALID under independent code with both enclosure methods. D5: P2's S3c pairs
(d, D) = (4,12), (5,11), (6,12), (7,13), (8,12), (9,13) exactly correct and minimal in their family. D6 (harmless):
`exact.py` sin_pi_frac_bounds would give a slightly too small upper bound at r = 1/2 exactly; never called. D7: S1, S3b,
S4 not re-checked; S2 (Phi_2, d = 3) matches.
Recommendation: ledger A3b -> PROVED (the clause is refuted for every d >= 4 on Phi_d), crediting Acin-Durt-Gisin-
Latorre 2002 and Baek-Ryu-Lee 2025.

## 7. Files (relative to independent-check-B/)
build_behaviours.py; competitor_exact.py [D_MAX]; half_lemma.py; dkz_certificates.py [dmin dmax] (writes
certificates/dkz_d{3..12}.json); verify_dkz_certificates.py (+ .log); check_p2_certificates.py (+ .log);
p2_verify_theorem_rerun.log; remark_full_support.py; lp_tools.py (float exploration only).
