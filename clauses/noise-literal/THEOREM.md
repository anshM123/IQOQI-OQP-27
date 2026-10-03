# OQP 27B, noise clause with Gill's uniform-outcome noise and all Bell inequalities: theorem and proof

Ansh Mishra, Aryan Senthilkumar -- 2026-10-02.
Verifier: `python verify_theorem.py` (one script, about 3 minutes; prints PASS/FAIL per item; see Section 4).

**Scope.** The counterexample of Theorem 1 uses measurements with d - 2 outcomes that never occur (zero projectors), and
Proposition S3b turns it into full-rank POVMs. It does not apply to complete von Neumann measurements on Phi_d (rank-one
projectors, every outcome used), the class of Formal Conjectures issue #3444. For those measurements Gill's noise is white
noise on the state (Lemma S3a), and the clause is open for d >= 4; it holds for d = 3 (Theorem 3).

---------------------------------------------------------------------------------------------------------------------

## 0. Setting, notation, conventions

* Scenario (2,2,d): settings x, y in {0,1} (x = 0, 1 are A_1, A_2 of CGLMP; y = 0, 1 are B_1, B_2), outcomes in
  Z_d = {0, ..., d-1}. A behaviour is p = (p(a,b|x,y)); L = L(2,2,d) is the local polytope, the convex hull of the
  d^4 deterministic behaviours delta_lambda(a,b|x,y) = [a = a_x][b = b_y], lambda = (a_0, a_1, b_0, b_1).
* Gill's noise ("completely random, uniform outcomes"): u(a,b|x,y) = 1/d^2.
* Critical visibility: v_c(p) = max{ v in [0,1] : v p + (1-v) u in L }. The set of such v is a closed interval
  [0, v_c(p)] (L is closed and convex and u is local, being a product behaviour), so v p + (1-v) u is local for
  v <= v_c(p) and nonlocal for v > v_c(p). A strategy is MORE resistant to noise when its v_c is SMALLER (its
  violation survives more admixture 1 - v of noise); the clause asserts that DKZ minimises v_c.
* Projective strategy on Phi_D = D^{-1/2} sum_i |ii>: projection-valued measures {P^x_a}_a, {Q^y_b}_b on C^D
  (zero projectors allowed), p(a,b|x,y) = <Phi_D| P^x_a (x) Q^y_b |Phi_D> = Tr((P^x_a)^T Q^y_b)/D.
* CGLMP expression I_d exactly as in the mathematical paper (papers/math, eq. (1)); local bound 2; I_d(u) = 0.
  I_ME(d) = 4/(d(d-1)) sum_{j=1}^{d-1} (d-j) sec(pi j/(2d)).
* DKZ_d (D = d): Alice |a>_x = d^{-1/2} sum_k w^{k(a + alpha_x)} |k>, Bob |b>_y = d^{-1/2} sum_k w^{-k(b + beta_y)} |k>,
  w = e^{2 pi i/d}, alpha = (0, 1/2), beta = (-1/4, 1/4). (This is the orientation in which the CGLMP expression of
  the mathematical paper takes the value I_ME(d); any relabelling of outcomes/settings/parties has the same v_c, because
  relabellings map L onto L and fix u.)
* Numbers: sqrt2 - 1 = 0.41421...;
      v_even(d) = 4(d-1) / ((sqrt2 - 1) d^2 + 4(d-1)),        v_odd(d) = 4 / ((sqrt2 - 1) d + 4).

---------------------------------------------------------------------------------------------------------------------

## 1. Core theorem

**Competitor C_d (projective, on Phi_d).** Let A_0 = sigma_z, A_1 = sigma_x, B_0 = (sigma_z + sigma_x)/sqrt2,
B_1 = (sigma_z - sigma_x)/sqrt2 (the optimal CHSH qubit observables) and Pi^x_{+-} = (1 +- A_x)/2,
Pi'^y_{+-} = (1 +- B_y)/2 (real symmetric rank-one projectors on C^2).

* even d: identify C^d = C^2 (x) C^{d/2} by |i>|j> -> |i d/2 + j>, so that Phi_d = Phi_2 (x) Phi_{d/2}; put
  P^x_0 = Pi^x_+ (x) 1, P^x_1 = Pi^x_- (x) 1, P^x_a = 0 (a >= 2), and Q^y_b likewise with Pi'^y.
  Ranks (d/2, d/2, 0, ..., 0).
* odd d: C^d = (+)_{k=1}^{(d-1)/2} span{|2k-2>, |2k-1>} (+) span{|d-1>}; put
  P^x_0 = ((+)_k Pi^x_+) (+) |d-1><d-1|, P^x_1 = ((+)_k Pi^x_-) (+) 0, P^x_a = 0 (a >= 2), and Q^y_b likewise.
  Ranks ((d+1)/2, (d-1)/2, 0, ..., 0). (The extra dimension gives the deterministic outcome 0 to every
  measurement; outcome 1 instead gives the same v_c, by the 0 <-> 1 symmetry; checked in competitor.py.)

**Theorem 1.** Let d >= 4 and D = d.

(a) v_c(C_d) = v_even(d) for even d and v_c(C_d) = v_odd(d) for odd d. For v > v_c(C_d) the noisy behaviour
    v p + (1-v) u violates the coarse-grained CHSH inequality (outcome 0 -> +1, outcomes 1, ..., d-1 -> -1, for all
    four measurements; sum_xy s_xy E_xy <= 2 with s = (s_00, s_01, s_10, s_11) = (1, 1, 1, -1)); at v = v_c(C_d) it
    is local. In particular this coarse-grained CHSH inequality is an optimal witness for C_d.

(b) For every d >= 2: v_c(DKZ_d) >= 1/2. For d = 4, ..., 9: v_c(DKZ_d) >= r(d) with
        r(4) = 69/100, r(5) = 687/1000, r(6) = 171/250, r(7) = 683/1000, r(8) = 341/500, r(9) = 681/1000;
    more precisely v_c(DKZ_d) >= v0(d) for 3 <= d <= 20 with explicit rationals v0(d) (table below; numerically 2/I_ME(d) - v0(d) = 1.0e-7). Always
    v_c(DKZ_d) <= 2/I_ME(d), with equality for d = 3, 4, 5, 6 (Proposition 11).

(c) Consequently v_c(C_d) < v_c(DKZ_d) for every d >= 4: on the maximally entangled state Phi_d, the DKZ
    measurements do NOT realise the highest resistance of the violation of local realism (the whole polytope
    L(2,2,d)) to Gill's uniform noise. The same holds on every Phi_{kd} (C_d (x) 1_k and DKZ_d (x) 1_k have the
    behaviours of C_d and DKZ_d).

**Corollary 2 (other local dimensions).** Let d >= 3 and let D be even. The strategy "CHSH qubit PVMs (x) 1_{D/2}"
on Phi_D (outcomes 0, 1 with ranks D/2, D/2; outcomes 2, ..., d-1 unused) has v_c = v_even(d) exactly (Proposition 5
with q = CH covers t = 1/d for all d >= 3), and v_even(d) < v_c(DKZ_d): for even d this is Theorem 1(c); for odd
d >= 5, v_even(d) < v_odd(d) (since d^2 > d(d-1)) and Theorem 1(c) applies; for d = 3 see Supplement S2.

| d | v_c(C_d) (exact) | r(d) | certified v0(d) <= v_c(DKZ_d) | 2/I_ME(d) >= v_c(DKZ_d) |
|---|---|---|---|---|
| 4 | v_even = 0.644211701564 | 0.69 | 0.690549638999 | 0.690549739488 |
| 5 | v_odd = 0.658862678520 | 0.687 | 0.687156473999 | 0.687156574416 |
| 6 | v_even = 0.572874043197 | 0.684 | 0.684883650999 | 0.684883751130 |
| 7 | v_odd = 0.579752581421 | 0.683 | 0.683255804999 | 0.683255905411 |
| 8 | v_even = 0.513670345675 | 0.682 | 0.682032857999 | 0.682032958173 |
| 9 | v_odd = 0.517603563835 | 0.681 | 0.681080610999 | 0.681080711104 |
| 10 | v_even = 0.464987979410 | (1/2 suffices) | 0.680318219999 | 0.680318320061 |
| 11 | v_odd = 0.467489102303 | (1/2 suffices) | 0.679694094999 | 0.679694195121 |
| 12..20 | v_even / v_odd < 0.43 | (1/2 suffices) | 2/I_ME - 1.01e-7 (certificates/dkz_d12..20.json) | |
| d -> inf | ~ 4/((sqrt2 - 1) d) -> 0 | | >= 1/2 | -> pi^2/(16 G) = 0.67344 |

(The v0 column is printed by `python dkz_cert.py check 3 4 ... 20`; v_c(C_d) values are exact algebraic numbers.)

**Scope of the construction (what it needs).** C_d uses d-2 zero projectors per measurement ("unused outcomes").
Gill's noise still puts weight 1/d on each unused outcome; this is what lets the cheap 2-outcome CHSH structure beat
DKZ. On Phi_d, a PVM in which every outcome has nonzero probability has d nonzero orthogonal projectors on C^d, hence
is rank-one, and then u coincides with white noise on the state (tr P^x_a tr Q^y_b / d^2 = 1/d^2); for such
strategies the question is ledger C2 and is NOT addressed by Theorem 1. With POVMs, unused outcomes can be avoided
(Supplement S3). Edge cases: d = 2 (no outcome to fuse; the clause holds: CHSH(u) = 0 and Tsirelson give v_c >= 1/sqrt2
= v_c(CHSH)); d = 3: on Phi_3 the competitor gives v_odd(3) = 4/(3 sqrt2 + 1) = 0.76297 > 2/I_ME(3) and the clause
in fact holds on Phi_3 (Supplement S1), whereas on Phi_2 it fails (Supplement S2).

**Prior work and credit.** Numerical full-polytope noise thresholds of the DKZ (CGLMP-optimal) measurements on Phi_d
go back to Kaszlikowski, Gnacinski, Zukowski, Miklaszewski, Zeilinger, PRL 85, 4418 (2000) (N <= 9), Durt,
Kaszlikowski, Zukowski, PRA 64, 024101 (2001) (OQP ref. [2], N <= 16) and Collins, Gisin, Linden, Massar, Popescu, PRL
88, 040404 (2002), eq. (23); Gruca, Laskowski, Zukowski, PRA 85, 022118 (2012) recomputed them by exhaustive LP numerics
(d <= 5) and found that Schmidt-rank-2 states are the most noise-robust; Chen, Kaszlikowski, Kwek, Oh, Zukowski, PRA 64,
052109 (2001) gave an analytical result for N = 3 (we did not check whether it contains a local model, so the novelty of
our d = 3 lower bound is uncertain). The threshold v_even(d) = (2 - n_d)/(2 sqrt2 - n_d), n_d = 2(1 - 2/d)^2, is the
critical visibility of the CHSH strategy on a Schmidt-rank-2 maximally entangled state embedded in C^d (x) C^d in
Acin, Durt, Gisin, Latorre, PRA 65, 052325 (2002), eq. (14) (state-optimised setting; there the settings have two
outcomes, so exactness is elementary, whereas exactness in the d-outcome scenario is our Proposition 5); the same
behaviour is produced on Phi_d itself by C_d for even d. Baek, Ryu, Lee, "Robustness measures for quantifying
nonlocality", arXiv:2311.07077 (New J. Phys. 27, 053001 (2025)), observed numerically (linear programming) that the
white-noise robustness R_w = (1 - v_c)/v_c of CGLMP correlations on maximally entangled states increases under local
output coarse-graining: R_w = 0.448 for d = 4 versus 0.552 after merging outcomes, and a chain 0.4755 -> 0.6216 ->
1.0243 -> 1.7673 for d = 16 (their Table 2). These values agree with ours: (1 - 2/I_ME(4))/(2/I_ME(4)) = 0.44812,
(1 - v_even(4))/v_even(4) = 0.55229 and (1 - v_even(16))/v_even(16) = 1.76731; so the fact that merged-outcome strategies
beat DKZ on Phi_4 and Phi_16 under uniform noise was already visible numerically there. The (2,2,3) facet classes are
those of Collins and Gisin, J. Phys. A 37, 1775 (2004). New here, as far as we found: an exact theorem for every d >= 4
on Phi_d (including odd d, via the block construction), the exact critical visibility of the competitor for every d (the
coarse-grained CHSH is an optimal witness in the d-outcome scenario), rigorous lower bounds on DKZ's critical
visibility against the full local polytope (and its exact value for d = 3, 4, 5), and the d = 3 dichotomy (Phi_3
versus even D).

---------------------------------------------------------------------------------------------------------------------

## 2. Proof of Theorem 1

### 2.1 The competitor's behaviour (Lemma 1)

**Lemma 1.** Let CH(a,b|x,y) = (1 + (-1)^{a+b} s_xy/sqrt2)/4 for a, b in {0,1} and 0 otherwise. Then
p_{C_d} = CH for even d, and p_{C_d} = ((d-1)/d) CH + (1/d) delta_0 for odd d, where delta_0(a,b|x,y) = [a = b = 0].

*Proof.* All matrices are real symmetric, so (P^x_a)^T = P^x_a. For two qubit projectors,
Tr(Pi^x_{e} Pi'^y_{f})/2 = (1/8) Tr((1 + e A_x)(1 + f B_y)) = (1 + e f Tr(A_x B_y)/2)/4 with e, f = +-1, and
Tr(A_x B_y)/2 = s_xy/sqrt2 (Tr(sigma_z sigma_z) = Tr(sigma_x sigma_x) = 2, Tr(sigma_z sigma_x) = 0). Even d:
Tr((Pi (x) 1)(Pi' (x) 1))/d = (d/2) Tr(Pi Pi')/d = Tr(Pi Pi')/2. Odd d: the trace splits over the (d-1)/2 blocks and
the last dimension: ((d-1)/2) Tr(Pi Pi')/d + [a = 0][b = 0]/d. Outcomes >= 2 have zero projectors. QED
(Exact re-check from the matrices, d = 4..9: verifier item C2; ranks as stated.)

### 2.2 The coarse-grained CHSH witness (Lemma 2)

Let sigma(0) = +1, sigma(a) = -1 (a >= 1), E_xy(p) = sum_ab sigma(a) sigma(b) p(a,b|x,y),
CHSH(p) = E_00 + E_01 + E_10 - E_11.

**Lemma 2.** (i) CHSH(p) <= 2 for every p in L(2,2,d). (ii) CHSH(u) = 2(d-2)^2/d^2; CHSH(p_{C_d}) = 2 sqrt2 (even d),
((d-1)/d) 2 sqrt2 + 2/d (odd d). (iii) v p_{C_d} + (1-v) u violates (i) iff v > v_even(d) (even d), resp. v > v_odd(d)
(odd d). Hence v_c(C_d) <= v_even(d), resp. v_odd(d).

*Proof.* (i) For a deterministic behaviour, A_x = sigma(a_x), B_y = sigma(b_y) in {+-1} and
CHSH = A_0(B_0 + B_1) + A_1(B_0 - B_1) <= 2; CHSH is linear, so the bound extends to the convex hull.
(ii) Under u the binarised outcomes are independent with mean e = (1 - (d-1))/d = (2-d)/d, so E_xy(u) = e^2 and
CHSH(u) = (1 + 1 + 1 - 1) e^2. For CH, E_xy = s_xy/sqrt2, so CHSH = 4/sqrt2. delta_0 gives E_xy = 1, CHSH = 2.
(iii) CHSH(v p + (1-v) u) = v CHSH(p) + (1-v) CHSH(u) > 2 iff v > (2 - CHSH(u))/(CHSH(p) - CHSH(u)) (the denominator is
positive). With 2 - CHSH(u) = 8(d-1)/d^2: even d, CHSH(p) - CHSH(u) = (2 sqrt2 d^2 - 2(d-2)^2)/d^2 and the quotient is
4(d-1)/((sqrt2 - 1) d^2 + 4(d-1)); odd d, CHSH(p) - CHSH(u) = 2(d-1)((sqrt2 - 1) d + 4)/d^2 and the quotient is
4/((sqrt2 - 1) d + 4). QED (Symbolic re-derivation and exhaustive check of (i) for d = 4..9: item C3.)

Remark (orientation). All four noise correlators equal +e^2 > 0, and sum_xy s_xy = 2 for every sign pattern with
s_00 s_01 s_10 s_11 = -1 and one minus sign, so the noise helps the witness by +2e^2; patterns with three minus signs
would give -2e^2. The quantum CHSH value 2 sqrt2 is attained exactly with the pattern (1, 1, 1, -1) by the observables
above.

### 2.3 Reduction to three outcomes (Lemma 3)

Let pi: Z_d -> {0, 1, R}, pi(0) = 0, pi(1) = 1, pi(a) = R (a >= 2); kappa(0) = kappa(1) = 1, kappa(a) = 1/(d-2) for
a >= 2. For a behaviour p on Z_d let pi_* p denote its coarse-graining on {0,1,R}.

**Lemma 3.** Let d >= 3, let p be a behaviour with p(a,b|x,y) = 0 whenever a >= 2 or b >= 2, and p_v = v p + (1-v) u.
Then p_v in L(2,2,d) iff q_v := pi_* p_v in L(2,2,3). Moreover q_v = v q + (1-v) n_t with q = pi_* p (= p restricted to
{0,1}^2) and n_t = product behaviour with all four marginals (t, t, 1 - 2t), t = 1/d.

*Proof.* "only if": coarse-graining maps deterministic behaviours to deterministic behaviours and is linear.
"if": for a, b in Z_d one has p_v(a,b|x,y) = kappa(a) kappa(b) q_v(pi(a), pi(b)|x,y). Indeed for a, b in {0,1} this is
the definition; if a >= 2 then p(a,b|x,y) = 0, so p_v(a,b|x,y) = (1-v)/d^2 does not depend on a in {2, ..., d-1}, and
summing over those d-2 values gives q_v(R, pi(b)|x,y) (same for b >= 2, and for a, b >= 2). Given a local model
q_v = sum_lambda w_lambda delta_lambda over {0,1,R}^4, let each party answer alpha_x (resp. beta_y) if it is 0 or 1 and a
uniformly random element of {2, ..., d-1} (fresh local randomness) if it is R. This is a local model whose behaviour is
sum_lambda w_lambda kappa(a) kappa(b) [pi(a) = alpha_x][pi(b) = beta_y] = kappa(a) kappa(b) q_v(pi(a), pi(b)|x,y) = p_v.
The formula for q_v: pi_* is linear and pi_* u has independent marginals (1/d, 1/d, (d-2)/d). QED
(Exact symbolic check d = 4..9: item C4.)

For C_d: q = CH for even d, q = (1-t) CH + t delta_0 (t = 1/d) for odd d (Lemma 1; the delta_0 part stays at outcome 0).

### 2.4 The facets of L(2,2,3) (Lemma 4)

Collins-Gisin coordinates of a no-signalling behaviour on {0,1,2}^2: pA(a|x), pB(b|y) (a, b in {0,1}) and p(a,b|x,y)
(a, b in {0,1}) -- 24 numbers which determine the behaviour (the remaining entries follow from normalisation and
no-signalling) by an affine bijection between the no-signalling affine space and R^24. In these coordinates
L(2,2,3) = conv(V), V = the 81 deterministic points (0/1 vectors); the 81 x 25 matrix [1, v] has rank 25, so conv(V)
is full-dimensional, hence equal to the intersection of its facet half-spaces (Minkowski-Weyl).

**Lemma 4.** L(2,2,3) has exactly 1116 facets: 36 positivity facets p(a,b|x,y) >= 0, 648 lifted CHSH facets
(every measurement coarse-grained by a partition {k} | {other two}, 3^4 partitions x 8 sign patterns), and 432
facets forming the orbit of CGLMP_3 under outcome permutations of each measurement, setting swaps and the party swap.
The list (primitive integer vectors (h_0, h) with h_0 + h.x >= 0) is in facets223.txt.

*Proof (computer-assisted, exact).* The facets of the full-dimensional polytope conv(V) correspond bijectively (up to
positive scaling) to the extreme rays of the pointed polyhedral cone C = {h in R^25 : h_0 + h.v >= 0 for all v in V}.
facets223.py computes all extreme rays of C by the double description method (Motzkin-Raiffa-Thompson-Thrall 1953;
Fukuda-Prodon 1996) in exact integer arithmetic with the combinatorial adjacency test (two rays are adjacent iff no
third current ray vanishes on all constraints on which both vanish). It returns 1116 rays; the computation is repeated
with the reverse constraint order with identical output. Independently of the algorithm, each of the 1116 inequalities
is checked exactly to be valid (nonnegative on all 81 vertices) and facet-defining (its tight vertices span an affine
hyperplane: rank of [1, v] over tight v equals 24). Finally the set coincides with the union of the three explicitly
generated classes. This agrees with Collins-Gisin (2004) (classes positivity, CHSH, CGLMP). QED (item C1, 10 s.)

### 2.5 Exact critical visibility of the competitor (Proposition 5)

Write every facet F of L(2,2,3) as an affine function f >= 0 of the CG coordinates (Lemma 4). Let F_c be the
coarse-grained CHSH facet of Lemma 2 restricted to {0,1,R} (partition {0}|{1,R} for all four measurements, signs
(1,1,1,-1)); it is one of the 648 lifted CHSH facets, f_c = k (2 - CHSH) with k > 0.

For t in [0, 1/3] let q_t be q from Lemma 3 (q_t = CH, or q_t = (1-t) CH + t delta_0) and n_t as in Lemma 3. All
CG coordinates of q_t and n_t are polynomials in t with coefficients in Q(sqrt2); so are
    f(q_t), f(n_t)  and  G_F(t) := f_c(n_t) f(q_t) - f(n_t) f_c(q_t).

**Proposition 5.** For every facet F and every t in [0, 1/3]: G_F(t) >= 0. Moreover f_c(n_t) = 8 k t (1 - t) > 0 and
f_c(q_t) < 0 for t in (0, 1/3]. Consequently, for every d >= 3 (t = 1/d) and both constructions,
    v_c = v*(t) := f_c(n_t) / (f_c(n_t) - f_c(q_t)),
and v*(1/d) = v_even(d) for q = CH, v_odd(d) for q = (1-t) CH + t delta_0.

*Proof.* Fix d and t = 1/d. Each f is affine, so f(v q + (1-v) n) = v f(q) + (1-v) f(n). At v = v* the identity
    f(v* q + (1-v*) n) = (f_c(n) f(q) - f_c(q) f(n)) / (f_c(n) - f_c(q)) = G_F(t) / (f_c(n) - f_c(q))
holds (expand v* and 1 - v* = -f_c(q)/(f_c(n) - f_c(q))). The denominator is positive. If all G_F(t) >= 0, the point
q_{v*} (a no-signalling behaviour, as a mixture of two) satisfies every facet inequality, hence lies in L(2,2,3)
(Lemma 4: complete list), and by Lemma 3 the
behaviour v* p + (1-v*) u is local, i.e. v_c >= v*. Since G_{F_c} = 0, f_c(q_{v*}) = 0, and f_c(q_v) = v f_c(q) +
(1-v) f_c(n) is strictly decreasing in v, so f_c(q_v) < 0 for v > v*: nonlocal. Thus v_c = v*. The closed forms
follow from f_c(n) = k (2 - CHSH(u)) and f_c(q) = k (2 - CHSH(q)) and Lemma 2(iii) (also verified as polynomial
identities: f_c(n) ((sqrt2 - 1) + 4(t - t^2)) = 4 (t - t^2)(f_c(n) - f_c(q)) for q = CH, and
f_c(n) ((sqrt2 - 1) + 4t) = 4t (f_c(n) - f_c(q)) for the odd construction, which are v* = v_even(1/t), v_odd(1/t)
after multiplying numerator and denominator by d^2 resp. d).

Certificate for G_F >= 0: for each F the polynomial G_F (degree <= 3) is written in the Bernstein basis of
[0, 1/3], G_F(t) = sum_i b_i C(n,i) s^i (1-s)^{n-i}, s = 3t; all b_i are >= 0, decided exactly in Q(sqrt2) (the sign of
a + b sqrt2 is decided by comparing a^2 and 2 b^2). For 8 facets (lifted CHSH facets equivalent to F_c on these
behaviours) G_F vanishes identically; for the other 1108 no subdivision is needed. The negativity of f_c(q_t) is
certified the same way (-f_c(q_t) - 10^-6 >= 0 on [0, 1/3]). Done for q = CH, q = (1-t) CH + t delta_0 and
q = (1-t) CH + t delta_1. QED (competitor.py; item C5, which also re-checks d = 3..12 by direct exact evaluation of
all 1116 facets at v*.)

**Facet-free alternative proof of the lower bound v_c >= v* (independent of Lemma 4).** independent-check-B/REPORT.md
(sec. 2.4) gives an explicit local model of the reduced behaviour v CH + (1-v) nu (x) nu, nu = (s, s, 1-2s), at
v = T(s) = 4s(1-s)/(sqrt2 - (1-2s)^2) (= v_even(1/s)) with 17 deterministic strategies: weight
sigma = (1-v)(1-2s)^2 on "all four outputs R"; weight (rho - sigma)/2, rho = (1-v)(1-2s), on each of 8 strategies with
exactly one output R (A_0 = R: (A_1, B_0, B_1) = (r, r, 1-r); A_1 = R: (A_0, B_0, B_1) = (r, r, r); B_0 = R:
(A_0, A_1, B_1) = (r, 1-r, r); B_1 = R: (A_0, A_1, B_0) = (r, r, r); r in {0,1}); weight (1 - 4 rho + 3 sigma)/8 on each of
the 8 deterministic {0,1}-strategies saturating CHSH with signs (1,1,1,-1). The odd construction reduces to this one
because its delta_0 part is deterministic (v_odd(1-s)/(1 - v_odd s) = T(s)). We re-verified this model exactly for
s = 1/d, d = 2..40 (item C5b); independently, exact LP-vertex local models with weights in Q(sqrt2) (also 17
strategies) were found and verified for both constructions, d = 3..16 (competitor_model.py, item C5b). Together with
Lemma 2 this proves Theorem 1(a) without the facet list; the facet list is still used for Theorem 3 (d = 3 on Phi_3).

This proves Theorem 1(a) (Lemma 2 gives the violating inequality, Proposition 5 the exact value), for all d >= 3.

### 2.6 The 1/2-lemma (Lemma 6)

**Lemma 6.** Let p be any behaviour of the (2,2,d) scenario whose four joint distributions p(.,.|x,y) all have
uniform marginals: sum_b p(a,b|x,y) = 1/d for all a, x, y and sum_a p(a,b|x,y) = 1/d for all b, x, y. Then
v p + (1-v) u is local for every v in [0, 1/2].

*Proof.* Define two joint distributions of (A_0, A_1, B_0, B_1) on Z_d^4:
    P_1(a_0, a_1, b_0, b_1) = p(a_0, b_0|0,0) p(a_1, b_1|1,1),     P_2(a_0, a_1, b_0, b_1) = p(a_0, b_1|0,1) p(a_1, b_0|1,0).
Each is a probability distribution on deterministic strategies, i.e. a local model. Under P_1 the pair (A_0, B_0) has
law p(.,.|0,0), (A_1, B_1) has law p(.,.|1,1), and (A_0, B_1) has law (marginal of A_0 under p(.,.|0,0)) x (marginal of
B_1 under p(.,.|1,1)) = (1/d)(1/d), i.e. u(.,.|0,1); likewise (A_1, B_0) ~ u. Under P_2 the links (0,1), (1,0) carry p
and the links (0,0), (1,1) carry u. Hence (P_1 + P_2)/2 is a local model of (p + u)/2. For v < 1/2,
v p + (1-v) u = 2v (p + u)/2 + (1 - 2v) u is a convex combination of local behaviours. QED
(More generally, the same two models show that (p + p_A (x) p_B)/2 is local for every no-signalling p, where
p_A (x) p_B is the product of the marginals; REF_noise_B sec. 3.1. An equivalent model glues two adjacent links at their
common variable and makes the other two links products of uniform marginals. The constant 1/2 is optimal in general: the PR box (d = 2) has uniform marginals and CHSH = 4, so
v PR + (1-v) u violates CHSH for every v > 1/2. Exact check of the construction on random rational behaviours: item C6.)

DKZ_d has uniform marginals (for a rank-one PVM on Phi_d, sum_b p(a,b|x,y) = <Phi_d|P^x_a (x) 1|Phi_d> = Tr P^x_a/d =
1/d), so v_c(DKZ_d) >= 1/2 for every d.

### 2.7 DKZ: closed form, covariant local models, certificates

**Lemma 7 (closed form).** p_DKZ(a,b|x,y) = h_xy(b - a)/d with
    h_xy(m) = 1 / (2 d^2 sin^2(pi (m - delta_xy)/d)),   delta_xy = alpha_x - beta_y:
    delta_00 = 1/4, delta_01 = -1/4, delta_10 = 3/4, delta_11 = 1/4.
*Proof.* p = |<Phi_d| a_x, b_y>|^2 = (1/d)|sum_k <k|a_x><k|b_y>|^2 = d^{-3} |sum_{k=0}^{d-1} e^{i k theta}|^2 with
theta = 2 pi (a - b + delta_xy)/d, and |sum_k e^{ik theta}|^2 = sin^2(d theta/2)/sin^2(theta/2) (theta/2 is not in
pi Z because delta_xy is not an integer). sin^2(d theta/2) = sin^2(pi(a - b) + pi delta_xy) = sin^2(pi delta_xy) = 1/2.
QED (Float cross-check against the explicit bases and of I_d = I_ME(d): item C7.) In particular sum_m h_xy(m) = 1
(orthonormality of the bases; equivalently sum_{m=0}^{d-1} csc^2(x + m pi/d) = d^2 csc^2(d x)).

**Lemma 8 (covariant local models).** Let P_00, P_01, P_10, P_11 be probability distributions on Z_d and mu a
probability distribution on M = {(m_00, m_01, m_10, m_11) in Z_d^4 : m_00 - m_01 - m_10 + m_11 = 0 mod d} whose
one-dimensional marginals are P_xy. Then p(a,b|x,y) = P_xy(b - a)/d is local.
*Proof.* Draw m ~ mu and, independently, a_0 uniform on Z_d; output A_0 = a_0, B_0 = a_0 + m_00, B_1 = a_0 + m_01,
A_1 = a_0 + m_00 - m_10. Then B_0 - A_0 = m_00, B_1 - A_0 = m_01, B_0 - A_1 = m_10, and B_1 - A_1 = m_01 - m_00 + m_10
= m_11 (mod d) by the constraint. Each A_x is uniform and independent of m (a_0 is uniform and independent of m), so
P(A_x = a, B_y = b) = (1/d) P(m_xy = b - a) = P_xy(b - a)/d. QED

**Lemma 9 (absorption).** Let T^v = v p + (1-v) u with p as in Lemma 6 (uniform marginals). Let Q be a local
behaviour with uniform marginals and 0 < v0 < v1 <= 1 with |Q(a,b|x,y) - T^{v1}(a,b|x,y)| <= (v1 - v0)/(2 d^2 v0) for
all entries. Then T^{v0} is local. (Covariant form: if p = h_xy(b - a)/d and Q = Q_xy(b - a)/d, the condition reads
|Q_xy(m) - T^{v1}_xy(m)| <= (v1 - v0)/(2 d v0), with T^{v1}_xy(m) = v1 h_xy(m) + (1 - v1)/d.)
*Proof.* T^{v0} = (v0/v1) T^{v1} + (1 - v0/v1) u. With E = T^{v1} - Q (all marginals of E vanish, since T^{v1} and Q
have uniform marginals) and kappa = v0/(v1 - v0):
    T^{v0} = (v0/v1) Q + (1 - v0/v1) (u + kappa E),     u + kappa E = (u + S)/2,   S := u + 2 kappa E.
The hypothesis gives S >= 0 entrywise; S sums to 1 on each (x,y) and has uniform marginals, so it is a behaviour with
uniform marginals and (u + S)/2 is local by Lemma 6. Hence T^{v0} is a convex combination of the local Q and a local
behaviour. QED

**Proposition 10 (certificates).** For each d in {3, ..., 20} the file certificates/dkz_d{d}.json contains rationals
v0 < v1 and a probability distribution mu with rational weights (common denominator 10^16) on triples (m_00, m_01,
m_10) (m_11 := m_01 + m_10 - m_00 mod d), such that the marginals Q_xy of mu satisfy Lemma 9 for DKZ_d. Hence
v_c(DKZ_d) >= v0(d) (values in the table, v0(d) > 2/I_ME(d) - 1.02 * 10^-7), and v_c(DKZ_d) >= r(d) for d = 4..9.
*Verification (exact).* mu >= 0 and sum mu = 1 are checked with integers. Q_xy(m) is computed exactly. The numbers
h_xy(m) are enclosed in rational intervals: pi in [PI_LO, PI_HI] from Machin's formula
pi = 16 arctan(1/5) - 4 arctan(1/239) (alternating series, consecutive partial sums bracket the limit; width < 10^-50);
sin^2(pi s) for rational s is reduced to sin(pi r), r in [0, 1/2], and sin is increasing on [0, pi/2], so
sin(r PI_LO) <= sin(pi r) <= sin(r PI_HI); sin(x) for rational 0 <= x <= 2 is bracketed by consecutive partial sums of
its Taylor series (alternating with decreasing terms since x^2 < 6). Then max over x, y, m of
max(|Q - T_lo|, |Q - T_hi|) is compared exactly with (v1 - v0)/(2 d v0): margins about 10^-13 against errors about
10^-15 (dkz_cert.py check; items C8, C8b). The certificates were produced by a covariant LP (HiGHS, d^3
variables) at v1 slightly below the LP optimum and rounded; the floating-point LP plays no role in the verification.
The supports have about 4d - 3 points (basic solutions). QED

**Upper bound.** I_d(p_DKZ) = I_ME(d) (direct computation, CGLMP 2002; checked numerically in item C7 and exactly in
radicals for d = 3 in item S1) and I_d(u) = 0, so I_d(v p + (1-v) u) = v I_ME(d) > 2
for v > 2/I_ME(d): v_c(DKZ_d) <= 2/I_ME(d). (Not needed for Theorem 1; it shows that the certified lower bounds are
within 1.02 * 10^-7 of the truth for 3 <= d <= 20, i.e. CGLMP is, up to 10^-7, the optimal witness for DKZ.)

**Proposition 11 (exact value for small d; not needed for Theorem 1).** v_c(DKZ_d) = 2/I_ME(d) exactly for
d = 3, 4, 5, 6; i.e. for these d the CGLMP inequality is an optimal witness for DKZ against the whole local polytope.
*Proof.* Let K_d = conv{(e_{m00}, e_{m01}, e_{m10}, e_{m11}) : m00 - m01 - m10 + m11 = 0 mod d} in coordinates
mu_xy(m), m = 1..d-1 (dimension 4(d-1); full-dimensional, rank check). Its complete facet list is computed by the exact
double description (two insertion orders, every facet re-verified): 66 (d = 3), 216 (d = 4), 1020 (d = 5), 2462
(d = 6) facets.
Let v* = 2/I_ME(d) and T = (T^{v*}_xy(m)). All numbers lie in the field Q(c), c = cos(pi/(4d)): with theta = pi/(4d),
pi (m - delta_xy)/d = k theta with k = 4m - 4 delta_xy an odd integer, sin^2(k theta) = (1 - T_{2|k|}(c))/2, and
sec(pi j/(2d)) = 1/T_{2j}(c) (T_n = Chebyshev polynomials). Elements are represented as polynomials in c of degree
< deg m, m = minimal polynomial of c (degrees 4, 8, 8, 8); m(c) = 0 is certified independently (m divides T_{2d}, and m
changes sign on a rational enclosure of c of width < 10^-45, while the roots of T_{2d} are farther apart). Inverses are
verified by a z = 1 mod m. Each facet value at T is an integer combination of the T values: it is either the zero
polynomial (exactly 0) or its sign is decided by rational interval evaluation at the enclosure of c. Result: every
facet is >= 0 at T, exactly one (the covariant CGLMP facet) with value exactly 0, all others >= 0.0234. Hence T is in
K_d, so a distribution mu as in Lemma 8 exists and T^{v*} is local: v_c(DKZ_d) >= 2/I_ME(d); the upper bound above
gives equality. QED (dkz_exact.py; item C11 runs d = 3, 4, 5 in 10 s; d = 6 takes about 9 minutes:
`python dkz_exact.py 6`, log logs/dkz_exact_d6.log. d = 3 agrees with Theorem 3. d = 7 (343 vertices) was not run to
completion.)

### 2.8 Conclusion

* d >= 10: v_c(DKZ_d) >= 1/2 (Lemma 6) and v_c(C_d) < 1/2. Even d: v_even(d) < 1/2 iff
  (sqrt2 - 1) d^2 - 4d + 4 > 0; at d = 9 the left side is 81 sqrt2 - 113 > 0 (13122 > 12769), and its derivative
  2 (sqrt2 - 1) d - 4 is positive for d >= 5, so it holds for all real d >= 9, in particular for even d >= 10 (it fails
  at d = 8: 64 sqrt2 - 92 < 0, v_even(8) = 0.5137). Odd d: v_odd(d) < 1/2 iff (sqrt2 - 1) d > 4 iff d > 4(sqrt2 + 1) =
  9.657..., i.e. odd d >= 11 (fails at d = 9: v_odd(9) = 0.5176).
* d = 4, ..., 9: v_c(C_d) < r(d) <= v_c(DKZ_d) by Proposition 10; the inequalities v_comp(d) < r(d) are exact
  comparisons in Q(sqrt2) (item C9; numerically 0.6442 < 0.69, 0.6589 < 0.687, 0.5729 < 0.684, 0.5798 < 0.683,
  0.5137 < 0.682, 0.5176 < 0.681).

Together with Proposition 5 this proves v_c(C_d) < v_c(DKZ_d) for all d >= 4. QED (Theorem 1)

---------------------------------------------------------------------------------------------------------------------

## 3. Supplements

### S1. d = 3 on Phi_3: the literal clause HOLDS (all PVMs, all ranks)

**Theorem 3.** For every projective strategy S on Phi_3 (three-outcome PVMs of arbitrary ranks, zero projectors
allowed) and Gill's noise u: v_c(S) >= 2/I_ME(3) = 3 sqrt3 - 9/2 = 0.696152422707..., with equality iff S is DKZ_3 up
to relabellings (outcome permutations of each measurement, setting swaps, party swap) and a local unitary
u (x) conj(u). Moreover v_c(DKZ_3) = 2/I_ME(3) and I_ME(3) = (12 + 8 sqrt3)/9.

*Proof.* Let p be the behaviour of S and p_v = v p + (1-v) u with v <= 2/I_ME(3). By Lemma 4 it suffices that p_v
satisfies the 1116 facet inequalities.
(i) Positivity: p_v is a probability distribution.
(ii) CGLMP class (432 facets): by construction each is, on the no-signalling space, a positive multiple of
2 - I_3(g.p) for a relabelling g; g.p is again a projective strategy on Phi_3 (an outcome relabelling permutes the
projectors; a setting swap permutes the PVMs; the party swap gives the strategy with the PVMs of Alice and Bob
exchanged, because Tr(X^T Y) = Tr(Y^T X)). The value under u is 0 for all 432 (exact check). By Theorem A of
main.tex (which covers PVMs with zero projectors), I_3(g.p_v) = v I_3(g.p) <= v I_ME(3) <= 2.
(iii) Lifted CHSH (648 facets): each is a positive multiple of 2 - CHSH_F, CHSH_F = sum_xy s_xy E^F_xy, where every
measurement x is binarised by a +-1-valued function sigma^F_x taking one value on a single outcome and the other
value on the remaining two (either polarity), and s has exactly one minus sign (a pattern with three minus signs is
the same inequality after flipping the polarity of one party's two binarisations).
Quantum part: A_x = sum_a sigma^F_x(a) P^x_a and B_y = sum_b sigma^F_y(b) Q^y_b are Hermitian involutions on C^3 (any
traces) and E^F_xy(p) = Tr(A_x^T B_y)/3. With one minus sign among the four s_xy, one row of s is (+-1)(1, 1) and the
other (+-1)(1, -1), so CHSH_F(p) = (1/3)[+-Tr(A_0^T (B_0 + B_1)) +- Tr(A_1^T (B_0 - B_1))] up to exchanging the
rows, and Hoelder (||A_x^T||_inf = 1) gives CHSH_F(p) <= (1/3)(||B_0 + B_1||_1 + ||B_0 - B_1||_1). By Jordan's lemma
B_0, B_1 have a common invariant orthogonal decomposition of C^3 into subspaces of dimension <= 2; on a 2-dimensional
one on which neither is scalar they act as two reflections at an angle t, and ||B_0 + B_1||_1 + ||B_0 - B_1||_1
restricted there equals 4|cos(t/2)| + 4|sin(t/2)| <= 4 sqrt2; on a 1-dimensional one b_0, b_1 in {+-1} contribute
|b_0 + b_1| + |b_0 - b_1| = 2. As C^3 splits as 2 + 1 or 1 + 1 + 1, CHSH_F(p) <= max(4 sqrt2 + 2, 6)/3 =
(4 sqrt2 + 2)/3. Noise part: each binarised outcome has mean +-1/3 under u, so CHSH_F(u) = (1/9) sum_xy s_xy (+-1)(+-1)
= +-2/9 (exact check of all 648). Hence CHSH_F(p_v) <= g(v) := v (4 sqrt2 + 2)/3 + (1-v) 2/9; g is increasing and
g(4/(3 sqrt2 + 1)) = 2, so no lifted CHSH facet is violated for v <= 4/(3 sqrt2 + 1) = 0.762974..., which exceeds
2/I_ME(3) (exact comparison of algebraic numbers, re-checked with rational enclosures of sqrt2 and sqrt3).
So p_v is local for every v <= 2/I_ME(3). DKZ_3: I_3(DKZ_3) = (12 + 8 sqrt3)/9 = I_ME(3) (computed exactly in radicals
from Lemma 7), so v_c(DKZ_3) <= 2/I_ME(3), hence equality.
Equality case: if v_c(S) = 2/I_ME(3), then for every v in (2/I_ME(3), 4/(3 sqrt2 + 1)) the point p_v violates some
facet, which by (i) and (iii) lies in the CGLMP class: v I_3(g.p) > 2. The relabelling group is finite, so one g works
along a sequence v_n -> 2/I_ME(3); this gives I_3(g.p) >= I_ME(3), hence = I_ME(3) (Theorem A), and Theorem B of
main.tex (rigidity, D = d = 3) gives g.S = DKZ_3 up to u (x) conj(u). Conversely, relabellings and local unitaries
u (x) conj(u) do not change v_c. QED (phi3.py; verify_theorem.py item S1.)

Remarks. (0) As far as we found this all-rank statement is new; for the lower bound on DKZ_3 itself see the caveat on
Chen et al. (2001) in Section 1. (1) The bound 4/(3 sqrt2 + 1) is attained: it equals v_c(C_3) = v_odd(3) (Proposition 5 at t = 1/3), so on
Phi_3 every non-CGLMP facet needs visibility > 0.76297. (2) For rank-one PVMs this is Theorem N3 of our earlier
working notes on the noise clause (where u = white noise); Theorem 3 covers all ranks, where u differs from white
noise.

### S2. d = 3 on other maximally entangled states: the clause FAILS (Phi_2 and every even D)

**Proposition S2.** On Phi_2 let P^x_0 = Pi^x_+, P^x_1 = Pi^x_-, P^x_2 = 0 and Q^y_b likewise (outcome 2 unused).
Then v_c = 8/(9 sqrt2 - 1) = 0.682132773235... < 2/I_ME(3) = v_c(DKZ_3) = 0.696152422707.... The same behaviour arises
on every Phi_D with D even (tensor with 1_{D/2}), in particular on Phi_6, where DKZ_3 (x) 1_2 is available. On Phi_D
with D odd, (D-1)/2 CHSH blocks plus one deterministic dimension give v_c <= (16/9)/((16/9) + ((D-1)/D)(2 sqrt2 - 2)),
which is < 2/I_ME(3) iff D >= 17 (exact). (D = 3: Theorem 3; D = 5, 7, ..., 15: not decided.)

*Proof.* The behaviour is CH (Lemma 1 with D = 2), so Lemma 3 (d = 3, R = {2}) and Proposition 5 with q = CH at
t = 1/3 give v_c = 4 * 2/((sqrt2 - 1) 9 + 8) = 8/(9 sqrt2 - 1). The comparisons and the statement for odd D are exact
comparisons of algebraic numbers (phi3.py). QED

So for d = 3 the literal clause is true when the state is fixed to Phi_3 and false when any maximally entangled state
is allowed.

### S3. Scope: what the counterexample needs; POVM version without unused outcomes

**Lemma S3a.** On Phi_d, a PVM whose d outcomes all have nonzero probability is rank-one; for rank-one PVMs u equals
the white-noise behaviour tr(P^x_a) tr(Q^y_b)/d^2 of the state v Phi_d + (1-v) 1/d^2.
*Proof.* d nonzero orthogonal projectors summing to 1_d have ranks >= 1 summing to d. QED
Hence for projective strategies on Phi_d that use every outcome the literal clause coincides with the white-noise
question C2 (proved for d = 3 by Theorem 3, numerically true for d <= 8, open otherwise): a projective counterexample on
Phi_d without unused outcomes would refute C2. The counterexample C_d of Theorem 1 uses d - 2 unused outcomes.

**Proposition S3b (POVMs, every outcome used).** Let d >= 4, 0 < eps <= 1/100, and
M^x_a = (1 - eps) P^x_a + (eps/d) 1, N^y_b = (1 - eps) Q^y_b + (eps/d) 1 with (P, Q) = C_d on Phi_d. Every effect is
>= (eps/d) 1 (full rank, trace >= eps), every outcome pair has probability >= eps^2/d^2, and
    v_c(C_d) <= v_c(M, N) <= w_eps(d) < v_c(DKZ_d),
where w_eps(d) = (2 - 2e^2)/(CHSH_eps - 2e^2), e = (2-d)/d, CHSH_eps = (1-eps)^2 2 sqrt2 + 2 eps^2 e^2 (even d),
CHSH_eps = (1-eps)^2 ((d-1)/d 2 sqrt2 + 2/d) + (1-eps) eps 4e/d + 2 eps^2 e^2 (odd d).
*Proof.* The behaviour is (L (x) L) p_{C_d}, with the local outcome channel L(a|a') = (1-eps)[a = a'] + eps/d, and
(L (x) L) u = u; local post-processing preserves locality, so v_c(M, N) >= v_c(C_d). After binarising as in Lemma 2,
L keeps the binary outcome with probability 1 - eps and otherwise replaces it by an independent one with mean e; with
the marginal means 0 (even d) resp. 1/d (odd d) of C_d this gives E_xy(eps) = (1-eps)^2 E_xy + (1-eps) eps e
(<A_x> + <B_y>) + eps^2 e^2 and the stated CHSH_eps; Lemma 2(iii) gives the bound w_eps. CHSH_eps is decreasing in eps
on [0, 1/100]: its derivative is -4 sqrt2 (1 - eps) + 4 eps e^2 <= -4 sqrt2 (0.99) + 0.04 < 0 (even d), resp.
-2 (1 - eps) CHSH(p_{C_d}) + (1 - 2 eps) 4e/d + 4 eps e^2 <= -2 (0.99) 2 + 0 + 0.04 < 0 (odd d; CHSH(p_{C_d}) >= 2,
e < 0); povm.py also certifies this exactly for d = 4..10, so w_eps <= w_{1/100}. Finally
w_{1/100}(d) < v0(d) for d = 4..10 and w_{1/100}(d) < 1/2 for all d >= 11 (exact, povm.py; the latter as positivity
of a polynomial in d - 11 with positive coefficients). Numerically w_{1/100} = 0.6602 (d=4), 0.6790 (5), 0.5900 (6),
0.6003 (7), 0.5312 (8), 0.5380 (9). QED

**Remark S3c (PVMs on Phi_D, D > d, every outcome used).** P^x_0 = Pi^x_+ (x) 1_k (+) 0, P^x_1 = Pi^x_- (x) 1_k (+) 0,
P^x_a = |e_a><e_a| (a = 2, ..., d-1, on d - 2 extra basis vectors), D = 2k + d - 2, Bob likewise. The behaviour is
(2k/D) CH + ((d-2)/D) tau (tau: perfectly correlated uniform outcome in {2, ..., d-1}); its coarse-grained CHSH threshold
tends to v_even(d) as k -> infinity and is already below the certified v0(DKZ_d) for (d, D) = (4, 12), (5, 11),
(6, 12), (7, 13), (8, 12), (9, 13) (exact, povm.py). For d = 4, D = 12 the strategy DKZ_4 (x) 1_3 lives on the same
state. So once D > d the counterexample needs no zero projectors, only unbalanced ranks (then u is not white noise).

### S4. Ledger B1: CGLMP witness, white noise on the state, unbalanced PVMs -- NUMERICAL

Question: with rho_v = v Phi_D + (1-v) 1/D^2 and arbitrary PVMs, the noise term is n = p_A (x) p_B,
n(a,b|x,y) = tr(P^x_a) tr(Q^y_b)/D^2; is the CGLMP-witnessed threshold still >= 2/I_ME(d), i.e.
    (B1)   I_d(p) <= I_ME(d) - ((I_ME(d) - 2)/2) I_d(p_A (x) p_B)      for all PVM strategies on all Phi_D?
Equivalently: the isotropic state at v* = 2/I_ME(d) never violates CGLMP_d with PVMs. Write F = v* I_d(p) +
(1-v*) I_d(n); (B1) is F <= 2.

Proved parts (elementary):
* The marginals tr(P^x_a)/D are fixed by the rank pattern r, so n = n_r is constant on each pattern and (B1) reads
  v* I_max(r) + (1-v*) I_d(n_r) <= 2, with I_max(r) = max of I_d over PVMs with pattern r.
* Balanced patterns (all ranks D/d), and more generally all patterns with I_d(n_r) <= 0: (B1) follows from Theorem A.
* Patterns with a deterministic measurement (one projector equal to 1): p is local (a party with only one non-trivial
  setting always admits a local model), so I_d(p) <= 2 and I_d(n_r) <= 2 give F <= 2. The same holds for every
  pattern with I_max(r) <= 2.
* Direct sums with DKZ blocks: if p = w p_DKZ + (1-w) p' (block-diagonal; w = dimension fraction), then, because DKZ
  has uniform marginals and I_d(u_A (x) q_B) = I_d(q_A (x) u_B) = 0 for every q (each link term of I_d depends only on
  the law of b - a, which is uniform), F(p) = 2w + (1-w)[v* I_d(p') + (1-v*)(1-w) I_d(n')]; hence F(p') <= 2 implies
  F(p) <= 2 (if I_d(n') < 0 use v* I_d(p') <= 2). DKZ blocks never help.
Numerical evidence (no counterexample found):
* D = 2, all d <= 6, all patterns, with the angle optimisation reduced exactly to one variable
  (white_qubit_scan.py): max F = 1.97676 (d=3), 1.96878 (4), 1.96473 (5), 1.96229 (6).
* Block mixtures of DKZ, all d^4 deterministic strategies and all optimal nonlocal qubit blocks (white_mixture.py,
  d = 3, 4): max F = 2, attained only by DKZ or deterministic strategies.
* All rank patterns enumerated for (d, D) = (3, 2..9), (4, 2..8), (5, 2..6), (6, 2..5) (up to 4.0 * 10^9 patterns per
  case), pruned by the bound I_d(p) <= min(I_ME, N(r)), N(r) = sum of four transportation LPs with the marginals of r
  (floating-point LPs); for each (d, D) the 200 surviving patterns with the largest bound plus 200 random survivors
  were optimised by Riemannian gradient ascent (3 starts) (white_search.py, logs/white_d*_D*.log): the largest F found
  is 1.98569 (d = 4, D = 3); never above 2.
Status: NUMERICAL. A proof for all D would need a quantitative version of Theorem A near uniform marginals: there the
no-signalling bound is useless, while I_d(n_r) is quadratic in the distance of the marginals from uniform.

---------------------------------------------------------------------------------------------------------------------

## 4. Verification

`python verify_theorem.py` (Python 3, numpy, scipy, sympy; about 3 minutes) prints one PASS/FAIL line per item:

| item | what is checked | method |
|---|---|---|
| C1 | Lemma 4: 1116 facets, classes, two DD insertion orders, = facets223.txt | exact integers |
| C2 | Lemma 1: projectors, ranks, behaviour of C_d, d = 4..9 | sympy, exact |
| C3 | Lemma 2: local bound 2 (all d^4 strategies, d = 4..9), CHSH values, v_even/v_odd symbolically | sympy, exact |
| C4 | Lemma 3: p_v = kappa kappa q_v, q_v = v q + (1-v) n_{1/d}, d = 4..9, symbolic v | sympy, exact |
| C5 | Proposition 5: Bernstein certificates for all 1116 G_F on [0, 1/3]; per-d recheck d = 3..12 | Q(sqrt2), exact |
| C5b | facet-free: explicit 17-strategy model (REF_noise_B 2.4), d = 2..40; exact LP-vertex models, d = 3..16 | Q(sqrt2), exact |
| C6 | Lemma 6: two-model construction on random rational behaviours, d = 2..5 | Fractions, exact |
| C7 | Lemma 7 closed form, I_d(DKZ) = I_ME (sanity, float) | float, informational |
| C8 | Proposition 10, d = 3..20 (Theorem 1 needs 4..9) | Fractions + rigorous enclosures |
| C8b | 2/I_ME(d) - v0(d) < 1.02e-7, d = 3..20 | rigorous enclosure of I_ME |
| C9 | Section 2.8 inequalities (d >= 10 and d = 4..9) | Q(sqrt2), exact |
| C10 | full (2,2,d) LP v_c: competitor d = 4,5,6, DKZ d = 4,5 (sanity) | float, informational |
| C11 | Proposition 11: v_c(DKZ_d) = 2/I_ME(d) exactly, d = 3, 4, 5 (facets of K_d, arithmetic in Q(cos(pi/4d))); d = 6 separately (`python dkz_exact.py 6`) | exact |
| S1 | Theorem 3: facet-class data, CHSH_F(u) = +-2/9, I_F(u) = 0, thresholds, I_3(DKZ_3) in radicals | exact (phi3.py) |
| S2 | Proposition S2: 8/(9 sqrt2 - 1) and comparisons; odd D >= 17 | exact |
| S3 | Proposition S3b (all d >= 4) and Remark S3c (d = 4..9) | exact (povm.py) |
| S4 | ledger B1 search summary from logs/white_d*_D*.log | numerical, informational |

Files: exact.py (Q(sqrt2), polynomials, Bernstein, rigorous pi/sin), facets223.py (double description, classes),
facets223.txt (facet list), competitor.py (Proposition 5), dkz_cert.py (Proposition 10; `make` = LP generation,
`check` = exact verification), certificates/dkz_d3..20.json, dkz_exact.py (Proposition 11), phi3.py (S1, S2), povm.py (S3), white_qubit_scan.py,
white_mixture.py, white_search.py, run_white_batch.sh (S4; logs in logs/), competitor_model.py (C5b). Exploration only (not part of the proof):
explore_competitor.py.
