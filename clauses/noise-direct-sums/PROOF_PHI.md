# Theorem PHI: phi_inf(n) is a mixture of composition laws, for every n >= 2

Ansh Mishra, Aryan Senthilkumar. 2026-10-20. Part of [`THEOREM.md`](THEOREM.md) in this folder.

**Status:** proved, computer-assisted (interval verification for 4 <= n <= 50000, a written argument with two
n-independent interval computations for n >= 50001, and n = 2, 3 by hand). Independently re-checked (see
`INDEPENDENT_VERIFICATION.md`). Not reviewed by outside experts.

The record below is the condensed proof. It uses the pairing method of Theorem M (Lemma 1, pairing; Lemma 2, core) in
[`../noise-dkz-threshold/THEOREM.md`](../noise-dkz-threshold/THEOREM.md).

## 0. Notation

- n >= 2, S = n - 1, L = floor((S - 1)/2). G_n(x) = 1/(2 n^2 sin^2(pi (4x + 1)/(4n))) is the DKZ link law and
  kappa_n = I_ME(n)/2.
- phi_inf(n) = [G_n - (kappa_n - 1) delta_0]/(2 - kappa_n). Its CGLMP mean equals (n - 1)/4, and for 1 <= x <= S,
  phi(x) = 1/(2 n^2 (2 - kappa_n) sin^2(pi (4x + 1)/(4n))).
- CLAIM(phi): phi is the common one-dimensional marginal of a law on the compositions of S into four nonnegative parts
  (equivalently, a mixture of the laws (1/4) sum_i delta_{pi_i}).
- Q_n = G_n/kappa_n + (1 - 1/kappa_n) u_n is the DKZ threshold law; CLAIM(Q_n) is Theorem M.
- c_n = 8/(pi^2 (2 - kappa_n)), c_oo its limit, Phi1 = pi/16 + pi^2/32 - G_cat/2 = 0.0467916 (G_cat = Catalan's
  constant).
- D(y) (1 <= y <= L) is the antisymmetric part of the debt that the interior coupling must carry in the pairing
  reduction (Section 1).

## 1. Why nonnegative decomposability of phi_inf suffices
- Block laws of the template lie on [phi_inf(n), Q_n] (write phi = a G + b u + c delta_0, a+b+c = 1,
  mean (n-1)/4  <=>  a(2-kappa) + 2b = 1; {b >= 0, c <= 0} is exactly the segment).  Q_n is a strictly positive
  mixture (Theorem M); convexity => every block law is decomposable; the local model needs only nonnegative weights.
- Pairing + core (Theorem M, Lemmas 1-2) work verbatim with pi_I >= 0: need symmetric pi_I >= 0 on
  I = {p,q >= 1, p+q <= S-1} with (C1) F(y) - F(S-y) = D(y) (1 <= y <= L = floor((S-1)/2)), F = m_I - R_I/2,
  (C2) m_I < phi on [1, S-1], and 2 phi(0) > 1 (true for all n: G(0) >= 8/pi^2 > kappa_oo/2 >= kappa_n/2).
- Move calculus: cells {(p,q),(q,p)} of weight w add w(sigma_p + sigma_q - sigma_{p+q}) to AF = F - F(S-.) on [1,L]
  (sigma_x = e_x for x <= L, -e_{S-x} for x >= S-L, 0 at S/2) and use capacity w at p and at q.


## 2. Construction X (S = n-1, L = floor((S-1)/2), k = 1/50)
- rho(y) = k min(1,y/3) max(0, 1-(2y+1)/L)/(y(y+1)).  Near-diagonal moves A(y) = B(y) = rho(y): {y,y}->2y via cell
  (y,y) [weight 2A/3] and (y,S-2y)+mirror [2A/3 each]; {y,y+1}->2y+1 via (y,y+1)+mirror [B/3 each], (y,S-2y-1),
  (y+1,S-2y-1) + mirrors [B/3 each].  AF_X(t) = 3 rho(t) + rho(t-1) - rho(floor(t/2)).
- End game: h(s) = a/(3s^3) on full anti-diagonals s = L+1..S-1, beta(q) = a/(3(S-q)^3) on full columns q <= S-L-1;
  AF = a E1(t), E1(t) = sum_{s=L+1}^{S-t} s^-3 + (S-t-1)/(2(S-t)^3).
- Bulk: Deff = D - AF_X - a E1, U(y) = sum_{t<=y} t Deff(t), a = sum t(D - AF_X)/sum t E1 (=> U(L) = 0),
  T(y) = 2U(y)/(y(y+1)), kappa(s) = T(s-1) - T(s), h(s) = kappa(s)/3 on (p, s-p), beta(S-s) = kappa(s)/3 on (p, S-s).
- (C1) is EXACT: the bulk families sum to T(y) - ((y-1)/2)(T(y-1) - T(y)) = U(y)/y - U(y-1)/y = Deff(y); end-game
  anti-diagonal s gives h[1_[1,S-s] + ((s-1)/2) e_{S-s}]; end-game column q gives beta[(S-1-q) e_q + 2 1_[1,q]];
  so AF = Deff + AF_X + a E1 = D.  (Float brute force from the cell matrix, n <= 80: residual <= 7e-18.)
- Closed-form marginals (direct summation; brute force agrees to 7e-18):
    lower  m(y)   = (2/3)T(y) + 2rho(y) + (2/3)rho(y-1) + (a/3)[2 Z_L + (S-1-y)/(S-y)^3],  Z_L = sum_{L+1}^{S-1} s^-3
    upper  m(S-s) = [4U(s-1) - 2s(s-1)Deff(s)]/(3s(s+1)) + (2/3)rho(floor(s/2)) + (2a/3) sum_{S-s+1}^{S-1} s'^-3
    middle m(S/2) = (a/3)[2 sum_{S/2+1}^{S-1} s^-3 + (S/2-1)/(S/2)^3] (S even);  m(S-1) = 0.
- Conditions per n: (P0) a > 0; (P1) U(y) > 0, y < L; (P2) Q(s) = 4U(s-1) - 2s(s-1)Deff(s) >= 0 (then
  kappa(s) = Q/((s-1)s(s+1)) >= 0); (CL), (CU), (CM) the three marginals < phi.

## 3. Small n
- 4 <= n <= 50000: rigorous interval verification of construction X, `code/verify_X.py` via `code/run_verify.py`;
  logs `logs/verify_*.log`, ALL PASS.
-  n = 2: the only law with mean 1/4 is (3/4,1/4) = one-hot.
  n = 3: phi = 4phi(2) [(3/4)d0 + (1/4)d2] + 2phi(1) [(1/2)d0 + (1/2)d1] (weights sum to 1 by the mean; both > 0).

## 4. Large n: n >= 50001

In this section phi, D, Phi_n, c_n and the n-independent profiles are those defined in `code/asym_check.py` and
`code/lemma_sanity.py`. The section records the chain of estimates; the two n-independent computations are
`asym_check.py` (A) and (B).

### (S >= 50000, L >= 24999, x = y/S, w_c(x) = (1-4x)+, f(x) = 4 int_{x/2}^x w_c(v)dv/v, g = f - 2w_c)
- (C) kappa_n = kappa_oo - 32 Delta_n/(pi^2 (n-1)), Delta_n = sum_{m>=0} (m mod n) phi(m) in [0, Phi1]
  (E_G split over m >= 0 / m < 0); hence c_oo (1 - 0.2946/S) <= c_n <= c_oo.
- (Phi) 1/(16(t+1)^2) <= t phi(t) <= 1/(16 t^2), phi(t) <= 1/(16 t^3)  (polynomial comparison).
- (D) D(t) = c_n[Phi_n(t) - Phi_n(S-t)], Phi_n(t) = sum_{i>=0} phi(t+in) (partial fractions of csc^2);
  c_n(phi - 0.6/S^3) <= D <= c_n(phi + 0.08/S^3), D > 0; phi(t) = (c_n/(4t+1)^2)(theta/sin theta)^2;
  M_D(y) in [c_n(Phi1 - 1/(16y) - 0.08/S), c_n(Phi1 + 0.01/S)].
- (E) E1 in [1/(2(L+1)^2), 1/(2L^2)]; M_E(y) in [y(y+1)/(4(L+1)^2), y(y+1)/(4L^2)];
  a in [4c_n Phi1 (1 - 9/S), 4c_n Phi1 (1 + 3/S)]; Z_L <= (1/2)(L^-2 - (S-1)^-2), W(s) <= (1/2)((S-s)^-2 - (S-1)^-2).
- (F) straddle form F_n(y) = sum_{j=floor(y/2)+1}^{y} 2j rho(j) + sum_{j=floor((y-1)/2)+1}^{y-1} (2j+1) rho(j) + y rho(y)
  (all coefficients >= 0); w_c(u/S) - 6/(S-2) <= w(u) <= w_c(u/S); for 8 <= y <= L (sum-integral comparison for
  nonincreasing summands): F_n <= k(f + 9/y), (4/3)F_n >= k((4/3)f - 12/y - 23/S), y^2 rho(y) <= k w_c,
  y^2 rho(y-1) <= k(w_c + 2/L)(1 + 1/(y-1)).   (lemma_sanity.py: all bounds hold in float at n = 50001..10^6.)
- Region A (y, s <= 200): rho_n = rho_oo (1 - eps), eps <= 401/24999; F_n in [(1-eps)F_oo, F_oo];
  U_n in [U_oo - 1.1e-5, U_oo + eps F_oo + 1e-8]; D_n in [(1-6e-6) c_oo phi - 1e-14, c_oo phi + 1e-14]; a E1 <= 2.4e-10;
  phi_n >= c_oo (1-6e-6)/(4y+1)^2 resp. /(4s+3)^2.  asym_check.py (A), exact rationals + interval c_oo
  (Catalan by Ramanujan's series with exact integer terms): PASS (worst 0.7966 / 0.7969; U >= 8.8e-3; Q >= 0.104*4U).
- Region B (y, s >= 201):
  (P1) forward for y <= 0.3S: U >= P(x) - 0.0016, P = c_n Phi1 (1-4x^2) - k f concave on [0,0.3], P(0) = 0.01818,
  P(0.3) = 0.0383; backward for y >= 0.3S: every term t(a E1 + AF_X - D) of U(y) = sum_{t>y} is > 0
  (a E1 >= 0.5889/S^2, rho(floor(t/2)) <= 0.3556/S^2, D <= 1e-4/S^2).
  (P2) s <= 0.3S+1: Q >= 4[c_n Phi1 - k f(x') - 4k x'] - 1.58/(s-1) - 3/S > 0, x' = (s-1)/S (the -16 c Phi1 x^2 of
  U cancels +2s(s-1)aE1; the bracket is >= 0.018); larger s: both terms of Q positive.
  Capacity: y^2 m(y) <= c_n H_S + k(12/y + 0.67/(y-1)) + 1/S;  s^2 m(S-s) <= c_n H_S + 23.4k/(s-1) + 1.2/S
  (rho(floor(s/2)) terms nearly cancel; F_n(s-1) >= F_n(s) - s(3rho(s) + rho(s-1))),
  H_S = (4/3)Phi1[1 + (1+3/S) x^2((1-x)^-2 - 1)] - (4/3)(k/c_oo) g; capacities >= (c_n/16)(1 - 3/(2y))(pi xt)^2
  csc^2(pi xt), xt = y/n >= x(1 - 2e-5).  asym_check.py (B): H + 0.0017 <= (0.9925/16)(pi xt)^2 csc^2(pi xt) on
  (0,1/2] (H and RHS increasing; 2000 cells H(x_{i+1}) <= RHS(x_i)): PASS, worst 0.8221.
- Middle: m(S/2) <= (a/3)(8/S^2) <= 0.786/S^2 < 0.9706/S^2 <= phi(S/2).  Corner: 2phi(0) > 1.
  => THEOREM PHI for n >= 50001.  QED

## 5. Lemma K

Lemma K (kappa_n strictly increasing) is proved analytically for every n in [`THEOREM.md`](THEOREM.md), Section 2.
`code/kappa_mono.py` is an independent interval check for 2 <= n <= 2000 (`logs/kappa_mono.log`).
