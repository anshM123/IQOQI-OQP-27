# Theorem N global certificate: method (tracking bound)

Theorem N (KL clause, d = 3, Nash part): for DKZ_3's Alice measurements A* and the DKZ-optimal Alice model mu*,
    max over Bob bases B of  Phi(A*, B; mu*) <= S0 = S(DKZ_3) (nats),
where Phi(A*, B; mu*) = min over stochastic kernels K(b | a0, a1) of (1/2) sum_x D(q_x || p_x(K)),
q_x(a, b) = |<a_x | Bt e_b>|^2 / 3  (Bt = steered Bob basis, CKM coordinates y in R^6),
p_0(a, b) = sum_a1 mu(a, a1) K(b | a, a1),  p_1(a, b) = sum_a0 mu(a0, a) K(b | a0, a).
Both DKZ Bob bases attain S0. Together with Lemma R (S <= min_mu (1/2) sum_y Phi_y), Theorem N gives
Bob-optimality of DKZ_3 against DKZ_3's Alice. By the party symmetry, DKZ_3 is a Nash equilibrium of the KL game.
It does NOT settle the KL clause (C3), which needs the maximum over Alice as well.

## Pieces

1. **Domain and symmetries (`bb_track.py`).**
   - The domain is D' = [0, pi/2]^3 x [0, pi] x [0, pi/3] x [0, 2 pi].
   - Complex conjugation reduces delta to [0, pi] (already in `nash_bb.py`).
   - D = diag(e^{i pi k/3}) is a symmetry: Phi(D B) = Phi(B), with D^2 = Z. Exact proof:
     - With w = e^{2 pi i/3}: <a_x | v> = 3^{-1/2} sum_k w^{-k(a + alpha_x)} v_k, alpha_0 = 1/2, alpha_1 = 0.
     - D v has components w^{k/2} v_k, so <a_x | D v> = 3^{-1/2} sum_k w^{-k(a + alpha_x - 1/2)} v_k. Hence
       <a_0 | D v> = <a_1 | v> and <a_1 | D v> = <(a-1)_0 | v>.
     - So q'_0(a, b) = q_1(a, b) and q'_1(a, b) = q_0(a - 1, b), where q' is the table of D B.
     - mu*(a0, a1) = f(a1 - a0 mod 3) with f(0) = f(1) (numerically 0.14893) and f(2) = 0.03547. Exact: mu*(a0, a1) =
       2 (4 P2/12) + P1/12 when a1 - a0 is 0 or 1, and 2 (P1/12) + 2 (P1/6) when a1 - a0 = 2 (count of facet strategies
       by type in `nash_core.facet_weights`), so f(0) = f(1) holds exactly.
     - Relabel kernels by K'(b | a0, a1) = K(b | a1 - 1, a0), a bijection of stochastic kernels. Then
       p_0(K')(a, b) = sum_{a0} mu(a, a0 + 1) K(b | a0, a) = p_1(K)(a, b), since mu(a, a0+1) = f(a0 + 1 - a) =
       f(a - a0) = mu(a0, a) by f(1 - u) = f(u).
     - Likewise p_1(K')(a, b) = sum_{a1} mu(a1, a) K(b | a - 1, a1) = p_0(K)(a - 1, b).
     - Hence D(q'_0 || p_0(K')) + D(q'_1 || p_1(K')) = D(q_1 || p_1(K)) + D(q_0 || p_0(K)), so Phi(D B) = Phi(B).
     - Numerically Phi(D B) = Phi(B) to 1e-9 on random B (EM).
   - D shifts (f1, f2) by (pi/3, 2 pi/3), so f1 is restricted to [0, pi/3].
   - Column permutations relabel b, which gives the region R = {|Bt00| >= |Bt01| >= |Bt02|} (`nash_core.outside_R`).
2. **Local certificates (`../nash_local_gs_*.json`, `nash_bb.inside_locals`).**
   - They are Gram-Schmidt cubes |z|_inf <= 0.1 around the DKZ copies (6,4,14) and (6,0,6), and the copies
     (6,8,22) and (6,8,-2) by symmetry.
   - On each cube g <= S0, with equality only at the copy. (These are earlier results; see `../NOTES.md`.)
   - **Coverage must be checked:** every global maximiser in D' ∩ R must lie inside one of these cubes.
3. **The tracking bound (`track.py`, `box_bound_track`).**
   - On a box c + [-h, h], take the kernel model K(y) = K0 + R (q(y) - q(c)).
     - K0 is an exact dyadic stochastic kernel, with exact zeros on a face Z.
     - R is a 27 x 18 matrix of exact floats on the grid 2^-30, with zero rows on Z and exact zero b-sums.
       So every K(y) has row sums exactly 1.
   - Then p(y) = p0 + Lam dq(y), with Lam = P R and dq = q(y) - q(c). So p is affine in q(y), and
     g_K(y) = G(q(y)) for the convex function G(q) = (1/2) sum_c q_c log(q_c / p_c(q)).
   - **Exact identity (Bregman divergence of G).** With r0 = q(c)/p0 and w = grad G(q(c)):
     - g_K(y) = F + w.dq(y) + (1/2) sum_c d(q_c(y), r0_c p_c(y)), where d(a, b) = a log(a/b) - a + b >= 0.
     - w_k = (1/2)(log r0_k + 1) - (1/2) sum_c r0_c Lam_ck.
     - q_c(y) - r0_c p_c(y) = (E dq)_c, with E = I - diag(r0) Lam.
   - **Bounds used:**
     - w.dq = Gr.t + (1/2) t^T (sum_k w_k q_k''(xi_k)) t. This is Taylor with a mean value per cell.
     - Shifts: dq(y) lies in W = {zero row and column sums in each x-block} exactly. So w, the rows of E and the rows
       of R may be shifted by alpha_{x,a} + beta_{x,b}, and these shifts are added as intervals.
     - d(a, b) <= kappa (a - b)^2, with kappa = min(1/b_lo, 1/(2 min(a_lo, b_lo))). This uses h(u) = u log u - u + 1
       <= (u-1)^2 and h(u) <= (u-1)^2/(2 min(u, 1)).
     - (E dq)_c = e_c.t + eps_c, with |eps_c| <= (1/2) sum |(E q''(box))_c,ij| h_i h_j, and
       (e.t + eps)^2 <= (1 + eta)(e.t)^2 + (1 + 1/eta) eps^2.
     - QP: `nash_core3.qp_bound` (Gershgorin, certified isotropic eigenvalue, Lagrangian dual with interval Cholesky).
   - **Validity:** K(y) >= 0 on the box, checked entrywise as K0_e - sum_i |(R q'(c))_e,i| h_i - (1/2) sum
     |(R q''(box))_e,ij| h_i h_j >= 0 off the face. Then K(y) is a local model, so Phi(y) <= g_K(y).
4. **Interval arithmetic (`../nash_iv.py`):** outward rounding by nextafter, and rigorous log, sin and cos (series with
   remainders). `track._matvec_iv` multiplies exact float matrices by IV arrays with a gamma_n error bound.
5. **Certification:** a box is certified when ub < S0.lo (S0 is an mpmath interval enclosure).
