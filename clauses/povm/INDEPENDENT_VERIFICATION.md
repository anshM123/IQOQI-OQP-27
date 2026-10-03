# Re-verification report: POVM optimality certificates, d = 3..8 (P1_povm_numerics)

Date 2026-10-02. Scripts and logs in this folder (`ref_verify.py` + `ref_verify_d3..d8.log`, `ref_objective.py` +
`ref_objective.log`, `ref_numeric.py` + `ref_numeric_d3..d8.log`, `tamper.py` + `tamper_d3.log`, `tamper_d4.log`,
re-runs of the original checker `their_verify_*.log`).

**Verdict: no error, no gap.** For d = 3..8, every D and all d-outcome POVMs on Phi_D, I_d <= I_ME(d); equality forces
projectivity, after which Theorem B (PVM rigidity) applies. All five items CONFIRMED.

1. **Soundness of the relaxation -- CONFIRMED.** Every POVM strategy on Phi_D gives p(a,b|x,y) = tau(E^x_a E^y_b),
   tau = Tr/D (Alice's POVMs at positions 0, 2; Bob's transposed POVMs, still POVMs, at 1, 3). Z^g_n = sum_a w^{na}
   E^g_a is an invertible change of variables; the only relations used are Z^g_0 = 1 (effects sum to 1) and
   (Z^g_n)* = Z^g_{-n} (Hermitian effects): the identity lives in the free algebra of POVM effects. Doubly-localizing
   terms: with E = E^0_c >= 0, F = (B^0_0)^T >= 0, tau(f* E f F) = tau((E^{1/2} f F^{1/2})*(E^{1/2} f F^{1/2})) >= 0 by
   cyclicity. Symmetrisation re-derived independently: the generated group (rho, sigma, transposition) has exactly 16d
   elements and induces L(u) = w^{sum t[g] n} L(f(u)), as both checkers use (rho shifts E^0 as E'^3_a = E^0_{a-1});
   S_op is invariant under all 16d elements (modulo rotation, checked exactly), so the direct sum of images is an
   admissible strategy with the same S. No idempotence or group law: words are only concatenated; a float test on
   random full-rank and rank-1 POVMs, PVMs, DKZ (x) 1_2 and noisy DKZ, without any word reduction, gives
   S - lambda = sum_b tr(X^b G^b) within 3e-14 for d = 3..8 with every term >= 0 (without symmetrisation the identity
   fails by up to ~2.6, so the symmetry relations are used, and they are valid).
2. **Identity and positivity -- CONFIRMED for every d = 3..8 (in full).** Own checker (`ref_verify.py`, no imports from
   the original): own parser; arithmetic in Z[x]/(x^N - 1), reduced modulo Phi_N only at the zero test; S_op built from
   the definition via the Fourier coefficients of the sawtooth; orbits from the whole group with different canonical
   forms. The identity holds exactly orbit class by orbit class (classes / expanded terms: 45/4396, 124/17969,
   269/52830, 502/127657, 842/270152, 1312/518961, same counts as the original). Positivity by a third method: rigorous
   interval enclosures of the 2k x 2k real embedding, a rational midpoint, exact rational LDL of M_q - mu I with
   mu >= ||M - M_q||_2; every pivot positive (smallest 1.56e-4 at d = 8). lambda checked exactly without inverses
   (4 - 2 lambda/(d-1) = I_ME(d), multiplying through by prod_j (zeta^j + zeta^{-j})).
3. **Link to the literal CGLMP expression -- CONFIRMED.** Own literal I_d on all d^4 deterministic points, d = 3..10:
   only the 'swap both settings' relabelling satisfies I_d(p') = 4 - 2 S(p)/(d-1); chain form S = d Pi - 1 and local
   maximum 2 hold; both sides affine and the local polytope full-dimensional in the no-signalling set, so the identity
   holds for every quantum behaviour. Relabelling settings is a bijection of strategies on the same Phi_D: the
   supremum is unchanged; projectivity is label-independent; Theorem B is applied to the unswapped strategy.
4. **Equality case -- CONFIRMED.** If S = lambda every term vanishes; Y_c > 0 gives N_c* H^c N_c = 0, hence
   tau(|E^{1/2} f F^{1/2}|^2) = 0 and, the trace on the direct sum being faithful, E f F = 0 in every block. Exact
   elimination over Q(zeta_N): Z^0_n - w^{nc} and Z^1_n - 1 lie in range(N_c) (12/24/40/60/84/112 vectors, d = 3..8);
   rho^4 is the uniform outcome shift, so the relations hold for all (c, b); Fourier inversion and marginalisation make
   E^0 and E^1 projective, and the rho, rho^2 images do the same for E^2, E^3. Theorem B needs exactly a projective
   strategy on Phi_D attaining I_ME for the literal I_d: the use of A2 is legitimate.
5. **Code reading and tamper tests -- CONFIRMED.** No decision on floats in `verify_povm.py` (its one float comparison
   is redundant with the following exact check); pivot signs by mpmath intervals; Hermiticity checked exactly; the
   generators cannot affect soundness (everything is re-verified from the pickle). Original checker re-run: exact mode
   d = 3, 4, 5 and interval mode d = 6, 7, 8: VERIFIED. Tamper tests (d = 3, 4): untouched copy accepted by both
   checkers; eight tampers rejected by both (Hermitian change 2^-60 in Y, 2^-60 on a doubly-localizing diagonal, a
   kernel entry, lambda + 1e-12, a changed letter, swapped letters, a shifted doubly-localizing label, a dropped block);
   Y - 10 I rejected by the exact LDL, the interval Cholesky and the independent checker.

Minor (non-blocking): the original equality check assumes each doubly-localizing element has coefficient 1 (true in all
six pickles); STATUS 2.2(b) should state the rho shift direction (E'^3_a = E^0_{a-1}); the numerical sections of
STATUS (sweeps, SDP values) were not re-checked (the proof does not use them).
