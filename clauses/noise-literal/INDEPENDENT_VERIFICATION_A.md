# Re-verification report A: Theorem 1 of `noise-literal/THEOREM.md` (ledger A3b)

Date 2026-10-02. Full record: scripts and logs in this folder; snapshots of the two P2 versions
checked in `snapshot/` (12:46) and `snapshot_v2/` (13:14) with hashes in `snapshot_sha256.txt`. Main logs:
`verify_run2_current.log`, `break_tests.log`, `ref_facets_compare.log`, `ref_competitor.log`, `ref_dkz.log`,
`ref_prop11.log`.

## Overall verdict
**Theorem 1 is correct as stated; no ERROR.** It concerns projective strategies on Phi_d (zero projectors allowed),
Gill's uniform-outcome noise, and violation of the whole local polytope L(2,2,d). Parts (a), (b), (c) CONFIRMED for every
d >= 4. Remaining items are attribution/wording (G2, G4); G1 and G3 were fixed by the author during the review.
Verifier: 11 items / 0 failures (12:46 version), 16 items / 0 failures, 140 s (13:14 version).

Scope caveat for the ledger (not an error): the counterexample exploits a known artefact of the uniform-outcome noise
model (ADGL 2002 concluded that "the resistance to noise is not a good measure of non-locality"): the noise puts weight
1/d on outcomes the competitor never produces, and v_c(C_d) ~ 4/((sqrt2 - 1) d) -> 0. Theorem 1 refutes the literal
clause only; it says nothing about rank-one PVMs, where u equals white noise (ledger C2) -- THEOREM.md states this.

## Verdict per claim
1. **Definitions vs the historical wording and Gill (math/0610115) -- CONFIRMED.** Gill (p. 140) mixes the
   distribution with "completely random, uniform outcomes" and asks for violation of local realism (leaving the whole
   polytope): exactly u and v_c of THEOREM.md. Gill's sentence behind the clause (p. 144) places no restriction on the
   measurement class, so PVMs with zero projectors are legitimate d-outcome measurements under the literal reading, and
   the noise still produces those outcomes. The POVM variant (S3b, full-rank effects) and the full-support PVMs on
   Phi_D (S3c) remove the zero-effect objection (checked by hand; secondary).
2. **Competitor C_d.** Lemmas 1-3 CONFIRMED (re-derived by hand; independent exact Q(sqrt2) code reproduces the
   behaviour from the projectors for d = 3..12). Lemma 4 (1116 facets of L(2,2,3)) CONFIRMED by an independent double
   description in different coordinates (outcome 0 dropped) with an algebraic adjacency test, identity and reversed
   order: 1116 facets, exactly verified, tight-vertex families identical to facets223.txt; Collins-Gisin 2004 gives
   1116 = 36 + 648 + 432 (labelled 3322 there, but the 36 positivity faces show it is 2233); spot checks: I2233, the
   coarse-grained CHSH, BRIEF's CGLMP_3 are in the list. Proposition 5 CONFIRMED with an independent certificate (exact
   real-root isolation of G conj(G) in Q[t] plus exact signs between roots): all 1116 G_F >= 0 on [0, 1/3], exactly 8
   vanish identically (the lifted-CHSH facets equivalent to f_c on CH, n_t, delta_0). Facet-free check: exact local
   models at v* with weights in Q(sqrt2) for d = 3..24 (both constructions), lifted to exact full d-outcome models for
   d = 4, 5; float LP agrees with the closed forms to ~1e-16 (d = 4..9). REF_noise_B's analytic flag model also proves
   (a) for all d without a facet list (weights re-checked by hand). Formulas v_even, v_odd CONFIRMED.
3. **DKZ lower bound.** Lemma 6 (1/2-lemma) CONFIRMED (same construction P1 = p00 (x) p11, P2 = p01 (x) p10; exact
   check d = 2..6; fails without uniform marginals; PR box shows 1/2 is sharp). Lemmas 7-9 CONFIRMED (Lemma 7: the
   theorem's DKZ strategy is the CGLMP-paper strategy with Bob's settings swapped, same v_c, value I_ME; Lemma 8:
   explicit local model built and checked exactly for d = 3, 4, 5; Lemma 9: identity re-derived, S >= 0 iff
   |E| <= (v1 - v0)/(2 d^2 v0)). Proposition 10 CONFIRMED: all 18 certificates (d = 3..20) re-verified with mpmath
   interval enclosures at 200 bits (margins ~1e-13 vs errors ~1e-15; 2/I_ME - v0 in [1.00e-7, 1.01e-7]). New
   Proposition 11 (v_c(DKZ_d) = 2/I_ME(d) exactly for d = 3, 4, 5) CONFIRMED without any facet list (exact local models
   in Q(zeta_{8d}), all 4d equations exact; minimum weights 0.143, 2.9e-3, 5.1e-3). Final comparison CONFIRMED, no
   gaps: certificates cover d = 4..9, the 1/2-lemma covers d >= 10 (v_comp < 1/2 checked exactly for d = 10..10^4,
   analytic tail re-done: 81 sqrt2 - 113 > 0; 4(sqrt2 + 1) = 9.657); fails at d = 8, 9 as THEOREM.md says.
4. **Verifier -- CONFIRMED.** No float decides an exact item (C7, C10, S4 are informational floats counted in OVERALL;
   they can only cause a false FAIL). C1 + C5 + C9 together check what the theorem states; C2-C4 cover d = 4..9 for
   lemmas proved by hand for all d. Tamper tests 11/11 as expected: moving 1e-10 of mu between atoms -> C8 fails; v1
   above 2/I_ME(4) -> C8 fails; deleting or weakening a facet -> C1 fails (C5 alone still passes on deletion because it
   trusts the list; C1 guards); wrong v_odd -> C3 fails; wrong observables -> C2 fails; broken 1/2-lemma model -> C6
   fails; false r(9) -> C9 fails; the Bernstein test has teeth (a 10% CGLMP-type admixture makes exactly one facet
   reject the CHSH-based v*; it also rejects (t - 1/6)^2 - 1e-9). Harmless: `exact.py` sine bound invalid at r = 1/2
   exactly, never called there.
5. **Attribution.** ADGL eq. (14) CONFIRMED (lambda = (1 - ((d-2)/d)^2)/(sqrt2 - ((d-2)/d)^2) = v_even(d) exactly;
   Crossref PRA 65, 052325). Baek-Ryu-Lee CONFIRMED (R_w = 0.448 vs 0.552; d = 16 chain ending at 1.7673 = v_even(16);
   no mention of Gill or OQP 27; Crossref NJP 27, 053001).
   **G2 -- GAP (fixable):** add the original numerical DKZ full-polytope thresholds: Kaszlikowski-Gnacinski-Zukowski-
   Miklaszewski-Zeilinger PRL 85, 4418 (2000) (N <= 9); Durt-Kaszlikowski-Zukowski PRA 64, 024101 (2001) (OQP ref. [2],
   N <= 16); CGLMP 2002 eq. (23). Credit Gruca-Laskowski-Zukowski 2012 also for finding that Schmidt-rank-2 states are
   the most noise-robust. Note that ADGL's settings are two-outcome, so exactness there is elementary; exactness in the
   d-outcome scenario is Prop. 5. Add "as far as we found" to novelty claims. Chen et al. PRA 64, 052109 (2001) gives an
   analytical result for N = 3 (not checked whether it contains a local model), so d = 3 lower-bound novelty is
   uncertain.

## Remaining wording items
- G1 -- fixed during review (the 12:46 claim 'fails on every Phi_D with D even' was ill-posed when d does not divide D;
  the 13:14 version replaces it by item (d), a comparison of numbers; v_even(d) < v_odd(d) checked for all d). Nit: (d)
  says "every d >= 3, every even D" under the header "Let d >= 4 and D = d".
- G3 -- fixed (Supplements S1-S4 written; S1, S2, S3b read: no error, given Theorems A and B of main.tex).
- G4 -- cosmetic: "main.tex Theorem A" is cited for I_d(DKZ) = I_ME(d); that value is a direct computation (CGLMP 2002).

## Comparison with REF_noise_B
Agreement on every mathematical point. B reports no gap; A lists G2, G4. B's report predates Proposition 11, which A
confirmed independently.
