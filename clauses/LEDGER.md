# OQP 27: clause-by-clause ledger

Status as of 2026-10-02. A clause is marked PROVED or FALSE only with a rigorous proof or a rigorous counterexample that
has been re-checked in a separate verification pass. These are internal checks, not peer review: none of the results
below has yet been reviewed by outside experts. Other statuses: NUMERICAL (strong numerical evidence only), OPEN.

## The problem as posed

IQOQI Vienna Open Quantum Problem 27, "The power of CGLMP inequalities" (proposed by R. Gill, 2006), in the setting of
two parties, two settings and d outcomes
([archived page](http://web.archive.org/web/20231029013544/https://oqp.iqoqi.oeaw.ac.at/the-power-of-cglmp-inequalities)):

> **Problem 27.A** Show that every face of the local polytope, which is not already contained in a face of the
> no-signalling polytope is of CGLMP type, i.e., an inequality of the form first written out in [1], but possibly lifted
> from lower dimensions by fusing together some outcomes.
>
> **Problem 27.B** Numerically, the observables maximally violating the CGLMP inequality on a maximally entangled state
> are of a very specific form [2], involving measurements in computational basis, transformed by only discrete Fourier
> transformation and diagonal unitaries [1]. Show that this is necessarily the case. Show also that these measurements
> realize the highest resistance of violation to noise, and the best discrimination against classical realism in the
> sense of Kullback-Leibler divergence [3].

([1] Collins, Gisin, Linden, Massar, Popescu, PRL 88, 040404 (2002); [2] Durt, Kaszlikowski, Zukowski, PRA 64, 024101
(2001); [3] van Dam, Grunwald, Gill, quant-ph/0307125.) In Gill's paper behind the problem (R. Gill, "Better Bell
inequalities (passion at a distance)", IMS Lecture Notes 55 (2007), arXiv:math/0610115), noise resistance means how
much the behaviour can be mixed with "completely random, uniform outcomes" while local realism is still violated.

Formal Conjectures issue #3444 (google-deepmind/formal-conjectures) formulates Part B with the maximally entangled state
Phi_d of C^d (x) C^d, complete von Neumann d-outcome measurements, the CGLMP functional of the problem page, and white
noise on the state for the noise clause. For complete von Neumann measurements on Phi_d, Gill's uniform outcome noise
and white noise on the state give the same behaviours (`noise-literal/THEOREM.md`, Lemma S3a).

## A. The clauses as posed

| Clause | Status | Proof / counterexample | Credit |
|---|---|---|---|
| **27A** every non-trivial facet of the (2,2,d) local polytope is of CGLMP type | **FALSE** | d = 4 has non-CGLMP facets | Bancal, Gisin, Pironio, J. Phys. A 43, 385303 (2010) (prior work, not ours) |
| **27B (i)** the observables maximally violating CGLMP on a maximally entangled state are necessarily the DKZ (DFT + diagonal unitaries) measurements | **PROVED for every d** (computer-assisted for d >= 21): optimal for every local dimension D and all projective measurements, and the unique optimum up to local unitaries u (x) conj(u) and an inert ancilla (d \| D) | `../papers/math`, Theorems A and B; Lean `../lean/` (complete for 2 <= d <= 20; every d given the certified cone condition CONE_d for d >= 21, `../cone-certificates/`); Lean `../formal-conjectures-27/` (formulation of issue #3444) | this work |
| **27B (ii)** "highest resistance of violation to noise", for the **CGLMP** violation, with white noise on Phi_d (equivalently, uniform outcome noise) | **PROVED for every d** (same status as 27B (i)): the threshold of every projective strategy is 2/I_d >= 2/I_ME(d), with equality only for DKZ | `noise-cglmp/THEOREM.md`; Lean `../lean/OQP27/CglmpNoise.lean` and `../formal-conjectures-27/` (`dkz_noise_of_le_twenty`, `dkz_noise`) | this work |
| **27B (ii)** for the violation of **local realism** (all Bell inequalities), complete von Neumann measurements on Phi_d (white noise = Gill's uniform outcome noise) | **OPEN for d >= 5.** True for d = 2, d = 3 (`noise-literal/THEOREM.md`, Theorem 3) and d = 4 (`noise-complete-vn/`: complete facet list of L(2,2,4), computer-assisted, independently re-implemented); NUMERICAL for d <= 8 (DKZ optimal in all global searches). Proved parts for d >= 5: for every d, DKZ's own threshold is exactly 2/I_ME(d) and DKZ is a strict local optimum (`noise-dkz-threshold/`); for d = 5, 6, 7, DKZ is optimal among all covariant strategies, including every DFT + diagonal-phase strategy (`noise-covariant/`) | `noise-literal/THEOREM.md`, Supplements S1 and S3; `noise-complete-vn/` | this work (d = 3, 4) |
| **27B (ii)** for the violation of **local realism** with Gill's uniform outcome noise, when measurements may have outcomes that never occur (zero projectors), or are POVMs | **FALSE for every d >= 4**, on Phi_d itself: an explicit projective strategy with d - 2 unused outcomes has critical visibility 4(d-1)/(4(d-1)+(sqrt2-1)d^2) (even d), 4/(4+(sqrt2-1)d) (odd d) and beats DKZ, whose critical visibility is >= 1/2 for every d and within 1.02e-7 of 2/I_ME(d) for d = 3..20; small perturbations give full-rank POVMs that use every outcome. (d = 2: true; d = 3: true on Phi_3, false on Phi_2.) This does not decide the row above. | `noise-literal/THEOREM.md` (Theorem 1, Proposition S3b), verifier `noise-literal/verify_theorem.py` (17 checks); two re-verifications `noise-literal/INDEPENDENT_VERIFICATION_A.md`, `..._B.md` | this work (exact theorem for every d). The effect was observed before: Acin, Durt, Gisin, Latorre, PRA 65, 052325 (2002), eq. (14) (the even-d threshold for a Schmidt-rank-2 state); Baek, Ryu, Lee, New J. Phys. 27, 053001 (2025) (numerical, d = 4 and 16) |
| **27B (iii)** best discrimination in the Kullback-Leibler sense | **FALSE for every d >= 4**: explicit orthonormal-basis (complete von Neumann) strategies on Phi_d have statistical strength >= 0.0703204 bits > 0.0687803 >= S(DKZ_d) (all three van Dam-Grunwald-Gill strengths). **OPEN for d = 3** (see B) | `kl-divergence/THEOREM.md`; re-verification `kl-divergence/INDEPENDENT_VERIFICATION.md` | d = 4 first by Y. Zhang (Zenodo, 2026, doi:10.5281/zenodo.23022433); every d >= 4: this work |

**Summary.** 27A is false (2010). 27B (i) is proved for every d (projective measurements; computer-assisted for d >= 21).
27B (ii) is proved for the CGLMP violation under white noise; for the violation of local realism with complete
von Neumann measurements it holds for d <= 4 and is open for d >= 5 (for d >= 5 we prove DKZ's exact threshold for every d,
its strict local optimality, and its optimality among covariant strategies for d = 5, 6, 7), and false for every d >= 4 once unused outcomes or POVMs are allowed. 27B (iii) is
false for every d >= 4 and open for d = 3. None of these results has yet been reviewed by outside experts.

## B. Precise variants

| Variant | Status |
|---|---|
| 27B(ii) with white noise on the state, CGLMP witness, projective measurements whose outcomes have unequal ranks (the noise is then the product of the marginals, not uniform) | OPEN; no counterexample in rank-pattern searches for d = 3..6 (exhaustive for d = 3 with local dimension <= 9 and d = 4 with local dimension <= 8; largest value 1.98569 < 2) |
| 27B(iii) at d = 3 | DKZ_3 is a strict local maximiser of the strength (PROVED, re-checked); global optimum inside the three-parameter Fourier-shift family F3, for all three strengths (PROVED, computer-assisted, `kl-divergence/fourier-family/`); global optimality over all PVMs NUMERICAL |

## C. Strengthenings (not asked by the problem)

| Strengthening | Status |
|---|---|
| 27B(i) for arbitrary POVMs on maximally entangled states | **PROVED for d = 3..8** (every local dimension; optimal POVMs are projective, hence DKZ up to local unitaries): exact sum-of-squares certificates in a POVM-only relaxation, re-checked, `povm/`; OPEN for d >= 9 |
| Maximum of CGLMP over all states (Tsirelson bound) equals 2(lambda_max(K_d) - 1)/(d - 1), K_d = [sec(pi(k-l)/2d)] | exact for d <= 8 (d = 3, 4 Ioannou-Rosset; d = 5..8 our earlier certificates); OPEN for d >= 9 |

## Labels used in the documents of this folder
A1 = 27A; A2 = 27B(i); A3a = 27B(ii), CGLMP violation; A3b = 27B(ii), violation of local realism with Gill's uniform
outcome noise (the counterexample of `noise-literal/` needs unused outcomes or POVMs); A4 = 27B(iii);
B1 = 27B(ii) with white noise on the state, CGLMP witness, unequal ranks; C1 = POVM strengthening of 27B(i);
C2 = 27B(ii) for the violation of local realism with white noise on the state and every outcome used (for complete von
Neumann measurements on Phi_d this is the open row of Section A); C3 = the KL clause at d = 3; C4 = the all-state
Tsirelson bound. (In the verifier output, items C1-C12 and S1-S4 are check numbers, not these labels.)
