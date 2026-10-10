# The noise clause for covariant strategies, d = 5, 6, 7

Ansh Mishra, Aryan Senthilkumar. 2026-10-10.

**Status:** proved, computer-assisted.
- **Inputs:** exact facet lists, exact dual certificates, and ledger input A2.
- **Re-checks:** the facet lists and the ratio bounds are re-checked by separately written code with a different
  relaxation (rational certificates).
- **Review:** not reviewed by outside experts.

Notation as in [`../noise-dkz-threshold/THEOREM.md`](../noise-dkz-threshold/THEOREM.md):
- v_c(p) is the white-noise critical visibility against all Bell inequalities of the (2,2,d) scenario;
- I_ME(d) is the maximal CGLMP value on maximally entangled states, and κ_d = I_ME(d)/2.

## Theorems

A behaviour is **covariant** if p(a + s, b + s | x, y) = p(a, b | x, y) for all s ∈ Z_d.
- This covers every DFT + diagonal-phase strategy (the class of 27B (i)), with any inert ancilla.
- We checked it directly from the state for d = 3, 5, 6: max |p(a+1, b+1) − p(a, b)| < 2e-15.

**Theorem C5 (d = 5).** Let p be the behaviour of a maximally entangled strategy with balanced projective measurements
(projectors of rank D/5 on Φ_D, any D). Suppose p is covariant, or a relabelling of a covariant behaviour. Then
v_c(p) ≥ 2/I_ME(5) = 0.6871566…, with equality if and only if p is the DKZ_5 behaviour up to relabelling.

**Theorem C6 (d = 6).** The same, with v_c(p) ≥ 2/I_ME(6) = 0.6848838… and equality only for DKZ_6.

**Theorem C7 (d = 7).** The same, with v_c(p) ≥ 2/I_ME(7) = 0.6832559… and equality only for DKZ_7.

So within covariant strategies, and in particular among all DFT + diagonal-phase measurements, DKZ has the highest
resistance to white noise of the violation of local realism, for d = 5, 6, 7.

**What is not claimed.**
- This does not settle the clause for general (non-covariant) strategies at d ≥ 5. Twirling only increases v_c, so the
  covariant case does not reduce the general one.
- For d ≤ 4 the general clause is proved in [`../noise-literal/`](../noise-literal/) (d = 3) and
  [`../noise-complete-vn/`](../noise-complete-vn/) (d = 4).

## Reduction

- **Link-difference laws.** A covariant behaviour is determined by its link-difference laws Q_xy(m) = P(b_y − a_x = m).
  Use the cycle coordinates n1 = b0 − a0, n3 = a1 − b0, n4 = b1 − a1, n2 = a0 − b1.
- **The cyclic polytope.** These satisfy n1 + n2 + n3 + n4 = 0 on deterministic points, and the covariant part of the
  local polytope is

  L ∩ Cov = twirl(L) = K_d := conv{(e_{n1}, e_{n2}, e_{n3}, e_{n4}) : n1 + n2 + n3 + n4 ≡ 0 (mod d)}.

- **Formula for v_c.** For covariant p, every point u + v(p − u) is covariant. Writing the facets of K_d as
  F_f = Σ_i c_i(n_i) ≤ 0,

  v_c(p) = min over the facets f with F_f(p) > F_f(u) of (0 − F_f(u))/(F_f(p) − F_f(u)).

- **The criterion.** The noise clause restricted to covariant behaviours holds at d if and only if, for every facet class,
  the maximally entangled ratio R(f) = (max_ME F_f − F_f(u))/(0 − F_f(u)) is at most κ_d. Equality must occur only for
  CGLMP, and only at DKZ.
- **Class functions.** The ratio is constant on the orbits of the physical relabellings:
  - zero-sum translations (outcome shifts);
  - units of Z_d (outcome multiplications);
  - the dihedral group on the cycle order (n1, n3, n4, n2) (setting and party swaps).

  This is checked in `kd_facets.py`.

## The facets of K_d

| d | vertices / dim | facets | classes (size, tight vertices) |
|---|---|---|---|
| 2 | 8 / 4 | 16 | CHSH (8, 4), positivity (8, 4) |
| 3 | 27 / 8 | 66 | CGLMP_3 (54, 10), positivity (12, 18) |
| 4 | 64 / 12 | 216 | CGLMP_4 (128, 20); tent c = −min(n, 4−n) (64, 16); parity-lifted CHSH c = −(n mod 2) (8, 32); positivity (16, 48) |
| 5 | 125 / 16 | 1020 | CGLMP_5 (500, 35); N5: c1 = c2 = c3 = (0,−6,−2,−3,−4), c4 = (0,4,3,2,6) (500, 26); positivity (20, 100) |
| 6 | 216 / 20 | 2462 | CGLMP_6 (432, 56); f = (0,1,2,1,2,1) (864, 34); f = (0,2,1,3,2,1) (432, 44); f = (0,2,4,3,2,1) (432, 41); tent (216, 36); CGLMP_3 lifted by n mod 3 (54, 80); parity CHSH (8, 108); positivity (24, 180) |
| 7 | 343 / 24 | 24724 | 8 classes: positivity (28), CGLMP_7 (2058), and six others (5488, 8232, 2058, 2058, 2744, 2058) |

**How the lists were obtained.**
- **d ≤ 6:** exact double description (`kd_facets.py`, with the exact double-description code `IND_dd.py`).
- **d = 4, …, 7:** an exact symmetric adjacency decomposition, with the completeness criterion Theorem V
  ([`../noise-complete-vn/THEOREM.md`](../noise-complete-vn/THEOREM.md)) (`kd_adjacency.py`). The ridge
  double descriptions were done twice, by `IND_dd.py` and by the separately written `dd_numba.py`, with identical results.
- **d = 4, 5:** also by a naive exact double description in Python integers (`kd_check.py`, `kd_check_sets.py`), with
  identical facet sets.

**The CGLMP-type classes.**
- For d ≤ 6, every non-positivity class has, in its canonical representative, the subadditive form
  f(n1) + f(n2) + f(n3) ≥ f(n1 + n2 + n3), for a subadditive f on Z_d with f(0) = 0. For CGLMP, f(n) = (−n) mod d.
- The CGLMP-type class is exactly the CGLMP inequality in its Π-form:
  - at d = 5, checked on all 625 deterministic points (`kd_check_orbits.py`);
  - for d = 6, 7, the class contains the Π-form facet (`kd_cglmp_ident.py`).
- Its ratio is I/2 ≤ κ_d, by input A2 (the maximally entangled CGLMP theorem with rigidity, any D;
  [`../../papers/math`](../../papers/math), Theorems A and B).

## Ratio bounds for the other classes

Each non-CGLMP, non-positivity class needs R(f) < κ_d.
- **Upper bounds:** a level-2 tracial moment relaxation (`kd_sdp.py`).
  - It uses clock unitaries U_g with U_g^d = 1, balanced; τ(w) = τ(reverse w); and words of length ≤ 2.
  - It is block-diagonal by charge, because the simultaneous outcome shift multiplies a moment by a phase and keeps all
    constraints.
- **Certification:** each bound is turned into an exact dual certificate by `kd_cert_run.py`:
  - dyadic dual matrix, exact LDLᵀ positive-definiteness;
  - ball arithmetic for the irrational objective coefficients.

| d | class | certified upper bound on R | κ_d |
|---|---|---|---|
| 5 | N5 | 1.43059302 | 1.45527240 |
| 6 | f = (0,2,1,3,2,1) | 1.41421497 | 1.46010180 |
| 6 | f = (0,2,4,3,2,1) | 1.43646849 | |
| 6 | tent | 1.41421426 | |
| 6 | CGLMP_3 lifted | 1.43646795 | |
| 6 | parity CHSH | 1.41421741 | |
| 6 | f = (0,1,2,1,2,1) | 1.38161168 | |
| 7 | class 2 | 1.24163832 | 1.46358047 |
| 7 | class 3 | 1.38981986 | |
| 7 | class 4 | 1.44379755 | |
| 7 | class 5 | 1.44193792 | |
| 7 | class 6 | 1.24163487 | |
| 7 | class 7 | 1.42708466 | |

Every bound is below κ_d. Positivity facets have ratio 1. So every facet term in v_c(p) is at least 1/κ_d, with equality
only through a CGLMP facet at DKZ. This proves Theorems C5–C7. ∎

**Lower bounds.** The bounds are nearly tight: best DFT + phase strategies (`kd_ratio.py`, `kd_lower67.py`) reach, for
example, 1.43059294 for N5. The relaxation also reproduces κ_3, κ_4 and √2 exactly on the d = 3, 4 classes.

## Separate re-check of the ratio bounds

`kd_check.py` imports nothing from `kd_facets.py`, `kd_sdp.py` or `IND_dd.py`. It uses a different relaxation:
- projector words of length ≤ 2, with all moments real by the transpose symmetry;
- completeness Σ_a P^g_a = 1 imposed on the moment-matrix columns, and balancedness τ(P) = 1/d;
- no charge reduction.

Its certificates are fully rational: integer data, Z′ + sI = LLᵀ + R with L integer and R exactly diagonally dominant.
It certifies:
- **d = 5:** N5 ≤ 1.43166;
- **d = 6:** the six classes ≤ 1.39063, 1.41727, 1.43875, 1.41753, 1.44104, 1.42335;
- **d = 7:** the six classes ≤ 1.24886, 1.39106, 1.44503, 1.44351, 1.24889, 1.42813.

All of these are below κ_d.

## Scope and outlook

- **d = 8.** The adjacency decomposition finds at least 38 classes for K_8; the run was stopped by hand
  (`logs/kd_adjacency_d8.log`).
- **Observed pattern, not proved:** for 4 ≤ d ≤ 7, every non-CGLMP class has ratio below κ_{d−1}.
- An all-d statement would need the structure of all facets of K_d, which is closely related to Gomory's master cyclic
  group polyhedra, together with a uniform ratio bound.

## Priority

As far as we found (web, arXiv and the openai/math release, 2026-10-10), the noise clause for covariant strategies had
not been settled for any d ≥ 5. We make no claim about the facet lists of K_d themselves: K_d is closely related to
Gomory's master cyclic group polyhedra, whose facets have been studied extensively, and we did not search that literature
specifically.
