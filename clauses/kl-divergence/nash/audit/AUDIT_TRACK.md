# Audit of the tracking bound (`fast/track.py`) and the Theorem N branch-and-bound (`fast/bb_track.py`)

Date: 2026-10-19, 19:50 to 21:00. This is an independent audit. The claims in `fast/TRACK_METHOD.md` and in the code
comments were re-derived, not taken on trust. All scripts and logs are in this folder (`audit_track/`). No existing
file was edited, and no process of the running B&B was touched.

Notation: ROOT = `iqoqi/programs/oqp27_kl3`, u = 2^-53.
- **Proved** means a pen-and-paper argument given here.
- **Checked numerically** means a float or 60-digit experiment. It is evidence, not proof.

**Not re-audited:**
- the machinery behind the local cube certificates `nash_local_gs_*.json` (Oct 13 code: `nash_local_gs2.py`,
  `nash_tmbound.py`); only their coverage of the copies and their leaf counts were checked;
- Lemma R and Lemma CG;
- the jet library (`nash_core3`, `kl3mix.z3`), apart from a read-through and a 60-digit containment test.

## Verdicts

| Item | Verdict | One line |
|---|---|---|
| 1. Mathematics of the tracking bound | **OK** (proved) | Bregman identity, the kappa inequalities, Young splitting, per-cell Taylor, exact W-shifts and validity are all correct. |
| 2. Implementation versus mathematics | **ISSUE (minor)** | `E = IV(E.lo + eye, E.hi + eye)` (track.py line 246) is not outward-rounded. The exact diag(E) was outside the interval in 2 of 1,368 tested entries. The fix is one line. Everything else is a rigorous enclosure. |
| 3. Domain reduction and coverage | **ISSUE (minor)** | D and conj are exact symmetries (proved), and the copies are covered. But `bb_track.DHI` = float(pi/2, pi, pi/3, 2 pi) lies below the true endpoints, which leaves slivers of width 1e-16 uncovered. The fix is one line. |
| 4. Driver logic | **OK** for soundness. **Major completeness problem** | Certifies only when ub < S0.lo, discards only when outside R is rigorously true, and records unresolved boxes. **But as configured the run cannot finish:** the face rule leaves p0_c = 0 near cells with small q, so track fails there at every box size (see 4(d)). |
| 5. Numerical spot checks | **OK** | 1,149 certified boxes. Max(sample or local maximum of g_K - ub) = -1.6e-3; max(Phi_EM - ub) = -4.0e-3; no violated intermediate inequality. |

**Overall:** see the end of this file. In short:
- the tracking bound is sound, apart from a one-line rounding fix;
- the domain needs a one-line endpoint fix;
- the current run will not finish (near-zero cells), so restart it with the fixes.

---

## 1. Mathematics of the tracking bound: OK (proved)

**Setting.**
- q(y) is in R^18, with index x*9 + a*3 + b. The model is K(y) = K0 + R dq(y), where dq = q(y) - q(c), c is the float
  box centre and q(c) is its exact value.
- p = P K with P[x*9 + a*3 + b, a0*9 + a1*3 + b'] = mu*(a0, a1) [a_x = a][b = b'].
- Hence p(y) = p0 + Lam dq(y) with p0 = P K0 and Lam = P R, so p is affine in q(y).

**1.1 Exact identity.**
- Let f(a, b) = a log(a/b) for a >= 0, b > 0. Then grad f = (log(a/b) + 1, -a/b).
- The Bregman divergence of f is B_f((a, b), (a0, b0)) = a log(a/b) - a0 log r - (log r + 1)(a - a0) + r (b - b0),
  with r = a0/b0. This equals a log(a/(r b)) - a + r b = d(a, r b).
- Bregman divergences pull back under affine maps. So for G(q) = (1/2) sum_c f(q_c, p_c(q)):

      g_K(y) = G(q(y)) = F + w.dq + (1/2) sum_c d(q_c(y), r0_c p_c(y)),
      F = (1/2) sum_c qc_c log r0_c,
      w_k = dG/dq_k = (1/2)(log r0_k + 1) - (1/2) sum_c r0_c Lam_ck.

- Since r0_c p0_c = qc_c, we get q_c - r0_c p_c = dq_c - r0_c (Lam dq)_c = (E dq)_c with E = I - diag(r0) Lam.
- The identity holds whenever q_c(y) >= 0 and p_c(y) > 0. At a = 0 both sides equal r0 b.
- All formulas in the code (F, w, E) match.
- Checked numerically at 50 digits on random instances: error <= 2e-51 (`a1_structure.log`).
- In the spot checks, F + w.dq + (1/2) sum d reproduces the directly computed g_K to <= 2.3e-16.

**1.2 kappa.** Write d(a, b) = b h(a/b) with h(u) = u log u - u + 1.
- (i) h(u) <= (u - 1)^2 for u >= 0.
  - Let phi = (u-1)^2 - h. Then phi(0) = phi(1) = phi'(1) = 0 and phi'' = 2 - 1/u.
  - phi is convex on [1/2, inf), so phi >= 0 there.
  - phi is concave on (0, 1/2] with phi(0) = 0 and phi(1/2) = 0.097 > 0, so phi >= 0 there too.
  - Hence d <= (a - b)^2/b <= (a - b)^2/b_lo.
- (ii) h(u) = int_1^u (u - s)/s ds <= (u - 1)^2/(2 min(u, 1)).
  - Hence d <= (a - b)^2/(2 min(a, b)) <= (a - b)^2/(2 min(a_lo, b_lo)), when a_lo, b_lo > 0.
- In the code:
  - k1 = up(1/m_lo) and k2 = up(0.5/min(q_lo, m_lo)), with k2 = +inf when q_lo <= 0;
  - m_lo = lower end of r0 * p_box, a lower bound for r0_c p_c(y) on the box.
- Both inequalities checked on a dense grid (`a1_structure.log`).
- Young's inequality (x + y)^2 <= (1 + eta) x^2 + (1 + 1/eta) y^2 holds for every eta > 0. The code uses
  eta >= 1e-3.

**1.3 Taylor and mean-value steps, with a separate xi per cell.**
- For each cell k separately, q_k(c + t) = q_k(c) + q_k'(c).t + rho_k(t), where rho_k = (1/2) t^T q_k''(xi_k) t and
  xi_k lies on [c, c + t], inside the box.
- Every bound uses rho only through linear combinations sum_k M_k rho_k with interval coefficients M. Each
  q_k''(xi_k) is enclosed independently by qH[k]. So it does not matter that the xi_k differ.
- The same holds for:
  - p over the box: dq_k = q_k'(xi'_k).t, which lies in qg[k].[-h, h];
  - the nested refinements in `nash_core3.refine` (one mean value per scalar entry).
- The box satisfies [lo, hi] in c +- h and c in [lo, hi]. So every segment stays in the box over which the jets are
  enclosed.

**1.4 W and the shifts: exact.**
- For every real y:
  - sum_b q_x(a, b) = (1/3) ||Bt(y)^dagger a_x||^2 = 1/3;
  - sum_a q_x(a, b) = (1/3) ||Bt(y) e_b||^2 = 1/3.
  - Reason: Bt(y) is unitary for all real CKM parameters, and {a_x}_a is orthonormal.
- Hence dq(y) lies in W for every y. So does every column of q'(c), and so does rho(t) = dq - q'(c) t.
- Take v_k = alpha_{x(k), a(k)} + beta_{x(k), b(k)}. For u in W,
  v.u = sum_{x,a} alpha sum_b u + sum_{x,b} beta sum_a u = 0.
- So adding such a v to w, to a row of E, or to a row of R leaves unchanged: w.dq, (E dq)_c, (R dq)_e, the first-order
  terms and the remainder combinations. This holds exactly, for any real alpha and beta. The code adds float
  alpha and beta as outward-rounded intervals.
- Numerically, the row and column sums of q equal 1/3 to 2.8e-16.

**1.5 Validity.**
- K0 has exact row sums 1, exact zeros on the face, and entries >= 2^-40 elsewhere.
- R has exact zero b-sums and zero rows on the face.
- So for every y: sum_b K(y)(b | a0, a1) = 1 exactly, and the face entries are identically 0.
- For a non-face entry e:
  K(y)_e >= K0_e - sum_i |(R q'(c))_{e,i}| h_i - (1/2) sum_{ij} |(R qH)_{e,ij}| h_i h_j,
  and the same with the shifted rows of R. When the test passes, this is >= 0.
- Hence K(y) is a stochastic kernel and Phi(y) <= g_K(y) on the whole box.
- The test fl(K0 - move) >= 0 is equivalent to K0 >= move for floats (gradual underflow).

**1.6 Assembly and QP.**
- The bound reads g_K(c + t) <= F + Gr.t + (1/2) t^T [H_w(t) + sum_c kappa_c (1 + eta_c) e_c e_c^T] t
  + (1/2) sum_c kappa_c (1 + 1/eta_c) eps_c^2, with H_w(t) in [Hw].
- `nash_core3.qp_bound` bounds the sup over |t_i| <= h_i, H in [Hq] and Gr in [Gr], by three methods:
  - (b1) |t_i t_j| <= (t_i^2 h_j/h_i + t_j^2 h_i/h_j)/2, which gives the scaled Gershgorin bound;
  - (b2) gamma I - H positive definite for all H in [H], by interval Cholesky;
  - (b3) the Lagrangian dual (1/2) g^T (Lam - H)^{-1} g + (1/2) lam.h^2, valid for any lam >= 0 with Lam - H
    positive definite, enclosed by interval Cholesky and forward substitution.
- All three are valid.

---

## 2. Implementation versus mathematics: ISSUE (minor)

**2.1 Conventions: OK.**
- The q index is x*9 + a*3 + b; this is the loop order of `q_float`, `q3` and `z3`.
- The K index is a0*9 + a1*3 + b; this is the `em_kernel` layout.
- `P_F == nash_core.A27` exactly. Each P entry is a single mu, so `_Plo` and `_Phi` bracket the true P.
- `_XA`, `_XB` and `dc_coeffs` match the (x, a, b) layout.
- `tracking_matrix` uses rows r = a0*3 + a1 and entries r*3 + b.

**2.2 Exactness claims: OK** (proved, and checked on every test box).
- `exact_kernel`:
  - all entries are multiples of 2^-52 in [0, 1] and every partial sum is < 2;
  - so `others` and `1 - others` are exact, and the row sum is exactly 1 (the assert also checks this).
- R = D A, with A rounded to the 2^-30 grid and |A| <= 2^20:
  - each entry of R is +-A_j or -(A_j + A_j'), which needs at most 52 significant bits, so it is exact;
  - b-sums are exactly 0 and face rows are exactly 0.
- Checked on 1,000+ boxes: R lies on the grid, b-sums are 0, face rows are 0, K0 rows sum to 1
  (`a0_smoke.log`, `a5_*`).
- The `inspect` copy of `box_bound_track` used by the audit reproduces `ub` bitwise. Rebuilding (K0, face, ref, R)
  from the public functions reproduces it bitwise too.

**2.3 Enclosures.**
- p0: the terms are nonnegative, and the relative padding 64*2^-52 exceeds gamma_27. **OK.**
- Lam = P R: each term is enclosed by [mu_lo, mu_hi] according to the sign of R. The padding is
  27*2^-52*1.01*sum mu_hi |R|, against a needed (gamma_27 + u) sum mu |R|. **OK.**
- `_matvec_iv`: the error of two length-18 dot products plus one addition is at most
  (gamma_18 + u(1 + gamma_18)) sum |M||x|, about 9.5*2^-52 sum |M||x|. The code uses
  18*1.01*2^-52 sum |M||x| + 1e-300 (the extra term covers underflow). **OK**, about 2x conservative.
- r0, F, wv, Gr, Hw0/Hw1 (shift added with outward IV additions), e, Eq2, Es, Eq2s: built from IV operations and
  `V.isum`. **OK.**
- eps: magnitudes times w2 (w2 rounded up), then times (1 + 1e-12), which exceeds gamma_21. **OK.**
- kappa: one rounding, then `up`. **OK.**
- coefq: times (1 + 1e-12). **OK.**
- kc = kappa(1 + 1/eta): three roundings and one `up`, so it can be up to ~2u short.
  - It is still covered, because eps enters squared and carries >= 0.99e-12 of relative slack. **OK**, but the
    coverage is implicit.
  - Suggestion: `V.up(...) * (1 + 1e-12)`.
- `_sep_bound` (nash_core):
  - The vertex test gm <= -gamma h (1 - 1e-12) can choose the end value when the vertex lies inside by less than
    1e-12 h.
  - The resulting underestimate is <= |gamma| (1e-12 h)^2 / 2, about 1e-24 relative. That is far below the float
    spacing of ub near S0 (6.9e-18), so it cannot flip `ub < S0.lo`. **Harmless.**
  - Suggestion: use (1 + 1e-12) in the test.
- **ISSUE (minor): the diagonal of E.**
  - **What goes wrong.** `E = IV(E.lo + eye, E.hi + eye)` adds 1 with round-to-nearest. When |r0_c Lam_cc| << 1, the
    interval for -r0_c Lam_cc is much narrower than ulp(1) (about 1e-19 against 2.2e-16). Both endpoints then
    round to the same float, which can miss 1 - r0_c Lam_cc by up to 2^-53.
  - **Observed** (60-digit reference, `a2_shadow*.log`, `a2d_ediag.log`): 2 of 1,368 diagonal entries in 76
    ordinary B&B leaves were outside their interval, by 3.4e-17 and 1.8e-17. Example: box 16, cell 4 of
    `a2d_ediag.py 60 4`, with E_cc = 0.99999626... and the interval collapsed to a single float. In both cases the
    interval before `+ eye` contained the exact value.
  - **Concrete failure scenario.** A cell with weak tracking (Lam_cc around 1e-6) in an ordinary leaf. This occurred
    in about 1 of 40 boxes.
  - **Downstream.** The quantities that actually enter the bound (e, Es, Eq2, Eq2s) contained their exact values in
    all 76 boxes. This is because `V.isum` adds an a-priori error term ((n + 2) 2^-52 sum |terms|) that exceeds the
    true summation error by >= 2.5e-15 sum |terms|.
  - **Why this is not a proof.** The absorption is not guaranteed in general. Eq2s uses the double-centred rows Es,
    which are small precisely when the tracking is good, so their summation slack can fall below
    2^-53 |E_cc qH_c|. A crude bound on the possible error in ub is kappa (1 + 1/eta) eps 2^-53 |qH| h^2, at most
    about 1e-15. So as written, a certificate with ub within about 1e-15 of S0.lo would not be rigorous.
  - **Fix.** `E = E + IV(eye)`, which uses the outward-rounded IV addition.
  - **Effect of the fix.** With this fix and the two suggestions above (applied in memory), ub changes by at most
    2.4e-14 (relative 6.7e-13) on 950 certified boxes (all four saved sets, including the 200 tightest).
    It never decreases, and no certification flips
    (`a2c_fixes.log`). The change is dominated by the deliberate (1 + 1e-12) on kc.

**2.4 inf and NaN: OK.** I traced every path:
- kappa = inf (m_lo <= 0 or NaN) gives `finite` = False, hence ub = inf;
- eps NaN or inf gives `const.hi` non-finite (IV.sqr of NaN has hi = NaN), hence inf;
- NaN in F or qm gives ub = NaN, and `NaN < S0.lo` is False;
- NaN in Klow gives `valid` = False;
- qc or p0 not > 0 gives `okp` = False, hence inf;
- NaN in Hq makes `np.linalg.eigvalsh` raise, which crashes the call without producing a bound.

Injected tests (`a5b_extra.log`, 120 certified leaves):

| Injected fault | Result |
|---|---|
| NaN in a non-face row of R | exception for 120/120 |
| NaN in a face row of R | exception for all 66 boxes that have a face; the other boxes are unchanged |
| a zero non-face entry of K0 | ub = inf for 120/120 |
| R scaled by 2^12 | ub = inf for 120/120 |
| R = 0 (constant kernel) | finite and sound: sampled g - ub <= -4.7e-3 |

I found no path from inf or NaN to a finite wrong bound. Note, however, that an exception kills the worker
(see section 4).

**2.5 60-digit containment** (`a2_shadow.log`, `a2_shadow_60.log`; 76 leaves).
- Exact values were computed with mpmath at 60 digits; derivatives used steps of 1e-22 and 1e-16.
- Every quantity was inside its interval:
  - qc.v, qc.g and qc.H at the centre, and qv, qg and qH at 3 random points per box;
  - p0, Lam, r0, F, w, the shifted w, e, Gr, Es, Eq2 and Eq2s.
- The only exception is diag(E), as reported above.
- Entries that lie about 1e-323 from an endpoint are structural zeros. For example, the cells with b = 2 do not
  depend on theta12.

---

## 3. Domain reduction and coverage: ISSUE (minor)

**3.1 Structure of mu* (proved exactly)** (`a1_structure.log`).
- Counting the facet weights with integer coefficients gives mu*(a0, a1) = f((a1 - a0) mod 3), with:
  - f(0) = f(1) = P*_1/12 + 2 P*_2/3 = 0.148931;
  - f(2) = P*_1/2 = 0.035472.
- Hence f(m) = f(1 - m) for all m. This is the only property of mu* that the symmetries need.

**3.2 D = diag(1, e^{i pi/3}, e^{2 i pi/3}) is a symmetry (proved).**
- Alice's vectors are |a_x> = 3^{-1/2}(e^{2 pi i k (a + alpha_x)/3})_k with alpha = (1/2, 0). Then:
  - <a_0 | D v> = <a_1 | v>;
  - <a_1 | D v> = <(a - 1)_0 | v>, exactly, with no phase, since e^{-2 pi i k} = 1.
- For q' = q(D Bt): q'_0(a, b) = q_1(a, b) and q'_1(a, b) = q_0(a - 1, b).
- **Kernel map:** K'(b | a0', a1') = K(b | a1' - 1, a0'). This is a bijection of stochastic kernels.
- Then, using mu(a1, a0 + 1) = mu(a0, a1), which follows from f(m) = f(1 - m):
  - p'_0(a, b) = sum_{a0} mu(a, a0 + 1) K(b | a0, a) = p_1(a, b);
  - p'_1(a, b) = sum_{a1} mu(a1, a) K(b | a - 1, a1) = p_0(a - 1, b).
- So g(q', K') = g(q, K), hence Phi(D B) = Phi(B).
- Checked numerically: the q maps to 2.8e-16, g to 4.4e-16, and EM-Phi to 2.6e-16 on random bases.
- D shifts (f1, f2) by (pi/3, 2 pi/3) and leaves theta, delta and row 0 unchanged. Also D^2 = Z.

**3.3 Complex conjugation is a symmetry (proved).**
- conj |a_0> = |(-a - 1)_0> and conj |a_1> = |(-a)_1>.
- So q'_0(a, b) = q_0(-a - 1, b) and q'_1(a, b) = q_1(-a, b).
- **Kernel map:** K'(b | a0, a1) = K(b | -a0 - 1, -a1). The p's relabel the same way because
  mu(-a0 - 1, -a1) = f(1 - m) = f(m) = mu(a0, a1).
- Checked numerically.
- In CKM coordinates conj maps (theta, delta, f1, f2) to (theta, -delta, -f1, -f2), up to column phases. This is
  because every V entry is a real polynomial in e^{+-i delta}.
- Column permutations relabel b. Column phases leave q unchanged.

**3.4 Coverage.**
- Start from any unitary U:
  - permute its columns into R, so that the row-0 moduli decrease;
  - write it in PDG form: theta13 = asin |U02|, theta12 = atan2(|U01|, |U00|), theta23 = atan2(|U12|, |U22|), with
    delta, f1, f2 read off the phases. This is constructive for generic U, and surjective onto U(3) modulo phases by
    compactness and density;
  - if delta > pi, apply conj;
  - then apply D^-k to bring f1 into [0, pi/3).
- Both conj and D keep R, because they leave the row-0 moduli unchanged.
- Checked on 400 Haar bases (`a3_domain.log`): reconstruction error <= 5.6e-16, every reduced point lies in D' and R,
  and Phi agrees to 8e-16 (EM, 5000 iterations).

**ISSUE (minor): float endpoints.**
- **What goes wrong.** `bb_track.DHI` uses `math.pi/2`, `math.pi`, `math.pi/3` and `2*math.pi`. These are below the
  true values:

  | Coordinate | true - float |
  |---|---|
  | theta12, theta13, theta23 | 6.1e-17 |
  | delta | 1.2e-16 |
  | f1 | 1.1e-16 |
  | f2 | 2.4e-16 |

- The theta12 and theta13 slivers lie outside R: theta12 > pi/4 gives |B00| < |B01|, and theta13 near pi/2 gives
  |B02| > |B01|.
- The slivers theta23 in (fl(pi/2), pi/2], delta in (fl(pi), pi], f1 in (fl(pi/3), pi/3] and f2 in (fl(2 pi), 2 pi]
  are covered by no box. Their images under conj, D or 2 pi periodicity fall just below 0, which is also uncovered.
- **Concrete failure scenario.** A maximiser located inside one of these slivers would never be examined. This is
  numerically implausible (Phi is continuous), but the proof as stated does not cover these points.
- **Fix.** `DHI = V.up(np.array([...]))`, as `nash_bb.py` already does, or cover the four upper faces separately.

**3.5 Copies and local cubes** (`a3_domain.log`).
- The orbit of DKZ's two Bob bases under <Z, column permutations, conj> has 72 elements and is closed under D
  (D Bt*_0 = Bt*_1 P and D Bt*_1 = Bt*_0).
- Every copy has all moduli equal to 3^{-1/2}, which forces theta = (pi/4, asin 3^{-1/2}, pi/4); the phases then lie
  on the pi/12 grid.
- The only copies within pi/4 of D' are (6, 0, 6), at f1 = 0, and (6, 4, 14), at f1 = pi/3. Both lie on the boundary
  of D'.
- Each lies in its own certified cube (`inside_locals` is true at the point):
  - the largest CKM boxes contained in the cubes have half-widths 0.0242 for (6, 0, 6) and 0.0172 for (6, 4, 14);
  - Phi(EM)/S0 = 1.0000000000 at both.
- The copies (6, 8, 22) and (6, 8, -2), at f1 = 2 pi/3, lie outside D'. Their cubes are loaded but never used, which
  is harmless. Their transfer from (6, 0, 6) is valid: Btc(6, 8, 22) = Z Btc(6, 0, 6).
- The certificate leaf counts are consistent with complete bisection trees (processed = 2 x leaves - 1 for both).
- That the global maximisers are exactly these copies is a numerical claim. Soundness does not depend on it: a missed
  maximiser would show up as unresolved boxes.

---

## 4. Driver logic in `bb_track.py`: OK for soundness, with a major completeness problem

**What is correct.**
- Certification requires `ub < C.S0.lo`, where S0 is an mpmath-iv enclosure at 200 bits.
- A box is discarded only when `outside_R` is rigorously true: a strict inequality between the ends of enclosures of
  |Bt_0j|^2.
- `inside_locals` requires certified LU pivots and the whole z-enclosure inside the cube.
- Every box is either outside, local, certified, split, or appended to `unresolved` (when hmax < HMIN or the
  evaluation cap is hit). A split covers its parent: the midpoint is computed once and shared. No box is lost.

**Notes.**
- **(a) First launch.** The first launch logged "0 local certificates" (in `fast/bbrun/worker_*.log`, before 19:54),
  because `nash_bb.load_locals` opens relative paths. The current version changes directory and asserts that 4
  certificates are loaded. `bbrun/` was recreated at 19:54. Make sure no output of the first launch is mixed in.
- **(b) No aggregator.** The proof needs all of the following:
  - a `box_<idx>.json` for every one of the 4,224 indices in `work_list()`;
  - every `unresolved` list empty;
  - no crashed worker. An exception, or the `exact_kernel` assert, kills a worker silently. The log simply stops
    without "done".

  Recommended: an aggregation script, and a code hash recorded in each JSON.
- **(c) Certified boxes are not saved.** Only counts and the maximum ub per initial box are kept. Saving the boxes, or
  at least the minimum margin, would allow a-posteriori repairs (such as the fixes in 2.3 and 3.4) without a full
  rerun.
- **(d) Completeness: near-zero cells (not soundness).** Measured with `a4_copy_probe.py`, `a4b_diag_unresolved.py`,
  `a4c_face_zero.py`, `a4d_fallback.py` and `a4e_tube_count.py`.
  - **Probe.** I ran the driver's exact logic on initial box 3074, which has DKZ copy (6, 0, 6) at a corner. After
    16,261 evaluations it had 1,547 certified, 3 inside the cube, 1,510 unresolved (hmax = 7.7e-4 < HMIN) and 12,504
    still queued. A 20,000-evaluation run gave 3,624 unresolved.
  - **Where the unresolved boxes are.** They are not near the copy: CKM distance 0.26-0.52, |z| >= 0.23. There the
    true Phi is only 0.06-0.52 S0.
  - **Cause.** In all 1,510 boxes `okp` is False because p0 has an exact zero.
    - `face = K < 1e-3` (box_bound_track lines 197-199) puts on the face all three kernel entries feeding a cell with
      small q(c). Example: q = 3e-5, with EM entries around 1e-4.
    - p0_c = 0 while q_c > 0 makes the model infeasible, so ub = inf. This is correct behaviour, but splitting cannot
      cure it.
  - **Rates at h = 1e-3** (random points of D' cap R):

    | min_c q(c) | track fails |
    |---|---|
    | < 1e-5 | 100% |
    | 1e-5 to 1e-4 | 79% |
    | 1e-4 to 3e-4 | 17% |
    | >= 3e-4 | 0% |

    These regions make up 0.7% (min q < 1e-4) to 2.3% (min q < 3e-4) of D' cap R.
  - **Number of initial boxes affected.** At least 270 of the 4,224 initial boxes contain sampled points with
    min q < 1e-5; 928 contain points with min q < 1e-4. The first is index 163; the workers were near index 90 at
    20:29.
  - **Index 163.** Worker 1 started this box at 20:48. A probe of it (`a4_probe_163.log`) shows the same stall:
    after 10,273 evaluations, 2,336 were certified and the rest kept failing and splitting down to h = 3e-3, with
    8,178 boxes still queued.
  - **Consequence.** Each such box dives depth-first to HMIN, uses up CAP = 2,000,000 evaluations (about 8 h at
    about 14 ms each) and then dumps its queue into `unresolved`. The JSON files may become very large. So the
    current run cannot prove Theorem N and would take about 5 days or more.
  - **The older bounds handle these boxes.** `nash_core.box_bound` and `kl3mix.box_bound_mix`, with
    `nash_bb.kernel_models` (clean kernel, no face), certify 300 of 300 of these boxes (ub/S0 <= 0.52). The pilot
    (`pilot_bb.py`) used the minimum of all three bounds; `bb_track.py` dropped that fallback.
  - **Fix**, either of:
    - fall back to those bounds when track fails (they then need the same kind of audit as track.py);
    - or repair the face rule: never put on the face all contributors of a cell with q_c(c) > 0; for example, remove
      from the face the largest EM entry of such a cell.

  Whether the neighbourhoods of the copies (the boxes next to the cubes) resolve before HMIN was not determined. The
  probe's budget went into the near-zero region first. The worst certified ub in the probe was 0.9999984 S0, which
  suggests the boxes next to the cube are certified only just.
- **(e) File closing.** `json.dump(st, open(...))` relies on CPython reference counting to close the file before
  `os.replace`. This is fine on CPython.

---

## 5. Independent numerical spot checks: OK

**Per certified box** (`a5_spot.py`; `a5_*.log` and `a5_spot_*.json`):
- **Model.** The model and all internals come from an `inspect` copy of `box_bound_track`, which is bitwise
  identical to the original.
- **Sampling.** 300 uniform points, the 64 corners and 12 face centres.
- **Adversarial search.** L-BFGS-B maximisation of g_K from 4 starts.
- **Phi.** EM (5000 iterations) at the maximiser and 12 random points.
- **Intermediate inequalities**, checked at every sample:
  - q lies in qv;
  - K >= Klow;
  - |E dq - e.t| <= eps;
  - d <= kappa (E dq)^2;
  - w.dq <= Gr.t + (1/2) sup t^T Hw t;
  - Gr.t + (1/2) sup t^T Hq t <= qm;
  - the identity of 1.1.

  The largest positive residuals (<= 2e-18, float cancellation in d) were rechecked at 60 digits; all were <= 0.

| Set | What | Certified boxes checked | ub/S0 max | max (g_K - ub) | max (Phi_EM - ub) | min K entry | tightness max |
|---|---|---|---|---|---|---|---|
| leaf (2 seeds) | exact B&B leaves from random initial boxes | 166 + 300 | 0.99774 | -3.9e-3 | -7.9e-3 | 6.9e-5 | 0.54 |
| rand (2 seeds) | random centres in D' and R, half-widths uniform in [0.03, 0.06] | 33 + 250 | 0.99472 | -1.6e-3 | -4.0e-3 | 1.8e-4 | 0.59 |
| zero | centres with min_c q < 1e-3 (log singularity; kappa) | 200 | 0.99828 | -9.1e-3 | -1.3e-2 | 2.3e-4 | 0.33 |
| top | the 200 largest-ub boxes certified by a mini-B&B of initial boxes 21 and 22 (the live run's worst, 0.9997) | 200 | 0.99969 | -2.7e-2 | -3.4e-2 | 9.9e-4 | 0.22 |
| **all** | | **1,149** | 0.99969 | **-1.6e-3** | **-4.0e-3** | **6.9e-5** | 0.59 |

Column notes:
- "max (g_K - ub)" is taken over all samples and all local maximisers.
- "tightness" is (max found g_K - F)/(ub - F). Values well below 1 mean the bound is conservative; no box came close to
  1.
- The smallest margin S0.lo - ub among the checked boxes is 1.2e-5 (top set).
- The fixes of 2.3 change ub by at most 2.4e-14 on all 950 saved boxes, with no certification flips.

**Adversarial validity** (`a5b_extra.log`): minimising the 3 smallest-Klow entries of K over each of 120 boxes never
went below Klow (minimum gap +6.7e-7). The smallest K found was 6.9e-5.

---

## Overall verdict

**Soundness of the tracking bound.**
- The mathematics is correct (proved): the exact Bregman identity, both kappa inequalities, the Young splitting, the
  per-cell Taylor and mean-value steps, the exact W-shifts and the validity test (K(y) is a stochastic kernel, hence
  Phi <= g_K).
- The implementation is a rigorous enclosure except for one non-outward-rounded step:
  `E = IV(E.lo + eye, E.hi + eye)` (track.py line 246). The exact diag(E) was outside its interval in 2 of 1,368
  tested entries, by up to 3.4e-17. The quantities that enter the bound stayed contained in every test, but this is
  not guaranteed.
- **The domain reduction is correct:** D and conj are exact symmetries (proved, with explicit relabellings), and the
  only copies in D' are (6, 0, 6) and (6, 4, 14), both inside certified cubes.
  - The exception is the float endpoints `DHI`, which leave slivers of width at most 2.4e-16 uncovered.
- The driver never certifies or discards a box unsoundly.
- No numerical test found a counterexample: 1,149 certified boxes, including the tightest ones the run produces, with
  max(g_K - ub) = -1.6e-3 and max(Phi_EM - ub) = -4.0e-3.

**Severity.**
- Both soundness issues are minor and quantitatively negligible: the fixed code moves ub by at most 2.4e-14 and
  changes no certification.
- But the current run is not a rigorous proof as written. Fix (one line each):
  - `E = E + IV(eye)` in track.py;
  - `DHI = V.up(...)` in bb_track.py.

**Completeness (more urgent).**
- As configured, `bb_track.py` cannot finish. Around near-zero cell probabilities (min_c q below about 1e-4, at least
  270 initial boxes, the first at index 163), the face rule leaves a cell with p0 = 0. Track then returns inf at every
  box size, and each affected initial box will burn the 2,000,000-evaluation cap (about 8 h) and end with unresolved
  boxes.
- Since the run is only about 2% done (90 of 4,224 initial boxes at 20:29), I recommend stopping it now and
  restarting with:
  1. the two rigour fixes above (plus optionally `kc` times (1 + 1e-12) and the (1 + 1e-12) vertex test in
     `_sep_bound`);
  2. a repaired face rule, or a fallback to `nash_core.box_bound` / `kl3mix.box_bound_mix`. Those bounds certify
     these boxes, but they would need the same audit as track.py;
  3. an aggregator that checks every `box_<idx>.json` exists and has empty `unresolved`, plus a code hash in each
     JSON;
  4. optionally, saving certified boxes or margins.

**What Theorem N would then rest on.** If the restarted run finishes with no unresolved box, Theorem N follows from:
- this B&B;
- the two local cube certificates, whose bound machinery was not re-audited here;
- the symmetry reduction in section 3.

Lemma R is needed only for the Nash-equilibrium consequence.

---

## Follow-up: numba port

Date: 2026-10-19, 21:10 to 21:50.

**What was audited.**
- New code: `fast/nbjets.py`, `fast/nbtrack.py`, `fast/bb_nb.py`, `fast/check_run.py`.
- The applied fixes: `bb_track.DHI = V.up(...)`, `track.safe_face`, and `E = E + IV(eye)`.
- The later model change: the `freeze` mask in `track.tracking_matrix` and `nbtrack.build_model` (engine v2.1).

**How.** Scripts `nb_f*.py`, run with the repo `.venv` python (numba 0.67), with at most 2 processes at a time. Logs:
`nb_f*.log`, `nb_f*.json`. None of my processes ran `bb_nb.py`, so the restart of the production run did not affect them.

### Verdicts

| Item | Verdict |
|---|---|
| 1. Rounding argument and rounding sites | **OK.** Cosmetic: the `sincos_iv` radius, and inf/NaN robustness |
| 2. Port versus track.py, term by term | **OK** |
| 3. Containment of high-precision values | **OK** |
| 4. Driver `bb_nb.py` and `check_run.py` | **OK**, with a note: score-based splits can stall until CAP |
| 5. `safe_face` (and `freeze`) | **OK** |

### 1. Rounding: OK

**The up/dn argument is correct.**
- If x = fl(r) for a single correctly rounded operation, then |r - x| <= 2^-53 |x| for normal x, and <= 2^-1075 otherwise.
- The computed increment is >= |x| 2^-51, which is exact unless it underflows. When it underflows, the 2^-1073 term
  covers the loss.
- Hence fl(x + incr) >= x + 2^-53 |x| + ...
- One correction to the docstring: when 2^-1073 is below half an ulp of |x| 2^-51, the increment is exactly
  |x| 2^-51, not ">= |x| 2^-51 - 2^-1075 + 2^-1073". The conclusion still holds.
- Checked exactly with `fractions` and mpmath (`nb_f1_rounding.log`): up/dn after one +, -, *, / or sqrt, on
  852,743 cases across all magnitudes including subnormals: 0 failures.
- `up(-inf) = -inf` and `dn(inf) = inf` would be wrong if an infinity came from overflow. No overflow is possible at
  these magnitudes.

**Every rounding site was checked.** Each up/dn covers at most one rounding of exact or already-rigorous inputs, or
has explicit slack:
- sums are sequential `iadd`, outward at each step;
- `up(s + m*h)` with nonnegative terms covers two roundings, since 4u of slack exceeds 2u of error;
- the remainder terms (`rm ** 23`, `up(23 * dn(...))` as a denominator) are covered by the factor 1.01, as in
  nash_iv;
- the z phases are exact: cr is in {+-1, +-1/2}, and sqrt(3)/2 and 1/3 are intervals.

The `OMC`/`OMS` tables match om = exp(i pi n/3), with n = -k(2a + 1) for x = 0 and n = -2ka for x = 1.
`log_point` and `sincos_point` are faithful ports. On 20,000 + 20,000 arguments, both contain the 60-digit values.

**Disjoint-support products.** Every `jmul_d` call has disjoint coordinate supports:
- c12 or s12 (coordinate 0) times c23 or s23 (coordinate 2);
- s13 (1) times cd or sd (3);
- c12 or s12 (0) times c13 (1);
- s23 or c23 (2) times c13 (1);
- se = s13 e^{i d} ({1, 3}) times c12s23-type products ({0, 2});
- the row phases e1 (4) and e2 (5) times V rows ({0, 1, 2, 3}).

The Leibniz collapse is correct for derivative-stored jets. With supports S_f and S_g disjoint, the only nonzero
term of d^alpha(fg) has beta = alpha restricted to S_f, and its multinomial coefficient is the product of
C(alpha_i, alpha_i) or C(alpha_i, 0), which is 1. `disjoint_maps` builds exactly these index pairs.

**Cosmetic 1: the `sincos_iv` radius.**
- `sincos_iv` uses r = 0.5 (hi - lo). This is not a rigorous radius about the rounded midpoint m; nash_iv uses
  `rad()`. The midpoint error is at most 2^-53 |m|.
- That error is covered by the outward rounding inside `sincos_point`: for k = 0 the factor-4 slack of up; for k != 0,
  the width |k| * 4.4e-16 of the pi/2 interval.
- No failure was found in 20,000 B&B-size intervals or in 14,247 adversarial tiny intervals with an inexact midpoint.
- Suggested fix: `r = up(max(up(hi - m), up(m - lo)))`.

**Cosmetic 2: robustness with inf and NaN.**
- numba's `min`/`max` drop a NaN that appears as the second argument, so `imul`, `isqr` and `meet` can lose a NaN.
- A NaN can only arise from 0 * inf. That needs kappa or eta to overflow (m_lo < 5.6e-309, or eps/abar > 1.8e308),
  which is not possible in practice.
- If it did happen, the inf would reach Hq, and `np.linalg.eigvalsh` would raise `LinAlgError`. That crashes the
  worker but produces no bound.
- Suggested guards: return inf when coefq, kc or eta is not finite, and when r0l <= 0 before `log_point`.

### 2. Port versus track.py: OK

**Read term by term.**
- validity: lin, quad, and min(raw, shifted rows of R);
- p0 and Lam with mu intervals;
- r0, F, and w = (log r0 + 1 - sum r0 Lam)/2;
- Gr; Hw0/Hw1 with the double-centring shift and the gersh_proxy choice;
- E = I - diag(r0) Lam, now outward-rounded;
- e; eps = min(raw, shifted) * (1 + 1e-12);
- p over the box from the box gradient, m_lo, and kappa = min(1/m_lo, 1/(2 min(q_lo, m_lo)));
- eta = max(eps/abar, eta_min), coefq, the e_i e_j terms, kc and const;
- qp_bound (Gershgorin, certified isotropic eigenvalue, Lagrangian dual with interval Cholesky).

All of these match `track.py` and `nash_core3.qp_bound`.

**The two deviations are both valid.**
- Validity is tested as K0_e >= move_e. This is exact and slightly stronger.
- `isqr` is used for the diagonal squares g_i^2 (in jsqr) and e_i^2 (in coefq e e^T). The true values are >= 0.

**Numerical identity** (`nb_f5_model.log`; 2,291 boxes: leaves, near-zero boxes, leaves of box 163; v2.1 model).
- I ran numpy's `box_bound_track`, patched in memory with the same two `isqr` tightenings, on the same model.
- It reproduces the numba ub to a relative -2.4e-13 .. +1.6e-11, with identical finiteness and 100% certification
  agreement.
- Against plain numpy, numba is tighter by up to 8.9e-4 S0 and never looser than 3.2e-12 S0. (On the v2 model,
  `nb_f3_*.log`, it is tighter by up to 0.77 S0 on uncertified boxes.)
- The author's 7.9e-3 tighter Hessian lower ends are fully explained by the `isqr` on g_i^2: with `IV.sqr` on that
  diagonal, numpy's box Hessian equals numba's to 3.1e-14 (`nb_f2c_isqr.log`).

### 3. Containment of high-precision values: OK

**Jets** (`nb_f2_shadow.log`; 60 boxes, half B&B leaves and half random boxes with half-widths 0.001-0.06). The
60-digit values were inside the numba intervals for:
- QC value, gradient and Hessian at the centre;
- QB value, gradient and Hessian at 2 random interior points and 2 corners of each box;
- QB third derivatives at an interior point.

For the third derivatives, a first 60-digit run reported +1.9e-18. That is below the reference's own finite-difference
noise (~2.5e-17). A 100-digit recheck (reference error ~1e-25, `nb_f2b_third.log`) gives full containment. The
residual 1.6e-47 sits on the structurally zero entry d_delta d_f1 d_f2 of a b = 2 cell. The box geometry agrees with
nash_core: c is equal, and h is slightly larger (rounded up by more), with [lo, hi] inside c +- h.

**ub against sampled g_K.** Per certified box: 300 uniform samples, 64 corners, 12 face centres; L-BFGS-B maximisation
of g_K from 4 starts; EM Phi (5000 iterations) at 13 points.

| Set | Model | Boxes checked | max (g_K - ub) | max (Phi_EM - ub) | min K |
|---|---|---|---|---|---|
| B&B leaves | v2 | 300 | -4.2e-3 | -8.2e-3 | 5.0e-4 |
| 200 tightest boxes of the first audit | v2 | 200 | -2.7e-2 | -3.4e-2 | 9.9e-4 |
| near-zero (min q < 1e-3) | v2 | 43 | -1.1e-2 | -1.4e-2 | 9.9e-4 |
| 200 tightest leaves of box 163 (ub up to 0.99995 S0) | v2 | 200 | -2.4e-2 | -2.9e-2 | 8.5e-4 |
| certified boxes with frozen cells | v2.1 | 150 | -1.6e-3 | -2.6e-3 | 6.0e-4 |
| boxes where numba is most tighter than numpy | v2.1 | 100 | -1.2e-2 | -1.7e-2 | 1.8e-6 |

No violation was found.

### 4. Driver `bb_nb.py` and `check_run.py`: OK, with a note

**By reading.**
- A box is certified only if ub < S0.lo, discarded only if `outside_R` holds, and counted as local only if
  `inside_locals` holds.
- Every popped box ends up in one of those states, or is split (both children are pushed, sharing the exact
  midpoint), or is appended to `unresolved`, when hmax < HMIN or once evals >= CAP. The queue drains, because at the
  cap no box is evaluated and every remaining one becomes unresolved.

**Coarse/fine flags.** A box with hmax > HFINE is evaluated at most once on its path, at the coarse level. After a
coarse failure its descendants are split along the largest side until hmax <= HFINE, and are then always evaluated.
So no box is skipped forever.

**Instrumented run on box 163** (v2.1, `nb_f4_driver_163.log`; the code copy was taken from the source with
`inspect`):
- 162 s, 29,394 evaluations, 22,118 certified, 1,512 outside, 0 unresolved;
- the 23,630 leaves tile the initial box exactly: their volume sum in rational arithmetic equals the initial volume,
  and every leaf lies inside it;
- 2,000 certified leaves re-evaluated to ub < S0.lo (max 0.99907 S0.lo);
- all outside leaves were re-checked outside R;
- the float volume bookkeeping has a relative error of 6.7e-16.

**Mock runs** (CAP 20,000). All three tile the box exactly and terminate:
- every evaluation fails, with random scores: the run ends at CAP with unresolved boxes;
- coarse evaluations fail and fine ones succeed: the flag logic works, and the run ends at CAP;
- every evaluation fails, and the score always picks the **smallest** side: hmax never falls below 0.049, so only CAP
  ends the run.

**Note: the score-based split can stall.** The real score is h_i(|G_i| + sum_j |H_ij| h_j), which tends to 0 with
h_i. So stalling needs degenerate gradients, but nothing prevents it, and a stall would spend up to 3,000,000
evaluations on one initial box. Suggestion: take the score argmax only among coordinates with h_i >= hmax/4,
otherwise use the largest side.

**Notes on `check_run.py`.**
- It accepts any engine starting with "numba-track-v2", so the v2 boxes from before the restart and the v2.1 boxes are
  mixed. Both are sound; the freeze change affects only the float model. The checker should still report engine
  counts.
- Its 1e-9 volume tolerance cannot detect the loss of a box smaller than about (1e-9 x vol0)^(1/6), roughly h of 2e-3.
  The tiling property itself is verified above.

### 5. `safe_face` and `freeze`: OK

**safe_face removes the p0 = 0 failure.**
- It un-faces the largest feeding entry of any cell whose three feeding entries are all on the face.
- `exact_kernel` then gives that entry >= 2^-40, so P K0 > 0 in every cell.
- Observed: min P K0 = 2.8e-7 over 2,291 models and 3.0e-7 over the 24,320 leaves of box 163.
- On box 163, the old face rule failed in the near-zero region at every box size. Now, with v2.1, the whole box
  completes with 0 unresolved boxes.

**Validity cannot be broken by the face.**
- Face entries are identically 0, because the rows of R on the face are exactly 0 (checked on every model).
- Un-faced entries are checked like any other entry (K0_e >= move_e).
- An unsuitable face can only make a box fail (ub = inf). It can never make it pass.

**The freeze change (v2.1) does not affect soundness.**
- It changes only the weights of the least-squares solve (frozen cells get weight 0 plus rho = 1e6 on their
  p-motion).
- R is still D A, with A masked, rounded to 2^-30 and clipped. So the grid, exact zero b-sums and zero face rows hold
  for any A.
- Checked on 2,291 models (2,216 with frozen cells): all exactness properties hold. Certified boxes with frozen cells
  pass the sampling checks (section 3).

**Recommended insurance.** Soundness of `track_bound_one` relies on these model properties, which the float code
guarantees by construction but never checks. Assert them in `evaluate` before the bound: R b-sums == 0 and
R[face] == 0 exactly, K0 rows == 1 and K0[face] == 0.

### Follow-up: overall

The numba port is a faithful and rigorous implementation of the audited tracking bound:
- its only deviations are valid tightenings;
- it agrees with numpy+isqr to 1.6e-11;
- every jet enclosure tested contains the high-precision values;
- no sample or local maximum of g_K, and no EM Phi, exceeded ub on 993 checked boxes.

The three fixes are in place and work. The driver is sound and loses no box (exact tiling verified).

Remaining suggestions are robustness only:
- the rigorous `sincos_iv` radius;
- finiteness guards (inf/NaN);
- a guard on score-based splits;
- an explicit check of the model's exactness properties;
- engine counts in `check_run.py`.

Theorem N still depends on the run completing with no unresolved box, on the local cube certificates (not
re-audited), and on the symmetry reduction of section 3.

---

## Follow-up 2: local cube certificates

Date: 2026-10-19, 21:55 to 22:15.

**What was audited** (the Oct 13 code and certificates):
- `nash_local_gs2.py`: `star_radius`, `bound_boxes`, and the local B&B;
- `nash_local_gs.py`: `copy_basis`, `slope_z`, `kernel_at`;
- `nash_tmbound.py`: `gs_bt`, `q_tms`, `g_bound`;
- `nash_tm.py`: Taylor-model arithmetic;
- `nash_copies.py`, `nash_copies_exact.py`;
- `nash_bb.py`: `LOCAL_SOURCES`, `load_locals`, `inside_locals`;
- `nash_core3.z_of_box`;
- the certificates `nash_local_gs_6_4_14.json` and `nash_local_gs_6_0_6.json` with their leaves.

**How.** Scripts `lc_*.py`, logs `lc_*.log` and `lc_*.json`, system python, at most 2 processes. The numba run was not
touched.

### Verdicts

| Item | Verdict |
|---|---|
| 1. Star cube | **OK, conditional on two theoretical inputs** (exactness of g(0) = S0 and grad g(0) = 0). The code assumes them; it does not check them. Numerically confirmed to 60 digits. |
| 2. Taylor-model bound `g_bound` | **OK** |
| 3. Chart and coverage | **OK** |
| 4. Spot checks | **OK** |

### 1. Star cube: OK, conditional on exactness

**How `star_radius` uses the Taylor model.**
- It certifies g(s) <= S0 - |s|^2 (lam/2 - A3 |s| - K4 |s|^2) for |s|_inf <= rs.
- It uses only:
  - lam, the certified smallest eigenvalue of -H;
  - A3, the sum of |cubic coefficients|;
  - K4, the quartic remainder.
- It **does not use** the interval enclosures G0 or g (those are only reported, as `G0_contains_S0` and `grad_max`).
- So it silently assumes g(0) = S0 and grad g(0) = 0 **exactly**, for the anchored kernel K(z) = Kc + Mz z.

This is the right use. With interval G0 and g instead, a linear term of size about 1e-15 would make the bound fail for
|z| below about 1e-14. But exactness has to come from mathematics, not from the code.

**Where exactness comes from.** The three ingredients:

- **Exact copy basis: proved.** `nash_copies_exact.py` (re-run, `lc_copies_exact.log`) shows with sympy minimal
  polynomials that the CKM points of (6,0,6), (6,4,14), (6,8,22) and (6,8,-2) are exact images of DKZ Bob basis 0
  under (Z^j, column permutation, conjugation).
- **g(0) = S0.**
  - q(0) is the relabelled DKZ link law, and Kc is the relabelled facet kernel K*_y.
  - mu* is invariant under the joint Alice relabelling, by f(m) = f(1 - m) (first audit, 3.1).
  - Hence g(0) = (1/2) sum q log(q/p) at DKZ, which equals S0 by Prop K3 (theory).
- **grad g(0) = 0.** It splits into two terms:
  - **Kernel term.** It is sum_e Mz_e mu (r_0 + r_1). It vanishes exactly because:
    - KKT holds: r_0(a0, b) + r_1(a1, b) is constant on the support of Kc(. | a0, a1) (exact for the facet kernel);
    - Mz is zero off that support and has exact zero b-sums (checked).
  - **Fixed-kernel term.** It is (1/2) sum_c q_c' log r_c, where log r_c = log RL(level of c). It vanishes by
    stationarity of the level probabilities at DKZ ("Theorem 3", theory).

**60-digit check** (`lc_exact.log`; exact Btc, and Kc from the 200-bit facet weights), for both copies:

| Quantity | (6,4,14) | (6,0,6) |
|---|---|---|
| q(0) minus relabelled link law | 7.8e-62 | 4.4e-62 |
| Kc row sums minus 1 | 3.1e-61 | 3.1e-61 |
| KKT spread | 3.4e-60 | 3.7e-60 |
| g(0) - S0 | 8.3e-61 | 8.6e-61 |
| max \|grad g(0)\|, fixed kernel | 3.4e-37 | 2.9e-37 |
| max \|grad g(0)\|, anchored kernel (Kc + Mz z) | 4.4e-37 | 3.7e-37 |

- The gradient values are exactly the roundoff floor of a central difference at 60 digits with step 1e-25 (about
  1e-61 / 2e-25).
- Hessian eigenvalues at 0, in z units: -0.617, -0.617, -0.447, -0.374, -0.352, -0.352.
- The certificate's lam_s / rho^2 = 0.3449 = 0.98 x 0.352. Consistent.

**Remainder and lam: rigorous.**
- A3 and K4 come from the Taylor-model arithmetic (see item 2).
- lam is certified by interval Cholesky of -H - lam I over the interval Hessian of the quadratic coefficients.
- The final inequality lam/2 - A3 rs - K4 rs^2 > 0 is checked in interval arithmetic. The function is decreasing in
  rs, so it holds on all of (0, rs].
- The anchored kernel is checked >= 0 on the whole rho-cube (`kernel_at`). Off-support entries are exactly 0.
- The quadratic step (1/2) s'Hs <= -(lam/2)|s|_2^2 <= -(lam/2)|s|_inf^2 goes in the right direction.
- Recomputed with the current code (`lc_leaves.log`): r_s = 0.00509131 and 0.00509426, and lam_s, A3, K4 are
  identical to the JSONs.

**Recommendation.** State the exactness of g(0) = S0 and grad g(0) = 0 as an explicit lemma in the certificate, with
references to Prop K3 and Theorem 3. Better still, add a sympy check of KKT and of grad g(0) = 0, as was done for the
copy bases.

### 2. Taylor-model bound `g_bound`: OK

**Taylor-model arithmetic (`nash_tm.py`).**
- The coefficients are interval enclosures of the exact degree-<=3 Taylor coefficients at s = 0, because every
  operation acts on Taylor polynomials.
- The remainder K bounds |F - P_exact| <= K |s|_inf^4 on the unit box:
  - products: the dropped degree >= 4 terms are bounded by B_d1 B_d2, and the cross terms by K_P |Q| + K_Q |P| + K_P K_Q;
  - univariate functions: Lagrange remainder f''''(xi) d^4/24, with |d| <= B |s|_inf and xi in u0 + [-B, B].
- The fourth-derivative sups are correct and evaluated at `rng.lo`:
  - inv_sqrt: (105/16) u^(-9/2);
  - log: 6 u^(-4).
- Float powers (`B**4`, `lo**4`, `sqrt(lo) lo**4`) are covered by the explicit (1 + 1e-9) factors.
- Sums use `V.isum`; constants are IVs.

**`gs_bt` and `q_tms`.**
- `gs_bt` is Gram-Schmidt of I + Z in Taylor models: q0 = v0/|v0|, q1 = (v1 - <q0,v1> q0)/|.|, q2 = conj(q0 x q1).
  Then Bt = Btc Q.
- `q_tms` builds q = |sum om Bt|^2/9 with the interval om.

**`g_bound` itself.**
- Good cells (q_lo >= 1e-4, p_lo > 0) contribute the Taylor model of (1/2) q (log q - log p).
- Bad cells contribute the vertex maximum of the jointly convex q log(q/p), or +inf if p_lo <= 0.
- ub = G0.hi + QP bound + sum of |cubic coefficients| + K + bad sum. All terms are rigorous.

**Kernel validity.**
- Anchored kernel: an interval check of Kc + Mz c + Mz[-h, h] >= 0 on the support. Off the support the kernel is
  exactly 0.
- Per-box kernels: `clean_kernel` (exact rows) and `clean_slope` (dyadic slopes with exact zero b-sums; blocks scaled or
  zeroed until K - sum |M| h >= 0, checked with an upper-rounded slack).
- p > 0 is required in both paths.

**Numerical check** (`lc_spot.log`): on 35 boxes of the cube (including the star rho-cube itself), with the anchored
kernel, the 60-digit g(c + h s) lies inside the Taylor-model enclosure (polynomial with interval coefficients
+- K |s|^4) at every sampled s. The margin is >= 1.2e-9.

### 3. Chart and coverage: OK

**The chart is correct and has an explicit inverse.**
- With U = Btc^H Bt = L U' (LU without pivoting, L = I + Z unit lower triangular):
  - L's first column is proportional to U e0;
  - L's second column lies in span(U e0, U e1);
  - so Gram-Schmidt of the columns of L gives Q(z) = U diag(phases).
- Hence Btc Q(z) = Bt diag(phases), which has the same q.
- The coordinates (Re, Im of z10, z20, z21) agree in `gs_jets`, `gs_bt` and `z_of_box`.
- Checked on 300 CKM boxes accepted by `inside_locals` per copy, with 5 points each: Btc Q(z(x)) equals Bt(x) up to
  column phases to 5.6e-16.

**Leaves tile the cube exactly** (`lc_leaves.log`).
- For both certificates, the saved leaves tile [-0.1, 0.1]^6 exactly: the rational volume sum equals 0.2^6, and every
  leaf lies inside.
- The 64 star leaves lie inside |z|_inf <= r_s.
- processed = 2 x leaves - 1, which is consistent with a complete bisection tree.
- Re-certified with the current code: 3,000 random non-star leaves and the 704 leaves next to the star cube, per copy.
  All have ub < S0.lo (max 0.999982 and 0.999959 of S0.lo).
- `copy_basis` recomputes bitwise-identical Btc enclosures.

**`inside_locals` is rigorous.**
- `z_of_box` computes the LU of Btc^H Bt over the CKM box in interval arithmetic: l10 = W10/W00, l20 = W20/W00,
  l21 = (W21 - l20 W01)/(W11 - l10 W01).
- Pivots are required to satisfy |.|^2_lo > 0.
- A box is accepted only if the whole z-enclosure lies in [-R, R]^6.
- Sampled z(x) always lay inside the enclosure.

**Copies.** The only DKZ copies in the closure of D' are (6,0,6) at f1 = 0 and (6,4,14) at f1 = pi/3 (first audit,
3.5). Each has its own certificate.
- The largest CKM boxes contained in the cubes have half-widths 0.0242 and 0.0172.
- (6,8,22) and (6,8,-2) are exact Z / 2 pi translates of (6,0,6): Btc(6,8,22) = Z Btc(6,0,6), with Z a symmetry. They
  lie outside D' and are unused there. The transfer is valid, and sympy shows all four are exact DKZ images.

### 4. Spot checks: OK

Method (`lc_spot.log`), around each copy:
- 40 random directions at each |z|_inf in {1e-4, 3e-4, 1e-3, 3e-3, r_s, 0.01, 0.03, 0.06, 0.1};
- Bt = Btc Q(z);
- Phi from EM: 20,000 iterations warm-started from the exact kernel, plus 5,000 from uniform. EM values are upper
  bounds of Phi.

Results:
- S0 - max Phi > 0 at every radius:
  - (6,4,14): 2.9e-9 at r = 1e-4, 6.9e-6 at r_s, 2.5e-3 at 0.1;
  - (6,0,6): 2.3e-9, 6.4e-6, 2.4e-3.
- This is consistent with the quadratic decay (lam/2) r^2 (lower prediction 1.8e-9, 4.6e-6, 1.8e-3).
- A 30-digit EM at r = 1e-4 and 1e-3 (2 points each) gives S0 - Phi_EM = 4.6e-9 to 8.4e-9 and 3.2e-7 to 6.6e-7.

### Notes

- **Provenance.** `nash_tmbound.py` is dated 21:15 on Oct 13, during the (6,4,14) run, and the JSONs carry no code
  hash. This is mitigated by the identical recomputed star radii and Btc and by the 3,704 leaves re-certified per copy
  with the current code. A full re-run (about 70 min per copy) would remove the concern.
- **Same primitives as before.** The local bound uses the same `nash_iv` primitives audited in item 2 of the first
  audit. I found no non-outward-rounded step in `nash_tm` or `nash_tmbound`.

### Follow-up 2: overall

The local cube certificates are sound and cover both DKZ copies in D'. The one caveat is that the star cube relies on
the exact identities g(0) = S0 and grad g(0) = 0 for the anchored kernel. These follow from:
- the sympy-proved exact copy bases;
- Prop K3 (facet kernel and KKT);
- Theorem 3 (stationary level probabilities).

The code does not check them, but they hold to 60 digits (1e-60 for the value, the 4e-37 roundoff floor for the
gradient).

With the numba run finishing with no unresolved box, and with section 3 (symmetries), Theorem N then rests on audited
code plus those two theoretical inputs and Lemma R (for the Nash consequence).
