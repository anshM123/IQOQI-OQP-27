# Q_rig/RIGIDITY_ALLD.md -- rigidity of DKZ for CGLMP_d on maximally entangled states, for EVERY d

Labels: PROVED = complete argument written here (or a precise citation of a written proof); DEP = depends on a result of the
programme that is proved elsewhere but whose verification status is stated in section 0.3; NUMERICAL = sanity check only
(scripts in this folder, not part of the proof); GAP = missing step.

## 0. Statement, dependencies, outline

### 0.1 Theorem R (rigidity, all d)
Let d >= 2 and D >= 1.  Let {P^x_a}, {Q^y_b} (x, y in {1,2}, a, b in Z_d) be projective measurements on C^D (x) C^D and let
Phi_D = D^{-1/2} sum_i |ii>.  If the CGLMP value of this strategy equals I_ME(d) = (4/(d(d-1))) sum\_{j=1}^{d-1} (d-j) sec(pi j/(2d)), then
d | D and there is a unitary u : C^D -> C^d (x) C^{D/d} such that the local unitary u (x) conj(u) maps the strategy to
DKZ (x) 1\_{C^{D/d}} (and Phi_D to Phi_d (x) Phi\_{D/d}).  The unitary u is unique up to u -> (1_d (x) u') u.
Consequently, for d not dividing D the maximum of I_d over projective measurements on Phi_D is STRICTLY below I_ME(d).

(For d = 2 this is the rigidity of CHSH on Phi_D; the argument below does not treat d = 2 separately.)

### 0.2 Proof outline (the equality case of the optimality chain)
  strategy R --(twirl + Stone-von Neumann)--> reduced family V_0..V\_{d-1} in U(M), V_k^4 = 1 --(spectral projections)-->
  27B configuration {Q_x}\_{x in Z_4d}  --(CONE_d certificate: v = sum lambda_k u^{ell_k} (+ trivial directions))-->
  cell inequalities <u^ell, delta> <= 0, each an average of continuum inequalities Q^ell <= N^2 Phi_c (Q-T1 for step fields)
  --(Q-T1 chain: bathtub, (\*) pointwise, harmonicity)-->  strip inequality (\*) for the pair (B~(t), g(t)) at every t.
Equality I_d = I_ME(d) forces equality at every link of this chain:
  Step 1: <v, delta> = 0  ==>  <u^ell, delta> = 0 for some ell with ALL cells positive  ==>  Q^ell = N^2 Phi_c(1/4,1/4).
  Step 2: equality in Q-T1  ==>  equality in (\*) at lambda\* for a.e. t  ==>  [B~(t), g(t)] = 0 a.e. (Q_2bmv Theorem 2(d)).
  Step 3: (residue lemma) [B~, g] = 0 a.e. for a step field whose cells all have positive length  ==>  all Q_x commute.
  Step 4: the CONE_d certificates contain a cell vector with all cells positive (every d).
  Step 5: all Q_x commute  <=>  the reduced family V commutes  ==>  (Theorem B, Corollary C of paper-classical-all-d)
          R = DKZ (x) 1 up to u (x) conj(u).
Step 3 replaces the "analytic continuation and peeling" of the suggested route by a one-line residue argument (section 4).

### 0.3 Dependencies and their status (as of 2026-10-02)
 (D1) Strip inequality (\*) for every M, with its equality case "equality at one lambda iff [B, g] = 0":
      Q_2bmv/PROOF.md Theorem 2 (with Theorem 1 = 2BMV).  Status: RE-VERIFIED CORRECT (internal check, Q_2bmv_check/REFEREE.md), including Theorem 2(d) and Lemma 1(f).
 (D2) Q-T1 for projection-valued step fields (continuum quantum = classical):  Q_quantum/LOG.md s.4 and s.8 (technical points).
      PROVED modulo (D1).  Re-derived below with the equality analysis (section 3).
 (D3) Reduction to the clock model and the Q-picture: paper-classical-all-d Theorem 2.3 ("reduction to the clock model", proof in
      its appendix), eq. (projform) of its s.6, SHARED_LEMMAS E2-R2, QD-L7, QD2 section 4.  PROVED (elementary identities; the
      two needed counting identities are re-proved in 1.4 below; all re-checked numerically, section 7).
 (D4) Cell-embedding inequalities and their window/rotation structure: QD2/LOG.md section 4 (QD2-L1, QD2-L2, QD2-R1).  PROVED mod (D2).
 (D5) CONE_d for every d (QD2-T3): LP certificates d <= 200 (QD2/certs), Gaussian-modulated Dirichlet certificates 201 <= d <= 2000
      (QD2/verify_gauss.py + Lemma B fixed point, verify_fixedpoint.py), interval Taylor-model proof d >= 2001 (QD2/CONE_ALLD_PROOF.md).
      Status: computer-assisted.  The Lemma B fixed-point sweep (QD2/logs/fp_d\*.json) covered d = 201..1766 contiguously (1567 files,
      all "ok") at the last check of this file; 233 values in 1767..2000 were still running.  Rigidity for those d inherits exactly
      that status.
 (D6) Theorem B and Corollary C of publish/CGLMP/paper-classical-all-d/main.tex (commutative sector; equality only at one-step
      configurations; equal-link strategies attaining I_ME are DKZ (x) 1).  PROVED (classical all-d theorem, E2-T2).
Nothing else is used.  In particular the SOS certificates of d <= 20 are NOT used; the published rigidity for d = 3..20 is an
independent check of Theorem R for those d.

## 1. Setting: the forward chain (what is used, in the exact form used)

Throughout d >= 2, N = 4d, z = e^{2 pi i/N}, w = z^4, kappa(u) = cot(pi u/N) for u in Z_N \ {0}, kappa(0) = 0, tau = Tr/M.

1.1 Strategies [PROVED, paper s.2].  A projective strategy on Phi_D is encoded by the chain unitaries R_1 = U_2, R_2 = (U'\_2)^T,
R_3 = U_1, R_4 = (U'\_1)^T (U_x = sum_a w^a P^x_a, U'\_y = sum_b w^b Q^y_b, transpose in the Schmidt basis of Phi_D), R_i^d = 1, and
I_d = 4 - 2S/(d-1), S = 2(d-1) + sum_n c_n Lambda_n(R) (paper Lemma 2.1 and eq. (Strace)).  Conversely every such quadruple is a
strategy.  A simultaneous conjugation R_i -> u R_i u^\* is the local unitary u (x) conj(u) on the strategy, and fixes Phi_D.

1.2 Reduction [PROVED, paper Theorem 2.3(2) and its appendix].  Let Rt = (+)\_{r in Z\_{4d}} rho^r(R) (twirl, rho(R) = (R_2,R_3,R_4,wR_1)).
Then I_d(Rt) = I_d(R), R is the direct summand r = 0 of Rt, and in a suitable orthonormal basis Rt = R^V, the covariant strategy
of a family V_0..V\_{d-1} in U(M), V_k^4 = 1, M = 4D:  W = sum_k |k><k| (x) z^k V_k, R^V_1 = X (x) 1_M, R^V\_{i+1} = W R^V_i W^\*.
Moreover I_d(R) = 4F(V)/(d(d-1)) with F(V) = sum\_{j<k} Re[h\_{k-j} tr(V_j V_k^\*)], h_m = sec(pi m/2d) - i csc(pi m/2d), and
I_ME(d) = 4F_DKZ/(d(d-1)), F_DKZ = sum_m (d-m) sec(pi m/2d).  So   I_d(R) = I_ME(d)  <=>  F(V) = F_DKZ.

1.3 Q-picture [PROVED, paper eq. (projform); E2-R2].  For x in Z_N write uniquely x = k - d a (0 <= k <= d-1, a in Z_4) and let Q_x be
the spectral projection of E_k := V_k^\* for the eigenvalue i^a.  For each site k, {Q\_{k-da}}\_{a in Z_4} is a PVM and
      E_k = sum\_{a in Z_4} i^a Q\_{k-da}.                                                                                  (1.0)
Put A_x := Q_x, B_x := Q\_{x+d}.  Then A_x B_x = 0 (two outcomes of one PVM), sum_x A_x = sum_x B_x = d 1, and
      F(V) = (1/2) <A,B>\_tau - d/2,     <A,B>\_tau := sum\_{x,y in Z_N} kappa(x-y) tau(A_x B_y);   F_DKZ = (1/2) Phi_N - d/2,
Phi_N := sum\_{x in [0,d), y in [-d,0)} kappa(x-y) (V = 1).  Every rotation (rot_c Q)\_x := Q\_{x-c} is again a family of projections
in which each residue class mod d is a 4-outcome PVM ("27B configuration"); that is all QD2-L1 uses.

1.4 Linear form [PROVED; QD-L7, QD2 s.4(i); re-proved here].  Put C(n) := sum\_{u in Z_N} tau(Q_u Q\_{u+n}) (so C(-n) = C(n)),
T(m) := sum_y tau(A\_{y+m} B_y) = C(m-d), N(m) := T(m) - T(-m) = C(m-d) - C(m+d), delta_m := N(m) - m (m = 1..d-1).
 (a) N(d) = C(0) - C(2d) = d - 0 = d (Q_u Q\_{u+2d} = 0: same site, labels a, a-2) and N(2d-m) = C(d-m) - C(3d-m) = C(m-d) - C(m+d) = N(m).
 (b) Since kappa is odd, kappa(2d) = 0 and by (a):  <A,B>\_tau = sum\_{m=1}^{2d-1} kappa(m) N(m) = d kappa(d) + sum\_{m=1}^{d-1} v_m N(m),
     v_m = kappa(m) + kappa(2d-m) = 2 csc(pi m/2d); the window (V = 1) has N(m) = m.  Hence
        F(V) - F_DKZ = (1/2) <v, delta>,     <v, delta> := sum\_{m=1}^{d-1} v_m delta_m.                                     (1.1)
 (c) Pair form.  For sites j < k let pi_jk(t) := sum\_{b in Z_4} tau(Q\_{j-db} Q\_{k-d(b+t)}) (a probability vector on Z_4).  Splitting
     u = k - da according to whether k + m < d or k + m >= d (m in [1,d-1]) gives
        N(m) = sum\_{k-j = m} [pi_jk(1) - pi_jk(3)] + sum\_{k-j = d-m} [pi_jk(0) - pi_jk(2)],
     hence for 1 <= s <= d-1:  N(s) + N(d-s) - d = sum over the d pairs at distance s or d-s (each pair counted once, twice if s = d/2)
     of [pi(0) + pi(1) - pi(2) - pi(3) - 1] <= 0.  So with t_s := e_s + e\_{d-s}:   <t_s, delta> <= 0  for every configuration.  (1.2)
     (This is QD2-R2 "N(s) + N(d-s) <= d"; it is elementary and needs no (\*).)

1.5 Cell embeddings [PROVED mod (D1),(D2); QD2-L1, QD2-L2, QD2 s.4(ii)-(iii)].  A cell vector is ell in Delta_d := {ell in R^d :
ell_r >= 0, sum_r ell_r = d}; extend ell_x := ell\_{x mod d} (x in Z_N), L_0 = 0, L\_{x+1} = L_x + ell_x (so L_N = N), cells
I_x = [L_x, L\_{x+1}) on T_N = R/NZ, step fields At(xi) = A_x, Bt(xi) = B_x (xi in I_x), and
      Q^ell(Q) := int int tau(At(xi) Bt(eta)) cot(pi(xi - eta)/N) dxi deta = sum\_{x,y} K^ell(x,y) tau(A_x B_y),
K^ell(x,y) = int\_{I_x} int\_{I_y} cot(pi(xi-eta)/N).  (i) For every ell in Delta_d and every 27B configuration:
      Q^ell(Q) <= N^2 Phi_c(1/4,1/4)        (Q-T1 for the step field; section 3),                                         (1.3)
(ii) the IDENTITY (no inequality involved; it uses only 1.4(a) and the window values)
      (1/d) sum\_{c=0}^{d-1} [ Q^ell(rot_c Q) - N^2 Phi_c(1/4,1/4) ] = <u^ell, delta>,                                      (1.4)
with u^ell_m = Delta^2_m (1/d) sum_r Ghat(S_r(m)) (window-sum form).  Consequently <u^ell, delta> <= 0 for every ell in Delta_d.

1.6 CONE_d [DEP (D5); QD2-T1, QD2-T2, QD2-T3, CONE_PROOF.md Lemma R1].  For every d >= 2 there are a finite positive Borel measure
mu on Delta_d and w_s >= 0 with
      v = int\_{Delta_d} u^ell mu(d ell) + sum\_{s=1}^{floor(d/2)} w_s t_s,                                                   (1.5)
namely: d <= 200: mu = sum_k lambda_k delta\_{ell^(k)}, lambda_k > 0, ell^(k) = n^(k)/16, w = 0;  d >= 201: mu = the law of the
Gaussian-modulated Dirichlet process Pi\_{Phi#} (a probability measure), w = Delta^2 W (symmetric, >= 0).  (ell -> u^ell is bounded
and continuous on the compact Delta_d, so the integral is an ordinary vector-valued integral.)

## 2. Step 1: equality forces a tight cell inequality with all cells positive   [PROVED, given (D5) and section 5]

Let R attain I_ME(d).  By 1.2 and (1.1), <v, delta> = 0.  Insert (1.5):
      0 = <v, delta> = int <u^ell, delta> mu(d ell) + sum_s w_s <t_s, delta>.
Every <u^ell, delta> is <= 0 (1.5) and every <t_s, delta> is <= 0 (1.2); hence <u^ell, delta> = 0 for mu-almost every ell.  By
section 5, mu(Delta_d^+) > 0 where Delta_d^+ := {ell : ell_r > 0 for all r} (for d <= 200 every atom lies in Delta_d^+, for d >= 201
mu(Delta_d^+) = 1).  Pick ell\* in Delta_d^+ with <u^{ell\*}, delta> = 0.  In (1.4) all d summands are <= 0 by (1.3) and their mean is 0,
so every summand vanishes; in particular (c = 0)
      Q^{ell\*}(Q) = N^2 Phi_c(1/4, 1/4).                                                                                    (2.1)
(Remark: the uniform cell vector ell = (1,..,1) does NOT suffice here: u^1 = v + e is not proportional to v (QD2-L1), so the
equality <v, delta> = 0 does not by itself make the uniform cell inequality tight.  The cone representation is what transports
the equality to an individual continuum inequality.)

## 3. Step 2: tight cell inequality ==> [Bt, g] = 0 almost everywhere   [PROVED modulo (D1)]

This re-proves (1.3) (Q-T1 for one cell-embedded step field) with every inequality displayed, so that its equality case can be read
off.  Fix ell in Delta_d^+ (all cells positive) and a 27B configuration Q on C^M.

3.1 Normalisation.  Map T_N to T = R/2piZ by theta = 2 pi xi/N, dm = dtheta/2pi.  Cell endpoints t_j := 2 pi L_j/N (j in Z_N),
pairwise distinct mod 2pi because every cell has positive length (for (1.3) alone zero-length cells are harmless: they carry no
field, and 3.1-3.6 hold verbatim with the remaining distinct endpoints, so (1.3) holds for every ell in Delta_d); open arcs J_x := (t_x, t\_{x+1}) (nonempty, disjoint, covering T up
to the finite set {t_j}).  Step fields B(theta) := B_x, A(theta) := A_x on J_x.  Then B(theta) is a projection, 0 <= A <= 1 - B
(A_x B_x = 0), and the OPERATOR constraints hold:
      int B dm = (1/N) sum_x ell_x B_x = (1/N) sum_r ell_r sum\_{j in Z_4} Q\_{r+d+jd} = (d/N) 1 = (1/4) 1,   likewise int A dm = (1/4) 1.
3.2 Explicit Herglotz function.  For |z| < 1 put
      H(z) := int ((e^{i phi} + z)/(e^{i phi} - z)) B(phi) dm(phi) = (1/4) 1 + (i/pi) sum\_{j in Z_N} (B_j - B\_{j-1}) Log(1 - z e^{-i t_j}).
(Proof: (1/2pi) int_a^b (e^{i phi}+z)/(e^{i phi}-z) dphi = (b-a)/2pi + (1/(pi i))[Log(1 - z e^{-ib}) - Log(1 - z e^{-ia})], since
(e^{i phi}+z)/(e^{i phi}-z) = 1 + (2/i) d/dphi Log(1 - z e^{-i phi}) and Re(1 - z e^{-i phi}) > 0; sum over the cells and regroup by
endpoints.)  H is holomorphic on D, H(0) = (1/4) 1, Re H(z) = int P_z B dm (P_z > 0 the Poisson kernel), and H extends continuously
to the closed disc minus {e^{i t_j}}, with boundary values, for theta not in {t_j},
      H(e^{i theta}) = B(theta) + i g(theta),    g(theta) = (1/pi) sum\_{j in Z_N} (B_j - B\_{j-1}) log|sin((theta - t_j)/2)|      (3.1)
(|1 - e^{iu}| = 2|sin(u/2)| and sum_j (B_j - B\_{j-1}) = 0).  g is the conjugate function of B (on J_x it is the principal value
int p.v. cot((theta - phi)/2) B(phi) dm(phi)), real-analytic on each open arc J_x.  Since
      int\_{J_x} int\_{J_y} cot((theta-phi)/2) dm dm = K^ell(x,y)/N^2   and   tau(A_x B_x) = 0,
we have  Q^ell(Q) = N^2 int tau(A g) dm  (all integrals absolutely convergent: only logarithmic singularities).
Domination: |1 - r e^{iu}|^2 = (1-r)^2 + 4r sin^2(u/2) >= 2 sin^2(u/2) for r >= 1/2, so for 1/2 <= r < 1
      ||H(r e^{i theta})|| <= C_0 + (2/pi) sum_j |log|sin((theta - t_j)/2)||  =: Hmaj(theta),  Hmaj in L^p(dm) for every p < infinity.  (3.2)
3.3 Spectrum in the open strip S = {0 < Re w < 1}.  For a unit vector v and |z| < 1, <v, Re H(z) v> = int P_z(phi) <v, B(phi) v> dm(phi) =
sum_x omega_x(z) <v, B_x v> with harmonic measures omega_x(z) > 0, sum_x omega_x = 1.  It is 0 only if B_x v = 0 for all x, impossible
since sum_x ell_x <v, B_x v> = d |v|^2 > 0 (operator constraint); it is 1 only if B_x v = v for all x, impossible since then
sum_x ell_x <v, B_x v> = N |v|^2 != d |v|^2.  So the numerical range of Re H(z) lies in (0,1) and spec H(z) is contained in S.
3.4 The harmonic function.  For lam in R let phi_lam(w) := (i/pi^2) Li2(exp(-i pi w - pi lam)), holomorphic on S (arg exp(-i pi w) =
-pi Re w lies in (-pi, 0), off the cut [1, inf) of Li2), with Re phi_lam = h_lam (the strip function of (\*): harmonic on S, continuous
on the closed strip, boundary values (y - lam)\_+ on Re w = 0 and 0 on Re w = 1; Q_2bmv/PROOF.md Lemma 6).  By the holomorphic
functional calculus (Riesz-Dunford integral over a contour in S around spec H(z), locally uniform in z),
      u_lam(z) := Re Tr phi_lam(H(z)) = sum\_{nu in spec H(z)} h_lam(nu)        (algebraic multiplicities)
is harmonic on D, and u_lam(0) = M h_lam(1/4).
3.5 Boundary passage (mean value identity).  0 <= h_lam(x + iy) <= (y - lam)\_+ + C_1 <= |y| + |lam| + C_1 on the closed strip (Poisson
representation h_lam(x+iy) = int (s - lam)\_+ K_x(y - s) ds with K_x >= 0 of mass 1 - x and first absolute moment bounded uniformly in x),
and every eigenvalue nu of H(z) has |Im nu| <= ||H(z)||.  Hence 0 <= u_lam(r e^{i theta}) <= M (Hmaj(theta) + |lam| + C_1) for r >= 1/2.
For theta not in {t_j}, H(r e^{i theta}) -> B(theta) + i g(theta) (continuity of H up to the boundary, 3.2), eigenvalues move continuously and h_lam is continuous on the
closed strip, so u_lam(r e^{i theta}) -> u\*\_lam(theta) := sum\_{nu in spec(B(theta) + i g(theta))} h_lam(nu).  By the mean value
property on |z| = r and dominated convergence,
      int u\*\_lam dm = u_lam(0) = M h_lam(1/4).                                                                           (3.3)
3.6 The chain.  For theta not in {t_j}, with P(theta) := 1 - B(theta):
      tau(A(g - lam))  <=  tau((P(g - lam)P)\_+)  <=  (1/M) u\*\_lam(theta).                                                (3.4)
First: A = PAP, and for X := P(g - lam)P: tau(AX) <= tau(A X\_+) <= tau(P X\_+) = tau(X\_+) (0 <= A <= P, X\_+ >= 0, P X\_+ = X\_+).
Second: the strip inequality (\*) (D1) for the pair (B(theta), g(theta)) on C^M (Tr[(P(g-lam)P)\_+] = sum of the positive parts of the
eigenvalues of the compression to ran P, the same number as Tr of the positive part of the operator P(g-lam)P on C^M).
Integrating (3.4) with int tau(A) dm = 1/4 and (3.3):
      int tau(A g) dm = lam/4 + int tau(A(g - lam)) dm  <=  lam/4 + int tau((P(g-lam)P)\_+) dm  <=  lam/4 + h_lam(1/4).       (3.5)
By the Legendre identity (Q-L12; inf_y [h_0(x + iy) - p y] = Phi_c(x,p)) the right side is minimised at
      lam\* = (1/pi) log( sin(pi(alpha+beta)) / sin(pi alpha) ) = log(2)/(2 pi)   (alpha = beta = 1/4),   with value Phi_c(1/4,1/4).
So (3.5) at lam\* is (1.3).
3.7 Equality.  Under (2.1), int tau(A g) dm = Q^{ell\*}/N^2 = Phi_c(1/4,1/4) = lam\*/4 + h\_{lam\*}(1/4), so both inequalities of (3.5) at
lam = lam\* are equalities.  The second one says  int [ (1/M) u\*\_{lam\*} - tau((P(g - lam\*)P)\_+) ] dm = 0  with an integrand that is
>= 0 at every theta not in {t_j} by (3.4).  Hence for almost every theta
      sum\_{nu in spec(B(theta) + i g(theta))} h\_{lam\*}(nu) = Tr[(P(theta)(g(theta) - lam\*)P(theta))\_+],
i.e. (\*) holds with EQUALITY at lam = lam\* for the pair (B(theta), g(theta)).  By (D1) (Q_2bmv/PROOF.md Theorem 2(d): the defect equals
V(lam) = int int K\_{1-tau}(s - lam) F_2bmv(s,tau) ds dtau with K > 0 and F_2bmv >= 0 continuous, so V(lam) = 0 at ONE lam forces
F_2bmv = 0, D = 0, ||BgP||\_F^2 = 0):
      [B(theta), g(theta)] = 0      for almost every theta in T.                                                         (3.6)
(The first equality also gives the bathtub condition tau(A(g - lam\*)) = tau((P(g - lam\*)P)\_+) a.e.; it is not needed.)
NUMERICAL (c03_chain.py, d = 4, M = 2, 3): Q^ell/N^2 = int tau(A g) dm to 1e-11; mean value identity (3.3) to 1e-7 for four lam;
Phi_c - Q^ell/N^2 = S_star + S_bath (the two integrated slacks of (3.5) at lam\*) to 1e-8..1e-12; pointwise (\*)-defect >= -2e-15;
commuting one-step mixture: both slacks 0 (2e-16); non-commuting rotations by angle t: slacks ~ 0.0057 t^2 and 0.0041 t^2.

## 4. Step 3: [Bt, g] = 0 a.e. on a step field with all cells positive ==> all Q_x commute   [PROVED, elementary]

LEMMA 4.1 (residue lemma).  Let t_0, ..., t\_{n-1} in R be pairwise distinct modulo 2pi and J_0, ..., J\_{n-1} in M_M(C).  If
      sum_j J_j cot((theta - t_j)/2) = 0   for all theta in a nonempty open interval I contained in R \ U_j (t_j + 2 pi Z),
then J_0 = ... = J\_{n-1} = 0.
Proof.  Entrywise, R(z) := sum_j J_j cot((z - t_j)/2) is holomorphic on the connected open set Omega := C \ U_j (t_j + 2 pi Z) and
vanishes on I, a subset of Omega with accumulation points; by the identity theorem R = 0 on Omega.  Near z = t_j the terms with
j' != j are holomorphic (t\_{j'} != t_j mod 2pi) and cot((z - t_j)/2) = 2/(z - t_j) + O(z - t_j), so the residue of R at t_j is 2 J_j;
it must vanish.  []

PROPOSITION 4.2.  In the setting of section 3 (ell in Delta_d^+), (3.6) implies [Q_x, Q_y] = 0 for all x, y in Z_N.
Proof.  Fix x in Z_N.  On the nonempty open arc J_x, B(theta) = B_x and, by (3.1), g is real-analytic there, so theta -> [B_x, g(theta)]
is continuous on J_x and vanishes almost everywhere on J_x by (3.6); hence it vanishes identically on J_x, and so does its derivative:
      0 = d/dtheta [B_x, g(theta)] = (1/2pi) sum\_{j in Z_N} [B_x, B_j - B\_{j-1}] cot((theta - t_j)/2)      (theta in J_x).
The t_j (j in Z_N) are pairwise distinct mod 2pi because all cells have positive length.  Lemma 4.1 gives [B_x, B_j] = [B_x, B\_{j-1}] for
every j in Z_N; so j -> [B_x, B_j] is constant on Z_N, equal to [B_x, B_x] = 0.  As x runs over Z_N, B_x = Q\_{x+d} runs over all Q's. []

REMARK 4.3 (singular parts at shared endpoints; why positive cells are needed).  On J_x,
      [B_x, g(theta)] = (1/pi) sum_j c_j log|sin((theta - t_j)/2)|,   c_j := [B_x, B_j] - [B_x, B\_{j-1}]:
the logarithmic singularity at the endpoint t_j shared by the cells j-1 and j carries the JUMP of y -> [B_x, B_y] across t_j; at the
two endpoints of J_x itself these are c_x = [B\_{x-1}, B_x] and c\_{x+1} = [B_x, B\_{x+1}] (commutators with the neighbours).  The
suggested route (continue [B_x, g] analytically from J_x around t\_{x+1} into J\_{x+1}: log|sin| picks up +- i pi, so the continuation
is the old function plus i pi c\_{x+1}; compare with the expression valid on J\_{x+1}; peel cell by cell) proves the same thing; the
residue lemma treats all endpoints at once.  If a run of consecutive cells j, ..., j+k-1 has length 0, then t_j = ... = t\_{j+k} and only
c_j + ... + c\_{j+k} = [B_x, B\_{j+k}] - [B_x, B\_{j-1}] is visible: the projections of zero-length cells do not enter the field at all.
Concretely, if ell_r = 0 for one residue r, then K^ell(x,y) = 0 whenever x = r or y = r mod d, so Q^ell does not see the PVM of site r.
Every cell inequality is tight on every commuting optimal configuration (a direct sum of windows: windows embed as adjacent arcs), e.g.
on V_k = diag(1, i^{-[k >= r0]}) (M = 2); replacing the site-r PVM there by one that does not commute with the others keeps Q^ell =
N^2 Phi_c, although the new configuration is non-commuting (hence, by Theorem R, not optimal; c04 checks F < F_DKZ).  So Step 3
genuinely needs a cell vector with ALL cells positive, which is what section 5 checks.

## 5. Step 4: every CONE_d certificate charges cell vectors with ALL cells positive   [PROVED / CHECKED, all d]

What Steps 1-3 need: mu(Delta_d^+) > 0 in (1.5), Delta_d^+ = {ell : ell_r > 0 for every r}.  (The weaker condition "every residue r
has ell\_{k,r} > 0 for some k" of the suggested route would NOT suffice by itself: a tight cell vector with zero cells only yields
commutation among the residues of its support (Remark 4.3: [B_x, B_y] is constant over positive cells, hence 0 there), so what is
needed in general is that every PAIR of distinct residues lies in a common support.  The certificates satisfy the strongest form.)
5.1 2 <= d <= 200 (LP certificates, QD2-T1; files QD2/certs/cert_d{d}.json).  CHECKED (c02_quick.log, c02_cert_cells.py): all 199
    certificates have q = 16 and EVERY cell vector n^(k) satisfies n^(k)\_r >= 1 for all r (ell_r >= 1/16) and sum_r n^(k)\_r = 16 d; the
    certified lower bounds on the exact weights are positive for every d (smallest 4.25e-4, d = 198), and w = 0.  So mu is a positive
    combination of atoms in Delta_d^+, and ANY single atom serves as ell\* in Step 1.
5.2 201 <= d <= 2000 and d >= 2001 (QD2-T2, QD2-T3; CONE_PROOF.md Lemmas R1-R4, B; CONE_ALLD_PROOF.md).  mu is the law of the process
    Pi\_{Phi#}: with a centred Gaussian vector eta on Z_d, ell = d Dir(1 + eta) on E = {max_r |eta_r| < 3/4} and ell = d Dir(1,..,1) on E^c.
    Conditionally on eta, ell/d is Dirichlet with all parameters >= 1/4 > 0, a law that is absolutely continuous on the OPEN simplex.
    Hence mu(Delta_d^+) = 1 = mu(Delta_d).  [PROVED, elementary.]  The representation (1.5) is exact: Lemma B (Poincare-Miranda) gives a
    Phi# for which condition (i) of Lemma R1 holds exactly, and (ii) holds by the certified slack, so v = E_mu[u^ell] + w with
    w = Delta^2 W symmetric and >= 0, a nonnegative combination of the t_s (Lemma R1).
5.3 Consequently Step 1 applies for every d >= 2 for which (1.5) is certified, i.e. (D5).

## 6. Step 5: commuting configuration ==> DKZ (x) 1 up to local unitary   [PROVED; (D6)]

6.1 By Proposition 4.2 all Q_x commute.  By (1.0), E_k = sum_a i^a Q\_{k-da}, so the E_k commute pairwise, hence so do the V_k = E_k^\*.
    (Equivalently, by paper Proposition 2.4, R has equal links.)  The transfer is exact in both directions: Q's commute <=> the reduced
    family commutes <=> R has equal links; no information is lost in passing from R to its reduced family, because R is a direct
    summand of R^V (1.2) and the reduced family is unique up to simultaneous conjugation.
6.2 Theorem B of the paper (commutative sector, all d), in (M_M, tr): with the joint spectral projections Pi_a = prod_k P\_{k,a_k}
    (a in Z_4^d), F(V) = sum_a tr(Pi_a) F(a) <= F_DKZ, and F(a) < F_DKZ for every a that is not one-step (Theorem A, equality case).
    Since F(V) = F_DKZ (1.2), Pi_a = 0 for every non-one-step a: every joint eigenvector v_mu of the V_k has a one-step configuration
    a_k(mu) = c_mu + [k >= r_mu].
6.3 Paper Corollary C, second paragraph (verbatim argument): in a joint eigenbasis R^V = (+)\_mu R^{a(mu)}; W\_{a(mu)} = gamma_mu
    X^{r_mu} W_0 X^{-r_mu} (|gamma_mu| = 1, using z^d = i), so R^{a(mu)}\_i = X^{r_mu} R^(0)\_i X^{-r_mu} and R^V is unitarily equivalent to
    R^(0) (x) 1_M.  R is unitarily equivalent to the restriction of R^(0) (x) 1_M to a reducing subspace H'.  The \*-algebra generated by
    R^(0)\_1..R^(0)\_4 is M_d(C) (it contains X and R^(0)\_1 (R^(0)\_2)^{-1} = X W_0 X^{-1} W_0^\* = z^{-1}(1 + (i-1)|0><0|), hence |0><0| and all
    matrix units X^k|0><0|X^{-l}), so the commutant of {R^(0)\_i (x) 1_M} is 1_d (x) M_M(C) and H' = C^d (x) K.  Thus d | D (D = d dim K)
    and R is unitarily equivalent to R^(0) (x) 1_K; and R^(0) = G^\* R^DKZ G with G = W_0^{-2} (paper s.2.4).
6.4 Translation to measurements.  Let u : C^D -> C^d (x) C^K be unitary with u R_i u^\* = R^DKZ_i (x) 1_K (i = 1..4).  Then
    u U_x u^\* = U^DKZ_x (x) 1, so u P^x_a u^\* = P^{x,DKZ}\_a (x) 1 (spectral projections); and u (U'\_y)^T u^\* = (U'^DKZ_y)^T (x) 1 gives,
    after transposition, conj(u) U'\_y u^T = U'^DKZ_y (x) 1, i.e. conj(u) Q^y_b conj(u)^\* = Q^{y,DKZ}\_b (x) 1.  So the local unitary
    u (x) conj(u) maps the strategy to DKZ (x) 1_K, and (u (x) conj(u)) Phi_D = Phi_d (x) Phi_K.
6.5 Uniqueness: if u_1, u_2 both do this, u_2 u_1^\* commutes with every R^DKZ_i (x) 1_K; the R^DKZ_i generate M_d(C) (conjugate of the
    R^(0)\_i by G), so u_2 u_1^\* lies in 1_d (x) U(K).
6.6 Corollary (d not dividing D).  For fixed D the strategies form a compact set (closed subset of U(D)^4) and I_d is continuous, so the
    maximum over projective strategies on Phi_D is attained; if it were I_ME(d), Theorem R would give d | D.  So for d not dividing D
    the maximum is strictly below I_ME(d).  (No uniform gap: publish/CGLMP/rigidity/RIGIDITY.md Corollary D.)
Conversely DKZ (x) 1_K attains I_ME(d) for every K.  This completes the proof of Theorem R, given (D1), (D5) and section 5.  []

## 7. Numerical sanity checks (NUMERICAL; not part of the proof; all scripts self-contained in Q_rig/, QD2/ read only)
 c01_identities.py (.log)  random NON-commuting reduced families, d = 3..12, M = 2..4: F(V) = <A,B>\_tau/2 - d/2 (1e-13); N(2d-m) = N(m),
     N(d) = d (9e-15); <A,B>\_tau - Phi_N = <v,delta> (1e-13); identity (1.4) for random and certificate cells (1.7e-12); every single
     rotated cell inequality Q^ell(rot_c Q) <= N^2 Phi_c (max -1.33); N(s) + N(d-s) <= d (max -1.69); certificate identity
     <A,B>\_tau - Phi_N = sum_k lambda_k <u^{ell_k}, delta> with the LP certificates d = 3..12 (1e-13).
 c02_quick.log / c02_cert_cells.py (.log)  section 5.1 audit of all 199 LP certificates: no failures (every n_r >= 1, q = 16, sum = 16 d,
     certified lambda bounds > 0, min 4.25e-4); float re-check (own window-form code) |sum_k lambda_k u^{ell_k} - v|/|v| <= 1.5e-14 for
     d <= 40 and d = 60, 100, 150, 200.
 c03_chain.py (.log)  the chain (3.5) term by term on step fields (d = 4, M = 2, 3): see the NUMERICAL note at the end of section 3.
 c04_residue.py (.log)  (3.1) vs direct principal-value quadrature (2e-15); derivative formula of Prop. 4.2 (2e-10); closed-form
     Herglotz function vs the Herglotz integral (2e-16) and its boundary values (error ~ 1.7(1-r)); Remark 4.3 blind spot at d = 5:
     a cell vector with ell_3 = 0 is TIGHT (-1e-13) on a non-commuting configuration with F - F_DKZ = -5.44, while a positive-cell
     certificate vector gives Q^ell - N^2 Phi_c = -5.30.
 c05_ascent.py (.log)  sanity check of Theorem R itself: BFGS ascent of F over non-commuting families (d = 3..6, M = 2, 3; 50 runs).
     All 22 runs that reach F_DKZ (gap < 1e-6) end at COMMUTING families (max ||[V_j,V_k]|| <= 2.2e-7, consistent with
     ||[V_j,V_k]||^2 = O(F_DKZ - F)); all other runs stop at spurious local maxima >= 0.72 below F_DKZ (known: B-X2).
 c06_lamstar.py (.log)  lam\* = log2/(2pi): f(lam) = lam/4 + h_lam(1/4) has f(lam\*) = G/pi^2 = Phi_c(1/4,1/4) and f'(lam\*) = 0 to 40 digits,
     f''(lam\*) = K\_{1/4}(lam\*) = 1 (strict minimum).
 c07_pointwise.py (.log)  the equality clause of (\*) along step fields (d = 4, 60 points per cell): wherever ||[B(theta), g(theta)]||\_F > 1e-3
     the (\*)-defect at lam\* is >= 0.0149 ||[B,g]||^2 (random M = 3) and >= 0.0086 ||[B,g]||^2 (rotated mixture, t = 0.1); where the
     commutator vanishes the defect is 0 (<= 3e-15); commuting one-step mixture: defect identically 0.
 Independent confirmation for small d: publish/CGLMP/rigidity (exact SOS-support rigidity, d = 3..20) proves Theorem R for d <= 20 by a
 completely different method (no (\*), no CONE_d).

## 8. Status, gaps, what remains

THEOREM R (rigidity: every projective strategy on a maximally entangled state attaining I_ME(d) is DKZ (x) 1 up to a local unitary
u (x) conj(u); d | D; u unique up to 1 (x) u'; strict inequality for d not dividing D) is PROVED FOR EVERY d >= 2, with exactly the same
inputs as the all-d optimality theorem:
  (D1) Q_2bmv/PROOF.md Theorems 1-2 (2BMV and (\*) for all M) -- RE-VERIFIED CORRECT (internal check, Q_2bmv_check/REFEREE.md).  Rigidity uses, beyond the inequality, only its equality
       clause (Theorem 2(d)), which is three lines on top of Theorem 1 (V(lam) = int int K F with K > 0, F >= 0 continuous; then D = 0 and
       the tau-marginal sum rule of Remark 4.3 give BgP = 0).  The re-verification should confirm 2(d) and Lemma 1(f) (continuity of F)
       explicitly.
  (D5) CONE_d (QD2-T3, computer-assisted).  At the last check: complete for 2 <= d <= 1766 and all d >= 2001; for the 233 pending
       values in 1767..2000 the Gaussian certificates (vg_d\*.json) exist but the Lemma B fixed-point certificates (fp_d\*.json, sweep
       QD2/run_fp.sh) were still being produced (all 1567 produced so far: ok).  Theorem R for those d is exactly as final as
       optimality for those d.
No GAP was found in the rigidity-specific part (Steps 1-5): Step 1 (positivity of every term of the cone decomposition), Step 2
(equality analysis of the Q-T1 chain, written out here with an explicit Herglotz function, explicit domination and the strip-spectrum
argument), Step 3 (residue lemma), Step 4 (certificate cells strictly positive: checked for all LP certificates, automatic for the
Dirichlet processes), Step 5 (paper Theorem B + Corollary C, verbatim) are complete.

Notes for the re-verification / write-up.
 * The suggested route's step 3 ("peel cells, match log-singular parts") is correct but unnecessary: differentiate [B_x, g] on J_x and
   apply the residue lemma (all endpoints at once).
 * The suggested route's step 4 condition ("each residue covered by some k") is not the right one in general; the right one is
   "every pair of residues in a common support" (or simply one all-positive cell vector), which all certificates satisfy.
 * Rigidity needs ONE cell vector with all cells positive and positive weight in the CONE_d representation; the uniform embedding
   alone would not do (it is not proportional to v).
 * Scope: projective measurements (PVMs); POVMs are not covered (same scope as the optimality theorem).
 * By-product: the chain gives an exact "deficit identity" F_DKZ - F = -(1/2) sum_k lambda_k (1/d) sum_c [Q^{ell_k}(rot_c Q) - N^2 Phi_c]
   = (N^2/2) sum_k lambda_k (1/d) sum_c [S_star + S_bath](ell_k, rot_c Q) (+ trivial-direction terms), i.e. the CGLMP deficit is a positive
   combination of integrated (\*)-defects (2BMV defect integrals) and bathtub slacks.  A quantitative (robust self-testing) version would
   need a lower bound of the 2BMV defect V(lam\*) by ||[B,g]||^2; not attempted here.
What remains: (1) the re-verification verdict on Q_2bmv (Theorem 2 including 2(d)); (2) the fixed-point sweep for 1397 <= d <= 2000;
(3) optional: Lean formalisation of Lemma 4.1 / Prop. 4.2 and of the Corollary C step (the latter partly exists in publish/CGLMP/lean).


## 9. Update 2026-10-02 (after the re-verification reports)
(D1) Q_2bmv Theorems 1-2 re-verified as correct (Q_2bmv_check/REFEREE.md), including the equality clause 2(d) and Lemma 1(f).
(D5) Fixed-point sweep complete (1800/1800, ALL-D CERTIFIED); the 201..600 Gaussian and fixed-point certificates are being regenerated at a
common precision (160 bits) per gap G2 of the chain re-verification (Q_chain_check/REPORT.md).  The reduction chain and this rigidity proof were
re-verified: Q_chain_check/REPORT.md, overall verdict CORRECT (items 1-6 OK).
