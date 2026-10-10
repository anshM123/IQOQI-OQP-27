# White-noise robustness against all Bell inequalities at d = 4: the complete facet list of L(2,2,4)

Ansh Mishra, Aryan Senthilkumar. Computer-assisted; independently re-implemented (`INDEPENDENT_CHECK.md`); not
externally reviewed.

**The question (clause C2).** On the maximally entangled state Phi_d, mix the state with white noise,
rho_v = v |Phi_d><Phi_d| + (1 - v) 1/d^2, and let v_c(p) = max{v : v p + (1 - v) u in L} be the critical visibility
of the behaviour p of complete von Neumann measurements (u = uniform behaviour). C2 says that the DKZ measurements
have the smallest critical visibility against ALL Bell inequalities, v_c(p) >= 2/I_ME(d), with equality only for
DKZ. It holds for d = 2 (Tsirelson and Fine) and d = 3 (see `../noise-literal/`); this folder proves d = 4.

Notation: L = L(2,2,d) local polytope (Collins-Gisin coordinates, dimension n = 4d(d-1), vertices = the
d^4 deterministic points), NS = no-signalling polytope = {x : p(ab|xy)(x) >= 0 for all x,y,a,b}, G = relabelling group
(outcome permutations of the four measurements, setting swaps, party swap; |G| = 8 (d!)^4), u = uniform behaviour,
kappa_d = I_ME(d)/2.  "Neighbours" of a facet = facets sharing a ridge with it (dual graph of L).

## 0. Results

| Item | Statement | Status |
|---|---|---|
| Theorem V (visibility criterion) | a facet list of L containing the positivity facets is complete iff (i) every NON-positivity listed facet has all its ridge-neighbours in the list and (ii) every non-local vertex of NS violates some listed facet; the positivity class never has to be expanded | PROVED (Sec. 2) |
| Theorem F4 | L(2,2,4) has exactly 11 665 992 facets in the 34 G-classes of adj_d4_small_final.pkl (the Jesus-Zambrini Cruzeiro list) | PROVED (computer-assisted, exact; Sec. 3) |
| Theorem D4 = C2 at d = 4 | every max-ent strategy with balanced PVMs (any D) has white-noise critical visibility >= 2/I_ME(4) = 0.6905497... against ALL Bell inequalities, equality iff DKZ; the bound also holds for all PVMs on Phi_4 (Lemma CG) | PROVED (computer-assisted; Sec. 4) |
| Corollary P4 | a positivity facet of L(2,2,4) has exactly 7 539 571 facets (63 shared with positivity facets, 7 539 508 with the 33 other classes) | PROVED (Sec. 4) |
| Class 0 (160-vertex lifted CHSH) | expansion finished (64 111 ridges, every neighbour in the list); the independent re-run covers 31 of 33 classes and NOT classes 0 and 1 | PROVED (Sec. 3.1), independent re-run incomplete |
| Validation | the same pipeline, started from ONE seed facet and expanding only non-positivity classes, proves completeness of L(2,2,2) (24 facets) and L(2,2,3) (1116 facets) | done (logs/CLOSE_verify_d2.log, logs/CLOSE_verify_d3.log) |
| NS(2,2,d) vertices, d <= 4 | exactly the deterministic points and the generalised PR boxes PR_k (k = 2..d), counts C(d,k)^4 (k!)^3 (k-1)!; d = 4: 204 160 = 256 + 10 368 + 110 592 + 82 944 | PROVED (exact DD + independent adjacency closure), agrees with Barrett et al. PRA 71, 022101 (2005) |

Status: PROVED, computer-assisted with exact arithmetic, and confirmed by a second implementation that shares no code
with these scripts (`INDEPENDENT_CHECK.md`; it also re-expands classes 0 and 1). Not externally reviewed. Nothing in
the argument uses the positivity expansion (> 7.5 million ridges per positivity facet), the obstacle of earlier
approaches. Priority: as far as we found, no completeness proof of the (2,2,4) facet list has been published;
Jesus & Zambrini Cruzeiro (PRA 108, 052220 (2023)) and Staufenbiel (arXiv:2604.22859) give the same list without a
completeness proof.

## 1. Why the positivity class looked unavoidable, and why it is not

Balinski-type arguments cannot skip positivity: in L(2,2,2) the CHSH facets are adjacent ONLY to positivity facets, so
an adjacency closure that never expands positivity could miss a whole class "hidden behind" positivity.  Pure graph
arguments inside a positivity facet P fail by a fixed margin: P has 63 positivity-type facets but its dual graph is
only 47-connected (generally, #positivity facets - (dim - 1) = (total number of outcomes) + 1 > 0 for every face of
this kind).  The way out is geometric: a hidden class must still be cut off from NS by some non-local vertex of NS,
and the facets cut off by one point form a connected set that never contains a positivity facet.

## 2. Theorem V and its proof

Setting (any polytopes): L a full-dimensional polytope in R^n, NS = {x : f_i(x) >= 0, i = 1..m} a bounded polyhedron
with L subset NS, such that every inequality f_i >= 0 defines a facet of L ("positivity facets").

**Lemma 1 (every other facet is seen from a vertex of NS).**  If F is a facet of L that is not a positivity facet,
then some vertex w of NS strictly violates the inequality of F, and every such w lies outside L.
*Proof.*  Let beta <= c be the inequality of F.  If no vertex of NS strictly violates it, it is valid on NS = conv(vert NS), so
F subset NS cap {beta = c} =: F_NS, a proper face of NS (beta is not constant on L) of dimension >= dim F = n-1, i.e. a
facet of NS.  Every facet of NS = {f_i >= 0} is NS cap {f_i = 0} for some i, so F subset L cap {f_i = 0} =: P_i, which
is a facet of L.  Two facets with F subset P_i coincide: F = P_i, a contradiction.  Vertices of NS in L satisfy beta <= c.
QED

**Lemma 2 (visibility sets are connected).**  For any point y, the set Vis(y) of facets of L whose inequality y
strictly violates induces a connected subgraph of the dual graph of L.
*Proof.*  Fix z in int L and the polar L° = {g : g.(x - z) <= 1 for all x in L}.  Facets F of L correspond to vertices
g_F of L°, ridges of L to edges of L° (the two endpoints are the two facets through the ridge).  With phi(g) =
g.(y - z): F is strictly violated by y iff phi(g_F) > 1.  From any vertex with phi > 1 the simplex method gives a path
along edges of L° on which phi strictly increases, ending in the phi-maximal face M of L° (a vertex that is not
phi-maximal has an improving edge, since the tangent cone at a vertex is generated by edge directions); all vertices
on the path and all vertices of M have phi > 1, and the graph of the face M is connected.  QED
(Lemma 2 is classical: the facets visible from a point form a connected region, cf. beneath-beyond and the
Bruggesser-Mani line shellings; only its combination with Lemma 1 in Theorem V is used here.)

**Theorem V.**  Let K be a set of facets of L that contains all positivity facets.  Assume
 (i) every facet in K that is not a positivity facet has all its ridge-neighbours in K, and
 (ii) every vertex of NS outside L strictly violates some facet in K.
Then K is the set of all facets of L.
*Proof.*  Let U be a facet of L, not a positivity facet.  By Lemma 1 a vertex w of NS outside L violates U; by (ii)
w violates some K0 in K.  No positivity facet is violated by w (w is in NS), so K0 is not a positivity facet and
Vis(w) contains no positivity facet.  By Lemma 2 there is a path K0 = F_0, F_1, ..., F_m = U of neighbours inside
Vis(w).  Induction: F_t in K and not positivity => F_{t+1} in K (by (i)) and F_{t+1} not positivity (it is in Vis(w)).
Hence U in K.  QED

Remarks.  (a) The converse is trivial, so (i)+(ii) is an exact criterion.  (b) Both hypotheses are necessary in
general: for L(2,2,2) the list {positivity} satisfies (i) vacuously and fails (ii) (the PR boxes violate no listed
facet); a list missing a class adjacent to a listed non-positivity class fails (i).  (c) If K is G-invariant, (i) need
only be checked for one representative per class and (ii) for one vertex per G-orbit of non-local vertices.
(d) For the (2,2,d) scenario the non-local vertices of NS are the generalised PR boxes PR_k, k = 2..d, up to
relabelling (Barrett, Linden, Massar, Pironio, Popescu, Roberts 2005; re-derived exactly below for d <= 4), and PR_k
violates the (lifted) CGLMP_k inequality.  Hence, FOR EVERY d: a G-invariant list containing positivity and the lifted
CGLMP_k (k <= d) classes is complete as soon as its non-positivity classes are closed under ridge adjacency.  The
positivity class never needs to be expanded.
(e) Generalisation (used in the d = 5 assessment, Sec. 6): Lemma 1 and Theorem V hold verbatim with NS replaced by
any bounded polyhedron O = intersection of the half-spaces of a set S of facets of L and "positivity" replaced by S.
(f) The hypothesis that every f_i >= 0 defines a facet of L is not needed: if L cap {f_i = 0} has lower dimension,
the inclusion F subset L cap {f_i = 0} in Lemma 1 is impossible outright.  It holds for (2,2,d) anyway (checked).

## 3. Verification for d = 4 (and the validation runs d = 2, 3)

Script: `python CLOSE_verify.py d` (d = 2, 3, 4); logs/CLOSE_verify_d2.log, logs/CLOSE_verify_d3.log; for d = 4 the run
was split for memory reasons: logs/CLOSE_verify_d4.log = (A), (B'), (C)
(`--skip-polar`) and logs/CLOSE_verify_d4_polar.log = (A), (B), (C) (`--skip-adm`); each of the two runs alone proves
the theorem.  Every decision is exact (python integers / Fractions); floating point only proposes candidates that are
re-derived and verified exactly.  All double-description runs of the CLOSE_ scripts use CLOSE_dd_safe.py, which
certifies before every step that no int64 overflow can occur (2 S M^2 < 2^62, M = largest ray entry; the largest
entry seen was 48 in the polar DD and <= 5 elsewhere).

(A) Class data and hypothesis (i).
 * The 34 representatives of adj_d4_small_final.pkl are exact facets (integer slacks >= 0, exact affine rank 47 of the
   tight sets); class 25 is the positivity class and all 64 inequalities p(ab|xy) >= 0 are facets of L (exact affine
   rank 47 each).  Orbit sizes (exhaustive over G, from the 2026-10-02 run) sum to 11 665 992; positivity orbit 64.
 * All 33 non-positivity classes are expanded: all ridges of the representative by exact double description, exact
   rotation to the neighbour, identification with a listed representative by an explicit relabelling g with
   g.slack = slack(rep) checked in integers (adjacency_d4.py, adjacency_big.py; logs/adjacency_d4_small.log,
   logs/adjacency_d4_big.log; data adj_d4_small_final.pkl + adj_d4_full.pkl).  No neighbour outside the 34 classes.
   Double counting orbit_i a_ij = orbit_j a_ji holds for all 33 x 33 pairs.
 * Class 0 (160-vertex lifted CHSH, the last open class besides positivity) had in fact finished in the 2026-10-02
   run: 64 111 ridges, peak 196 465 intermediate rays, neighbours in classes 0..33 only (logs/adjacency_d4_big.log;
   saved in adj_d4_full.pkl); the job then entered the positivity DD (1.6 million rays at step 131/192) and ended
   without completing it.
 * Independent re-run of all 33 expansions (CLOSE_reexpand.py, seeded random insertion order = different initial
   simplex and pivoting path; logs/CLOSE_reexpand_small.log, logs/CLOSE_reexpand_big.log,
   logs/CLOSE_reexpand_c0.log, logs/CLOSE_reexpand_c1.log): re-expansion reproduced for 31 of the 33 non-positivity classes; classes 0 and 1 were not re-run here (logs/CLOSE_reexpand_c0.log and _c1.log contain only the start line); they are
   re-expanded by the independent implementation (`INDEPENDENT_CHECK.md`).
   In addition, for every class the number of positivity neighbours is recomputed WITHOUT double description (exact
   affine rank of the intersection of the tight set with each of the 64 positivity tight sets) and agrees with the DD.
(B) Vertices of NS(2,2,4) (hypothesis (ii), first half).  NS - u = {y : q_i.y <= 1} with integer q_i = -16 A_i
   (p(ab|xy) = c_i + A_i.x, verified on all deterministic points); its vertices are the facets of conv{q_i}: exact DD
   (64 points in R^48) gives 204 160 vertices, each re-verified exactly (all 64 forms >= 0, zero exactly on the reported
   tight set).  Classification: 256 deterministic points; every other vertex is g.PR_k for an explicit outcome
   relabelling g (pr_structure: perfect-matching supports with weights 1/k and a single k-cycle holonomy; equality
   W = g.PR_k checked entry by entry): 10 368 PR_2, 110 592 PR_3, 82 944 PR_4, exactly C(4,k)^4 (k!)^3 (k-1)!.
(B') Independent check of (B).  All NS-edges at one vertex of each type (extreme rays of the tangent cone by exact DD,
   endpoint by an exact ratio test): deterministic 32 097 edges (to 237 deterministic, 5 508 PR_2, 21 168 PR_3, 5 184
   PR_4), PR_2 1 536, PR_3 169, PR_4 48 edges; every neighbour is deterministic or a PR_k.  Since the graph of NS is
   connected and outcome relabellings are automorphisms of NS, this alone proves that every vertex of NS is
   deterministic or a relabelled PR_k (an argument independent of the polar DD; both use the same compiled DD step).
(C) Hypothesis (ii), second half.  PR_2, PR_3, PR_4 violate facets of class 0 (lifted CHSH), 13 (lifted CGLMP_3) and
   17 (CGLMP_4) by exactly 1/2, 2/3, 3/4 (LP proposal, exact re-derivation and facet test, explicit relabelling onto the
   representative, exact evaluation).  With the explicit relabellings of (B), every non-local vertex of NS violates a
   listed facet.
=> Theorem V applies: **the 34 classes (11 665 992 facets) are all facets of L(2,2,4).**

Validation (same script, from scratch): d = 2 -- one seed (the facet maximally violated by PR_2), expansion of the
non-positivity class only -> 2 classes, 24 facets, NS = 16 + 8 vertices, COMPLETE.  d = 3 -- one seed (facet
maximally violated by PR_3), expansion of the 3 non-positivity classes only (positivity never expanded) -> 4 classes,
1116 facets (= Collins-Gisin; = our earlier full closure, logs/closure_d3.log), NS = 81 + 648 + 432 vertices,
double counting exact, COMPLETE.

## 4. Consequences

**Theorem F4 (PROVED).**  The local polytope of the (2,2,4) scenario has exactly 11 665 992 facets in 34 G-classes:
10 lifted CHSH, 7 lifted CGLMP_3, CGLMP_4, the 7 non-CGLMP symmetric facets of Bancal-Gisin-Pironio, 2 further genuine
4-outcome classes, 4 + 2 classes lifted from the mixed scenarios, positivity (per-class table at the end of Sec. 4).  This is the
list found by Jesus & Zambrini Cruzeiro (PRA 108, 052220 (2023)): same class count, family breakdown and total
(class-by-class comparison not done).  As far as we found, they and Staufenbiel (arXiv:2604.22859) state no completeness proof.  The 34 classes are pairwise G-inequivalent (34
distinct G-invariant signatures, CLOSE_d4_extras.py (2), logs/CLOSE_d4_extras.log), so the orbits are disjoint and
the total is the sum of the orbit sizes.

**Theorem D4 (PROVED) -- clause C2 at d = 4.**  For every maximally entangled strategy with balanced PVMs (any local
dimension D; in particular rank-one PVMs on Phi_4) the white-noise critical visibility against all Bell inequalities
satisfies v_c >= 2/I_ME(4) = 0.6905497395..., with equality iff the behaviour is the DKZ behaviour up to relabelling.
By Lemma CG (Sec. 4a) the bound v_c >= 2/I_ME(4) also holds for all PVMs (any ranks, zero allowed) on Phi_4, where white state
noise acts on the behaviour as the product of the marginals; the equality statement is for the balanced case.
*Proof.*  v_c(p) = min over facets beta with beta(p) > beta(u) of (beta_L - beta(u))/(beta(p) - beta(u)); all
quantities are G-invariant, and by Theorem F4 the facets are the 34 classes.  Positivity is never violated;
class 17 is exactly CGLMP_4 (explicit relabelling onto the CGLMP_4 inequality I_4 <= 2 with I_4(u) = 0,
CLOSE_d4_extras.py (1)), so its ratio is max_ME I_4 / 2 <= kappa_4 with equality iff DKZ (max-ent CGLMP
optimality and rigidity, Theorems 1 and 2 of the main result; Lean-verified for d <= 20); each of the other 32 classes has a certified max-ent ratio bound
< kappa_4 (level-2 tracial relaxation over
all balanced max-ent strategies, rigorous dual certificate, independently re-certified with exact Bareiss
positive-definiteness: logs/verify_sdp_exact.log, logs/verify_sdp_exact_all.log, logs/check_d4_summary.log; largest
1.4142292 < kappa_4 = 1.4481216, class 9).  QED
Gap corollary: if the critical facet of a balanced max-ent behaviour at d = 4 is not a CGLMP_4 copy, then
v_c >= 1/1.4142292 = 0.707099 (exact Bareiss certificate; the floating-point-certified bound 1.4142143 of d4_ratios.pkl
gives 0.707106).

**Corollary P4 (PROVED).**  A positivity facet P of L(2,2,4) (240 vertices, dimension 47) has exactly 7 539 571 facets:
its facets are the ridges P cap F' with F' adjacent to P; by Theorem F4 every such F' is in the 34 classes; the number of
class-j neighbours is orbit_j a_{j,25}/64 (double counting from the expansions; every a_{j,25} also recounted without
DD in CLOSE_reexpand.py), summing to 7 539 508, plus the 63 other positivity facets (all adjacent to P: exact affine
rank 46 of each pairwise intersection, CLOSE_d4_extras.py (3)); logs/CLOSE_d4_extras.log.

### 4a. Lemma CG (arbitrary PVM ranks reduce to rank one)
Statement.  For PVMs of arbitrary ranks (zero allowed) on Phi_d with behaviour p and white noise n_p,
v_c(p; n_p) >= v_c(p~; u) for a rank-one PVM strategy p~ on Phi_d.
Proof.  Refine each projector in an orthonormal basis adapted to C^d = (+)_a range(A^x_a): p = c(p~), n_p = c(u) for
the coarse-graining c (basis index -> block), and p~ has uniform marginals.  c is linear and maps deterministic
points to deterministic points, so c(L) is contained in L; v p~ + (1-v) u in L implies v p + (1-v) n_p in L.  QED
(Not covered: Phi_D with D > d and unbalanced ranks -- the refinement has D outcomes -- and POVMs.)

### 4b. Per-class table

Ratio LB = gradient ascent over rank-one PVMs on Phi_4; certified ratio UB = level-2 tracial
relaxation over all balanced max-ent strategies (any D), with a rigorous dual certificate.

| # | type | eff. outcomes | tight | orbit | ratio LB | certified ratio UB | margin to kappa_4 |
|---|---|---|---|---|---|---|---|
| 0 | lifted CHSH | (2, 2, 2, 2) | 160 | 1024 | 1.276142 | 1.276146 | +0.1720 |
| 1 | lifted CHSH | (2, 2, 2, 2) | 160 | 1536 | 1.276142 | 1.276148 | +0.1720 |
| 2 | lifted CHSH | (2, 2, 2, 2) | 128 | 3072 | 1.000000 | 1.000003 | +0.4481 |
| 3 | lifted CHSH | (2, 2, 2, 2) | 128 | 2304 | 1.000000 | 1.000004 | +0.4481 |
| 4 | lifted CHSH | (2, 2, 2, 2) | 96 | 1024 | 0.600000 | 0.600008 | +0.8481 |
| 5 | lifted CHSH | (2, 2, 2, 2) | 96 | 1536 | 0.600000 | 0.600002 | +0.8481 |
| 6 | lifted CHSH | (2, 2, 2, 2) | 144 | 2304 | 1.236693 | 1.236695 | +0.2114 |
| 7 | lifted CHSH | (2, 2, 2, 2) | 128 | 3456 | 1.207107 | 1.207484 | +0.2406 |
| 8 | lifted CHSH | (2, 2, 2, 2) | 112 | 2304 | 1.000000 | 1.000004 | +0.4481 |
| 9 | lifted CHSH | (2, 2, 2, 2) | 128 | 648 | 1.414214 | 1.414214 | +0.0339 |
| 10 | lifted CGLMP_3 | (3, 3, 3, 3) | 104 | 82944 | 1.349174 | 1.349191 | +0.0989 |
| 11 | lifted CGLMP_3 | (3, 3, 3, 3) | 91 | 165888 | 1.150623 | 1.161265 | +0.2869 |
| 12 | lifted CGLMP_3 | (3, 3, 3, 3) | 89 | 82944 | 1.150623 | 1.160844 | +0.2873 |
| 13 | lifted CGLMP_3 | (3, 3, 3, 3) | 104 | 82944 | 1.349174 | 1.349176 | +0.0989 |
| 14 | lifted CGLMP_3 | (3, 3, 3, 3) | 88 | 82944 | 1.150623 | 1.160188 | +0.2879 |
| 15 | lifted CGLMP_3 | (3, 3, 3, 3) | 105 | 41472 | 1.349174 | 1.349189 | +0.0989 |
| 16 | lifted CGLMP_3 | (3, 3, 3, 3) | 82 | 20736 | 1.000000 | 1.000029 | +0.4481 |
| 17 | CGLMP_4 (BGP S1) | (4, 4, 4, 4) | 80 | 82944 | 1.448122 | 1.448124 | = kappa_4 (theorem) |
| 18 | BGP S2 | (4, 4, 4, 4) | 72 | 663552 | 1.366056 | 1.368076 | +0.0800 |
| 19 | BGP S3 | (4, 4, 4, 4) | 60 | 663552 | 1.262110 | 1.263400 | +0.1847 |
| 20 | BGP S4 | (4, 4, 4, 4) | 64 | 1327104 | 1.383603 | 1.383672 | +0.0644 |
| 21 | BGP S5 | (4, 4, 4, 4) | 55 | 221184 | 1.266650 | 1.276149 | +0.1720 |
| 22 | BGP S6 | (4, 4, 4, 4) | 56 | 331776 | 1.331365 | 1.331401 | +0.1167 |
| 23 | BGP S7 | (4, 4, 4, 4) | 68 | 1327104 | 1.319401 | 1.319429 | +0.1287 |
| 24 | BGP S8 | (4, 4, 4, 4) | 56 | 1327104 | 1.302423 | 1.302892 | +0.1452 |
| 25 | positivity | (2, 1, 1, 2) | 240 | 64 | 1.000000 | 1.000007 | +0.4481 |
| 26 | lifted from mixed (3/4) scenario | (3, 4, 3, 4) | 82 | 165888 | 1.260298 | 1.260335 | +0.1878 |
| 27 | lifted from mixed (3/4) scenario | (4, 4, 3, 4) | 76 | 663552 | 1.362748 | 1.362776 | +0.0853 |
| 28 | lifted from mixed (3/4) scenario | (3, 4, 4, 3) | 81 | 331776 | 1.356556 | 1.356563 | +0.0916 |
| 29 | genuine (new vs BGP) | (4, 4, 4, 4) | 64 | 1327104 | 1.380042 | 1.380055 | +0.0681 |
| 30 | lifted from mixed (3/4) scenario | (4, 3, 4, 4) | 72 | 331776 | 1.249410 | 1.249471 | +0.1987 |
| 31 | lifted from mixed (3/4) scenario | (4, 3, 4, 3) | 75 | 663552 | 1.241705 | 1.241742 | +0.2064 |
| 32 | genuine (new vs BGP) | (4, 4, 4, 4) | 58 | 1327104 | 1.247914 | 1.247949 | +0.2002 |
| 33 | lifted from mixed (3/4) scenario | (4, 3, 3, 4) | 72 | 331776 | 1.225592 | 1.225607 | +0.2225 |

## 5. Reproduction

    python CLOSE_verify.py 2        # ~1 s      logs/CLOSE_verify_d2.log
    python CLOSE_verify.py 3        # ~2 s      logs/CLOSE_verify_d3.log
    python CLOSE_verify.py 4        # ~3 min    logs/CLOSE_verify_d4.log   (add --orbits to recompute orbit sizes)
    python CLOSE_reexpand.py 2026 <classes>     # independent re-expansion (class 0 / 1: ~1 h each)
    python check_d4_summary.py      # saved per-class ratio certificates
Inputs: adj_d4_small_final.pkl, adj_d4_full.pkl (class representatives, orbits, saved expansions).
Code: CLOSE_lib.py (positivity forms, NS vertex enumeration, tangent cones, PR-structure recognition, violated facets),
facet_lib.py, dd_numba.py / dd_fast.py / dd_exact.py, closure_check.py (rotation), adjacency_d4.py (find_g).

## 6. Assessment: d = 5 and the facet-free route (honest feasibility estimates)

### 6.1 d = 5
What Theorem V changes.  For every d, completeness of a G-invariant list of facet classes of L(2,2,d) that contains
positivity and the liftings of CGLMP_k (k = 2..d) is EQUIVALENT to the ridge-adjacency closure of its NON-positivity
classes (Remark (d) of Sec. 2: the non-local vertices of NS(2,2,d) are the PR_k up to relabelling, Barrett et al. 2005,
and PR_k violates lifted CGLMP_k).  So the positivity bottleneck is gone for all d.  What remains is hard:
 * Facet classes of L(2,2,5): not known to us (we are not aware of a complete or candidate class list for five
   outcomes).  L(2,2,5): 625 vertices, dimension 80, |G| = 8 (5!)^4 = 1 658 880 000,
   NS(2,2,5) has 97 712 625 vertices (625 + 80 000 PR_2 + 4 320 000 PR_3 + 51 840 000 PR_4 + 41 472 000 PR_5).
 * Size of the classes that would have to be expanded (CLOSE_d5_probe.py, logs/CLOSE_d5_probe.log): the facets
   maximally violated by PR_2, PR_3, PR_4, PR_5 have 425, 292, 210, 175 tight vertices (175 = CGLMP_5); the outcome
   liftings of the 34 classes of L(2,2,4) have up to 425 tight vertices (lifted CHSH), typically 150-300.  At d = 4 the
   largest expanded class had 160 tight vertices in dimension 47 (peak 207 755 intermediate rays, ~1 h).
 * Feasibility test (logs/CLOSE_d5_dd_cglmp5.log): exact DD of the CGLMP_5 facet (175 points, dimension 79) reached
   119 678 intermediate rays at step 71 of 95 and was still growing when stopped for memory
   reasons.  CGLMP_5 is the SMALLEST genuine 5-outcome class; the lifted classes are 1.5-2.5 times larger.
 * Number of classes (CLOSE_d5_lifts.py, logs/CLOSE_d5_lifts.log): the outcome liftings of the 33 non-positivity
   classes of L(2,2,4) alone give AT LEAST 1250 pairwise inequivalent facet classes of L(2,2,5) (distinguished by a
   G-invariant of the slack tensor; each verified as a facet exactly: hyperplane recomputed from the tight set, slack
   tensor equal up to a positive factor, exact affine rank 79).  Liftings from the mixed 3/4/5-outcome scenarios and
   the genuine 5-outcome classes come on top.  PROVED lower bound: >= 1250 classes.
Estimate.  A d = 5 closure by plain exact DD is NOT feasible in this programme: Theorem V would need the expansion of
every non-positivity class (>= 1249, many with 250-425 tight vertices in dimension 79), and plain DD already explodes
on the smallest genuine class.  Realistic routes, in order of promise:
 (a) a lifting-adjacency lemma: a lifted facet F' (new outcome copying outcome c of one measurement) is the Cayley
     polytope conv(F u tau(F_c)) in the new-outcome marginal (F_c = face of F where that measurement shows c, tau =
     the copy map), so by the Cayley trick its ridges correspond to the facets of the Minkowski sum F + tau(F_c),
     which are determined by the normal fans of the parent facet F and of its face F_c.  If this can be turned into an
     algorithm using only data of the parent scenario, only the genuine 5-outcome classes (175-~300 tight vertices)
     need DD;
 (b) Theorem V with NS replaced by O = NS cap (half-spaces of the lifted classes) (Remark (e)): then lifted classes
     need no expansion at all, at the price of enumerating the vertices of O outside L (a symmetric vertex
     enumeration in dimension 80, size unknown);
 (c) PANDA-style recursive symmetric adjacency decomposition: weeks-months of CPU on a dedicated machine.
 Status: C2 at d = 5 OPEN (numerical evidence only: no strategy below 2/I_ME(d) in our global searches, for general
 bases up to d = 12 and for Fourier-type families up to d = 16).

### 6.2 Facet-free route ("SOS local models")
New data (sdp_rounding.py): level 2 at d = 4 gives s* = 0.4043 (logs/CLOSE_sos_d4_l2.log).  Together with d = 2:
0.7071 = 1/sqrt2 (tight) and d = 3: 0.4702, the level-2 values for d >= 3 are BELOW the trivial universal bound 1/2 of
Lemma U, and decrease with d, while the target 1/kappa_d stays near 0.69.  Structural reason: the weights mu_lam are
LINEAR in the tracial moment matrix, so they cannot represent product constructions such as Lemma U's
mu_1 = p(a0 b0|00) p(a1 b1|11) (quadratic in moments), which already give 1/2.  Level 3 at d = 3 (basis 345, 5 439
moment classes) failed for lack of memory.  Sizes: level k has ~(4(d-1))^k basis words, so level 3 is out of reach for d >= 4.
Estimate: the linear SOS-local-model hierarchy is not a realistic route to 1/kappa_d for d >= 3.  A facet-free all-d
proof needs a new family of local models that is at least quadratic in the moments ("glued" link models that contain
both Lemma U's product model and DKZ's partially coupled opposite links, which reproduce DKZ exactly), with positivity certified by SOS -- no candidate is known.  Status: OPEN, low feasibility.

### 6.3 What would move C2 forward most
1. (done) independent check of Theorem V and of the d = 4 computations by a separate implementation
   (`INDEPENDENT_CHECK.md`): CONFIRMED.
2. (research) the lifting-adjacency lemma of 6.1(a) -- with Theorem V it would reduce every d to the genuine classes.
3. (research) a quadratic local-model family for the facet-free route.
