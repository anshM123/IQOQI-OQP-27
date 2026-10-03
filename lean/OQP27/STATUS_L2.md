# STATUS_L2 -- module L2 (reduction): strategy -> clock model -> Q-configuration -> linear form

Owner files (namespace `OQP27.Red`): `OQP27/ReductionBasic.lean`, `ReductionChain.lean`, `ReductionClock.lean`,
`ReductionQ.lean`, `ReductionCsc.lean`, `ReductionSpectral.lean`, `ReductionCovariant.lean`, `ReductionProj.lean`,
`ReductionTwirl.lean`, `Reduction.lean` (imports all of them), and the check file `ReductionAxioms.lean`.
Build logs: `OQP27/logs/<File>.log` (stdout of `OQP27/leanrun.sh`); axiom check: `OQP27/logs/ReductionAxioms.log`.
Toolchain: Lean v4.33.1, Mathlib 0df444a3. Build order = the order of the file list above.
All files build with exit code 0 and no warnings; no `sorry`/`admit`/`axiom`/`native_decide`;
`#print axioms` of all 37 main theorems: `[propext, Classical.choice, Quot.sound]`.

**Integration (no hypotheses remain in module L2).**
* `OQP27.Red.hyp_reduction : OQP27.Hyp_Reduction d` (every `d` with `[NeZero d]`, i.e. every `d >= 1`).
* `OQP27.Red.optimality_iff_clock (hd : 2 <= d)`: `OptimalityStatement d <-> (F(V) <= F_DKZ for every family of
  order-4 unitaries of every size)` (paper Theorem 2.3, "consequently" clause, both directions).
* `OQP27.Red.optimality_iff_config (hd : 2 <= d)`: `OptimalityStatement d <-> (<v, delta> <= 0 for every
  QConfig d M, M >= 1)`, `v_m = 2 csc(pi m/2d)`, `delta_m = N(m) - m`.

Paper references: `CGLMP/paper-classical-all-d/main.tex` ("paper"); QD-L7 = `SHARED_LEMMAS (working notes; the lemma is proved in `papers/math`)` [QD]; R1.x = `proofs/rigidity/RIGIDITY.md` s.1.

| Lean name | Statement (paper) | Status | File |
|---|---|---|---|
| `val_eq_fourier` | eq. (mfourier): `m(t) = (d-1)/2 + sum_{n=1}^{d-1} c_n w^{nt}`, `c_n = -1/(1-w^{-n})` | PROVED | ReductionBasic |
| `hd_mul_zd_pow` | appendix: `4 c_n z^{-n} = -h_n` (as `h_n z^n = -4 c_n`), `h_m = sec psi_m - i csc psi_m` | PROVED | ReductionBasic |
| `cd_reflect`, `secd_reflect`, `cscd_reflect` | `c_{d-n} = conj c_n`, `sec psi_{d-m} = csc psi_m` | PROVED | ReductionBasic |
| `cglmp` | the CGLMP expression, eq. (cglmp) (behaviour level, outcomes in `Z/d`) | DEF | ReductionChain |
| `cglmp_eq_chain` | Lemma 2.1: `I_d = 4 - 2S/(d-1)` (normalised behaviours, `d >= 2`) | PROVED | ReductionChain |
| `IsPVM.mul_eq_zero`, `pvmU_pow`, `pvmU_unitary`, `pvmU_pow_d` | PVM calculus: `U = sum_a w^a P_a`, `U^n = sum_a w^{na} P_a`, `U` unitary, `U^d = 1` | PROVED | ReductionChain |
| `chainR` | chain unitaries eq. (chainR): `R_1 = U_2, R_2 = (U'_2)^T, R_3 = U_1, R_4 = (U'_1)^T` | DEF | ReductionChain |
| `chainS_trace` | eq. (Strace): `S = 2(d-1) + sum_n c_n Lambda_n(R)` for max-ent probabilities `Tr(A^T B)/D` | PROVED | ReductionChain |
| `Vred` | reduced family of Thm 2.3(2) (twirl + Stone-von Neumann in the explicit basis `f_{s,v}` of `H_0`): `V_k = sum_s \|s><s+1\| (x) z^{-k} R_{s+1}^{-k} R_{s+2}^k`, `M = 4D` | DEF | ReductionClock |
| `Vred_unitary`, `Vred_pow_four` | `V_k` unitary, `V_k^4 = 1` | PROVED | ReductionClock |
| `ntr_Vred` | `tr(V_j V_k^*) = z^{k-j} Lambda_{k-j}(R)/4` | PROVED | ReductionClock |
| `clockF` | clock functional eq. (F): `F(V) = sum_{j<k} Re[h_{k-j} tr(V_j V_k^*)]` | DEF | ReductionClock |
| `chainS_eq_clockF`, `cglmp_eq_clockF` | **Thm 2.3(2)**: `S = 2(d-1) - (2/d)F(V)`, `I_d = 4F(V)/(d(d-1))`, every projective max-ent strategy | PROVED | ReductionClock |
| `specProj_*`, `sum_specProj`, `sum_iz_smul_specProj` | spectral projections of an order-4 unitary, `Q_a = (1/4) sum_t i^{-at} E^t` | PROVED | ReductionQ |
| `qd`, `site`, `label`, `qd_eq`, `sum_zmod4d` | `x = k - d a` in `Z_{4d}`; the bijection `Z_{4d} = {0..d-1} x Z/4` | PROVED | ReductionQ |
| `Ccorr`, `Nnet`, `piQ` | `C(n) = sum_u tau(Q_u Q_{u+n})`, `N(m) = C(m-d) - C(m+d)`, pair couplings `pi_{jk}(t)` (R1.4) | DEF | ReductionQ |
| `Nnet_pair` | R1.4(c): `N(m) = sum_{k-j=m}[pi(1)-pi(3)] + sum_{k-j=d-m}[pi(0)-pi(2)]` | PROVED | ReductionQ |
| `Qcfg`, `Qcfg_isConfig` | the 27B configuration of a clock family (R1.3) | PROVED | ReductionCsc |
| `clockF_eq_csc` | **QD-L7**: `F(V) = sum_{m=1}^{d-1} csc(pi m/2d) N(m)` | PROVED | ReductionCsc |
| `Nnet_d`, `Nnet_reflect` | R1.4(a): `N(d) = d`, `N(2d-m) = N(m)` | PROVED | ReductionCsc |
| `Nnet_add_reflect_le` | R1 eq. (1.2) (QD2-R2): `N(s) + N(d-s) <= d` | PROVED | ReductionCsc |
| `famOf`, `Qcfg_famOf` | every 27B configuration is the configuration of a clock family | PROVED | ReductionCsc |
| `specPVM_isPVM`, `pvmU_specPVM` | any unitary `R` with `R^d = 1` is `sum_a w^a P_a` for a PVM (paper s.2.2, "conversely") | PROVED | ReductionSpectral |
| `Rcov`, `Lam_Rcov`, `ntr_Lzero` | covariant strategy eq. (covariant); all four links have trace `tau(L^(0)_n) = (z^{-n}/d)[...]` | PROVED | ReductionCovariant |
| `sum_cd_Lam_Rcov`, `cglmp_cov` | **Thm 2.3(1)**: `S(R^V) = 2(d-1) - (2/d)F(V)`, `I_d(R^V) = 4F(V)/(d(d-1))` | PROVED | ReductionCovariant |
| `pairing_odd_kernel`, `pairing_odd_kernel_fold` | R1.4(b) for every odd kernel `K`: `sum_{x,y} K(x-y) tau(A_x B_y) = sum_{m=1}^{2d-1} K(m)N(m) = d K(d) + sum_{m<d} (K(m)+K(2d-m)) N(m)` | PROVED | ReductionProj |
| `pairing_cot`, `projform` | R1.4(b): `<A,B>_tau = d + sum_m 2csc(pi m/2d) N(m)`; **eq. (projform)**: `F(V) = (1/2)<A,B>_tau - d/2` | PROVED | ReductionProj |
| `Jt_isometry`, `direct_summand` | **Thm 2.3(2), direct summand**: isometry `J` with `R^V_i J = J R_i` | PROVED | ReductionTwirl |
| `FDKZ_eq_csc`, `IME_eq_FDKZ` | `F_DKZ = sum (d-m) sec psi_m = sum m csc psi_m`, `I_ME = 4F_DKZ/(d(d-1))` | PROVED | Reduction |
| `cglmp_strategy` | adapter: `OQP27.Strategy.cglmp` (L1) = `cglmp` of `probME` | PROVED | Reduction |
| `cglmp_eq_clockF_strategy`, `cglmp_eq_csc_strategy` | Thm 2.3(2) and QD-L7 for `OQP27.Strategy` | PROVED | Reduction |
| `cglmp_eq_cglmp_cov`, `redFamily_direct_summand` | Thm 2.3(2) for `OQP27.Strategy`: `I_d(R) = I_d(R^V)`; `R` is a direct summand of `R^V` | PROVED | Reduction |
| `deficit_strategy` | `I_ME - I_d = 4/(d(d-1)) (F_DKZ - F(V)) = 4/(d(d-1)) sum csc psi_m (m - N(m))` | PROVED | Reduction |
| `cglmp_le_IME_iff` | `I_d <= I_ME(d) <=> F(V) <= F_DKZ` (reduced family of the strategy) | PROVED | Reduction |
| `toQConfig`, `toQConfig_delta`, `qcfg_delta_eq` | transport to `OQP27.QConfig d (4D)`; `delta_m = N(m) - m` | PROVED | Reduction |
| **`hyp_reduction`** | **`OQP27.Hyp_Reduction d`** (Skeleton) | **PROVED** | Reduction |
| `optimality_of_clock`, `clock_of_optimality`, `optimality_iff_clock` | Thm 2.3 "consequently": optimality on max-ent states `<=>` `F <= F_DKZ` for all order-4 families | PROVED | Reduction |
| `optimality_iff_config` | optimality `<=>` `<v, delta> <= 0` for every 27B configuration | PROVED | Reduction |

Notes.
* The reduced family is the paper's one for the explicit orthonormal basis `f_{s,v} = d^{-1/2} sum_j e_{s+4j} (x) v`
  of `H_0 = ker(W^4 - 1)`; with it the Stone-von Neumann step is an explicit block formula,
  `I_d = 4F(V)/(d(d-1))` follows from `tr(V_j V_k^*) = z^{k-j} Lambda_{k-j}(R)/4`, and the summand `r = 0` of the
  twirl is the range of the explicit isometry `J v = d^{-1/2} sum_k |k> (x) |0> (x) R_1^{-k} v`.
* Modules L5/L6 import `ReductionQ`, `ReductionClock`, `Reduction` (`qd`, `site`, `label`, `Vred`, `chainR`, `stratA/B`,
  `redConfig`, `toQConfig`, ...); names and signatures of these are kept stable. `CellEmbedding`, `RigidityBlocks`,
  `RigidityReduction` were re-checked against the final L2 files (exit code 0).
