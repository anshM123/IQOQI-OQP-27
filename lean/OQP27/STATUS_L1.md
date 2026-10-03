# STATUS of module L1 (`OQP27/Statement.lean`, `OQP27/Skeleton.lean`)

Date: 2026-10-02.  Toolchain: Lean v4.33.1, Mathlib 0df444a3 (as in `lean/`).

Build (from `lean/`):

    bash OQP27/leanrun.sh OQP27/Statement.lean -o .lake/build/lib/lean/OQP27/Statement.olean -i .lake/build/lib/lean/OQP27/Statement.ilean
    bash OQP27/leanrun.sh OQP27/Skeleton.lean  -o .lake/build/lib/lean/OQP27/Skeleton.olean  -i .lake/build/lib/lean/OQP27/Skeleton.ilean

Both files build with no errors and no warnings (`OQP27/logs/Statement.log`, `OQP27/logs/Skeleton.log`).
No `sorry`, `admit`, `axiom` or `native_decide`.  `#print axioms` of all 35 theorems listed below gives
`[propext, Classical.choice, Quot.sound]` (`OQP27/logs/L1_axioms.log`, which contains the checked file verbatim).
`Skeleton.lean` imports `OQP27.Statement` and `OQP27.CertDefs` (module L4); `Statement.lean` imports only Mathlib.

## 1. The statement (`Statement.lean`) -- everything PROVED, no hypotheses

| Lean name | Paper statement | Status |
|---|---|---|
| `IsProjection`, `PVM d D`, `Strategy d D` | projections; `d`-outcome PVMs on `C^D` (`Fin d → Matrix (Fin D) (Fin D) ℂ`); Alice's and Bob's two PVMs (index 0 = setting 1, index 1 = setting 2) | definitions |
| `PVM.mul_eq_zero` | distinct outcomes of a PVM are orthogonal | PROVED |
| `Strategy.prob` | `p(a,b\|x,y) = <Φ_D\|A_{x,a}⊗B_{y,b}\|Φ_D> = Tr(A_{x,a}ᵀ B_{y,b})/D` (real part; the trace is real) | definition |
| `Strategy.trace_nonneg`, `im_trace_eq_zero`, `prob_nonneg`, `prob_eq`, `sum_prob` | `Tr(AᵀB) ≥ 0` is real; `p ≥ 0`; `Σ_{a,b} p(a,b\|x,y) = 1` (`D ≥ 1`) | PROVED |
| `Strategy.probAB`, `Strategy.probBA`, `Strategy.cglmp` | `P(A_x = B_y + k)` = Prob(`A_x - B_y ≡ k mod d`); the CGLMP expression, eq. (1) of `paper-classical-all-d/main.tex` | definitions |
| `IME d` | `I_ME(d) = 4/(d(d-1)) Σ_{j=1}^{d-1} (d-j) sec(πj/(2d))` | definition |
| `IME_gt_two` | `I_ME(d) > 2` for `d ≥ 2` | PROVED |
| `zz`, `phaseProj`, `dkzA`, `dkzB`, `dkzPVMA`, `dkzPVMB`, `dkz` | DKZ measurements (`main.tex` s.2.4 = Collins et al. eqs. (12)-(15)), `α = (0,1/2)`, `β = (1/4,-1/4)`; entries `d^{-1} z^{∓(j-j')(4k ± 4α/β)}`, `z = e^{2πi/(4d)}` | definitions; PVM property PROVED |
| `dkzA_eq_vecMulVec`, `dkzB_eq_vecMulVec` | `A^DKZ_{x,k} = \|k>_{A,x}<k\|`, `\|k>_{A,x} = d^{-1/2} Σ_j e^{-2πij(k+α_x)/d}\|j>`; same for Bob with `e^{2πij(l-β_y)/d}` | PROVED |
| `Strategy.cglmp_eq_sum_range` | folding step of Lemma 2.1: `I_d = Σ_{t<d} (1 - 2t/(d-1)) [P(A_1-B_1≡t) + P(B_1-A_2-1≡t) + P(A_2-B_2≡t) + P(B_2-A_1≡t)]` | PROVED |
| `dkz_cglmp` | **the DKZ strategy attains `I_ME(d)`, every `d ≥ 2`** | PROVED |
| `Strategy.IsDKZTensorId` | `d ∣ D` and a unitary `u : C^D → C^d⊗C^K` with `u A_{x,a} u† = A^DKZ_{x,a}⊗1`, `ū B_{y,b} ū† = B^DKZ_{y,b}⊗1` | definition |
| `OptimalityStatement d` | for all `D ≥ 1` and all strategies on `Φ_D`: `I_d ≤ I_ME(d)` | definition (proved in Skeleton from hypotheses) |
| `RigidityStatement d` | `I_d = I_ME(d)` ⇒ `IsDKZTensorId` (Theorem R of `Q_rig/RIGIDITY_ALLD.md`) | definition (proved in Skeleton from hypotheses) |
| `MaxEntClause d` | `OptimalityStatement d ∧ RigidityStatement d` | definition |
| `dkz_isDKZTensorId`, `Strategy.IsDKZTensorId.dvd` | DKZ itself satisfies `IsDKZTensorId` with `K = 1` (non-vacuity of the rigidity statement); `IsDKZTensorId → d ∣ D` | PROVED |
| `Strategy.cglmp_congr`, `Strategy.prob_eq_dkz_of_isDKZTensorId`, `Strategy.cglmp_of_isDKZTensorId` | converse of rigidity (RIGIDITY_ALLD 6.6, last sentence): a strategy (`D ≥ 1`) that is DKZ⊗1 up to `u⊗ū` has the DKZ statistics, hence attains `I_ME(d)` | PROVED |
| `rigidity_iff` | under `RigidityStatement d`: `I_d = I_ME(d)` iff `IsDKZTensorId` (the rigidity conclusion is exactly the set of optimal strategies) | PROVED |

## 2. The skeleton (`Skeleton.lean`)

### 2.1 Objects (cone-certificates/RESEARCH_LOG.md s.4, SHARED_LEMMAS [QD2])
`QConfig d M` (27B configuration: `Q : ZMod (4d) → Matrix (Fin M) (Fin M) ℂ`, projections, and for each site `k`
the four `Q (siteIndex d k a) = Q_{k-da}`, `a : ZMod 4`, sum to 1; `siteIndex` is the same formula as L6's `Rig.siteIdx`);
`QConfig.pairCount` `T(m) = Σ_y τ(Q_{y+m} Q_{y+d})` (`A_x = Q_x`, `B_x = Q_{x+d}`, `τ = Re Tr/M`); `QConfig.netCount`
`N(m) = T(m) - T(-m)`; `QConfig.delta` `δ_m = N(m) - m`; `pairingIco d a b = Σ_{m=1}^{d-1} a_m b_m`;
`coneV d` = `v_m = 2/sin(πm/(2d))` (L4); `IsConeCell` (L4); `cellBoundary`, `cellPairKernel`
(`K^ℓ(x,y) = G(L_{x+1}-L_y) - G(L_x-L_y) - G(L_{x+1}-L_{y+1}) + G(L_x-L_{y+1})`, `G = coneG` from L4),
`cellKernelAvg` (`K̃(n) = (1/d)Σ_{r<d} K^ℓ(r+n,r)`), `cellDirection` (`u^ℓ_m = K̃(m) + K̃(2d-m)`), `IsPosConeCell`;
strip: `stripPoissonKernel` (`K_x(u) = sin(πx)/(2(cosh(πu)-cos(πx)))`, same formula as `StripL3a.stripKernel`), `hStrip`
(`(y-λ)_+` on `Re = 0`, `0` on `Re = 1`, Poisson integral inside), `posPartTrace` (`Σ_i max(λ_i, 0)`), `stripSum`
(`Σ` of `hStrip λ` over the roots of `charpoly (B + i g)`).

### 2.2 Proved

| Lean name | Paper statement | Status |
|---|---|---|
| `cellDirection_eq_coneU` | QD2-L2: kernel form `K̃(m)+K̃(2d-m)` = window form `Δ²_m (1/d)Σ_r Ĝ(S_r(m))` (L4's `coneU`) for every cell vector, `1 ≤ m ≤ d-1` | PROVED |
| `pairing_coneV_eq_sum`, `pairing_coneV_nonpos` | QD2-R1 (CONE step): `<v,δ> = Σ_k λ_k <u^{ℓ_k},δ> ≤ 0` | PROVED |
| `exists_pos_cell_tight` | RIGIDITY_ALLD s.2 (step 1): `<v,δ> = 0` ⇒ a tight cell inequality with all cells positive | PROVED |
| `optimality_of_cells`, `optimality_of_strip` | `OptimalityStatement d` from the hypotheses below | PROVED |
| `rigidity_of_cells`, `rigidity_of_strip` | `RigidityStatement d` from the hypotheses below | PROVED |
| `maxEntClause_of_strip`, `maxEntClause_all_d` | `MaxEntClause d` (and `cglmp (dkz d) = IME d`) for one / every `d ≥ 2` | PROVED |
| `ConeCertPos.coneCert`, `Hyp_ReductionRig.reduction` | the rigidity versions imply the optimality versions | PROVED |
| `QConfig.pairCount_eq_corr`, `corr_neg`, `netCount_eq_corr` | `T(m) = C(d-m)`, `C(-n) = C(n)`, `N(m) = C(m-d) - C(m+d)` with `C(n) = Σ_u τ(Q_u Q_{u+n})` (RIGIDITY_ALLD 1.4; L2's form) | PROVED |
| `IME_eq_sum_csc`, `clock_value_eq_linear` | `I_ME(d) = 4/(d(d-1)) Σ_m m csc(πm/(2d))`; `F = Σ_m csc(πm/(2d)) N(m)` ⇒ `4F/(d(d-1)) = I_ME + 2/(d(d-1))<v,δ>` | PROVED |

### 2.3 Hypotheses (HYPOTHESIS = proved on paper, enters only as an explicit argument)

| Lean name | Paper statement and location | Status |
|---|---|---|
| `Hyp_StripInequality` | (*) for every `M`, projection `B`, Hermitian `g`, real `λ`: `Tr[(P(g-λ)P)_+] ≤ Σ_{ν∈spec(B+ig)} h_λ(ν)`; `Q_2bmv/PROOF.md` Theorem 2 (re-verified, `Q_2bmv_check/REFEREE.md`) | HYPOTHESIS (target of L3) |
| `Hyp_StripEquality` | equality in (*) ⇒ `B g = g B`; `Q_2bmv/PROOF.md` Theorem 2, equality clause | HYPOTHESIS (L3) |
| `Hyp_CellInequalities d` | QD2-L1: `<u^ℓ, δ(Q)> ≤ 0` for all `M ≥ 1`, all 27B configurations, all `ℓ ∈ Δ_d`; `cone-certificates/RESEARCH_LOG.md` s.4 (ii) | HYPOTHESIS |
| `Hyp_ContinuumCell d` | `Hyp_StripInequality → Hyp_CellInequalities d` (continuum theorem Q-T1 for cell-embedded step fields + rotation average): `Q_quantum/LOG.md` s.4, s.8; `Q_rig/RIGIDITY_ALLD.md` s.3 (all steps displayed); `cone-certificates/RESEARCH_LOG.md` s.4 (ii) | HYPOTHESIS |
| `Hyp_CellEquality d` | `ℓ` with all cells positive and `<u^ℓ,δ> = 0` ⇒ all `Q_x` commute; RIGIDITY_ALLD s.2 (second half), s.3.7, s.4 (residue lemma; L6 `RigidityResidue`) | HYPOTHESIS (L6) |
| `Hyp_ContinuumCellEq d` | `Hyp_StripInequality → Hyp_StripEquality → Hyp_CellEquality d`; RIGIDITY_ALLD s.2-4 | HYPOTHESIS (L6) |
| `ConeCert d` (L4, `CertDefs.lean`) | CONE_d: `v = Σ_k λ_k u^{ℓ_k}`, finitely many `ℓ_k ∈ Δ_d`, `λ_k ≥ 0`; QD2-T1/T2/T3 (computer-assisted) | HYPOTHESIS (L4 checks small `d` in Lean) |
| `ConeCertPos d` | CONE_d with one `ℓ_k` having all cells positive and `λ_k > 0`; RIGIDITY_ALLD s.5 | HYPOTHESIS (L4) |
| `Hyp_Reduction d` | every strategy on `Φ_D` (`D ≥ 1`) has a 27B configuration on `C^M` (`M ≥ 1`) with `I_d = I_ME(d) + 2/(d(d-1)) <v,δ>`; `main.tex` Theorem 2.3 + appendix, QD-L7 | HYPOTHESIS (L2) |
| `Hyp_ReductionRig d` | as `Hyp_Reduction`, plus: if that configuration commutes and `I_d = I_ME(d)` then `IsDKZTensorId`; `main.tex` Prop. 2.4, Theorem B, Corollary C; RIGIDITY_ALLD s.6 | HYPOTHESIS (L2, L6) |

Notes on faithfulness.
* `ConeCertPos` for `d ≥ 201`: the paper's representation is `v = ∫ u^ℓ dμ(ℓ) + Σ_s w_s (e_s + e_{d-s})` with a probability
  measure `μ` charging only all-positive cells (RIGIDITY_ALLD 1.6, 5.2).  Since `ℓ ↦ u^ℓ` is continuous on the compact
  `Δ_d`, `∫ u^ℓ dμ` lies in the convex hull of `{u^ℓ : ℓ ∈ Δ_d^+}` and Carathéodory gives a finite positive combination;
  the trivial directions are positive multiples of two-residue cell directions (QD2-R2, re-checked numerically, check
  (5) below).  So the finite form stated here follows from the paper's results.  For `d ≤ 200` the LP certificates
  are already of this form (all `n_r ≥ 1`, `λ_k > 0`).
* All definitions were cross-checked numerically, independently of the Lean code (`OQP27/logs/L1_definitions_check.py`,
  output `L1_definitions_check.log`): (1) the Lean CGLMP expression on the Lean DKZ matrices equals `I_ME(d)` and
  `check_reduction.cglmp_standard`, `d = 2..9`; (2) the identity of `Hyp_Reduction` (with exactly the Lean `δ`) holds to
  `2.5e-14` on random strategies, `d = 2..6`, with the paper's twirl reduction; (3) the kernel-form `cellDirection`
  reproduces `v` from the stored certificates (`d = 2,3,4,5,7,10`, residual `≤ 1.2e-14`); (4) cell inequalities hold
  on random configurations, `δ = 0` on the DKZ window; (5) QD2-R2; (6) `hStrip` equals the `Li₂` formula of PROOF.md.

## 3. Interface notes for the other modules and the integrator
* Names: my projection predicate is `OQP27.IsProjection` (`OQP27.IsProj` is taken by `StripPencil.lean`); it is the
  same `Prop` as `OQP27.IsProj`, `OQP27.Red.IsProj`, `OQP27.Rig.IsProj` (`P.IsHermitian ∧ P * P = P`), so bridges are
  `Iff.rfl` up to the index type.  Helper lemmas carry `dkz_`/`cell_`/`chain_` prefixes to avoid clashes in `OQP27`.
* L4: `Skeleton.lean` uses L4's `ConeCert`, `coneU`, `coneV`, `IsConeCell`, `coneG` unchanged; `cellDirection_eq_coneU`
  connects them to the kernel form of QD2-L1.  `ConeCertPos d` needs, in addition to `ConeCert`, one certificate cell
  with all `n_r ≥ 1` and a certified `λ_k > 0`; the LP certificates have this, so a small strengthening of L4's
  soundness theorem gives `ConeCertPos d` directly.
* L2: `Hyp_Reduction` is stated for `Statement.Strategy` (outcomes `Fin d`) and `QConfig` (indices `ZMod (4d)`).
  L2's `Red.cglmp` (outcomes `ZMod d`) is the same expression term by term; the integrator needs the outcome
  relabelling `Fin d ≃ ZMod d`.  `netCount_eq_corr` matches L2's `N(m) = C(m-d) - C(m+d)` (real parts), and
  `clock_value_eq_linear` turns QD-L7 (`F = Σ csc(πm/(2d)) N(m)`) plus `I_d = 4F/(d(d-1))` into the form of
  `Hyp_Reduction`.
* L3: `Hyp_StripInequality`/`Hyp_StripEquality` use `hStrip` (built on `stripPoissonKernel`, literally the formula of
  `StripL3a.stripKernel`), `posPartTrace` and `stripSum` (roots of the characteristic polynomial), as fixed in
  `LEAN_BRIEF.md`.
* L6: `Hyp_CellEquality` is RIGIDITY_ALLD steps 1(b)-3; the rigidity clause of `Hyp_ReductionRig` is steps 5-6
  (`RigidityClassical`: Theorem B, Corollary C).

## 4. Files and logs
* `OQP27/Statement.lean` (1234 lines), `OQP27/Skeleton.lean` (541 lines), `OQP27/STATUS_L1.md`.
* `OQP27/logs/Statement.log`, `OQP27/logs/Skeleton.log` (stdout of `leanrun.sh`), `OQP27/logs/L1_axioms.log`,
  `OQP27/logs/L1_definitions_check.py`, `OQP27/logs/L1_definitions_check.log`.
