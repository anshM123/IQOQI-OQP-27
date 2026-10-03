# STATUS of module L5 (`OQP27/Cell*.lean`): the cell-embedding inequalities from the strip inequality

Date: 2026-10-02.  Toolchain: Lean v4.33.1, Mathlib 0df444a3 (as in `lean/`).  Namespace `OQP27.Cell`.

## Result

**`OQP27.Cell.continuumCell (d : ℕ) [NeZero d] : OQP27.Hyp_ContinuumCell d`** -- PROVED, no hypotheses.

Also (file `CellRigidity.lean`, the continuum inputs of the rigidity chain of module L6):
**`OQP27.Cell.continuumCellEq (d : ℕ) [NeZero d] : OQP27.Hyp_ContinuumCellEq d`** -- PROVED, no hypotheses
(`Hyp_StripInequality → Hyp_StripEquality → Hyp_CellEquality d`), obtained from L6's `Rig.continuumCellEq_of_tight`
with `cellIneqSinglePos_of_strip : Hyp_StripInequality → Rig.Hyp_CellIneqSinglePos d` ((1.3)) and
`continuumTight_of_strip : Hyp_StripInequality → Rig.Hyp_ContinuumTight d` (step (a) of RIGIDITY_ALLD s.3.7: a tight
cell inequality with all cells positive forces equality in `(*)` at `λ*` for `(B(θ), g(θ))` a.e.).  Also
`cellIneqSingle_of_strip : Hyp_StripInequality → Rig.Hyp_CellIneqSingle d` (all cell vectors).

`Hyp_ContinuumCell d` is L1's statement (`OQP27/Skeleton.lean`) `Hyp_StripInequality → Hyp_CellInequalities d`:
the strip inequality `(*)` for every matrix size `M` (with L1's `hStrip`, `posPartTrace`, roots of `charpoly (B + i g)`)
implies QD2-L1, `pairingIco d (cellDirection d ℓ) C.delta ≤ 0`, for every `M ≥ 1`, every 27B configuration
`C : QConfig d M` and every cell vector `ℓ ∈ Δ_d` (`IsConeCell`; zero cells allowed, not only positive ones).
So the analytic link "(*) ⇒ QD2-L1" (Q_quantum/LOG.md s.4 Q-T1, Q_rig/RIGIDITY_ALLD.md s.1.5 and s.3, cone-certificates/RESEARCH_LOG.md s.4)
is fully formalised; with it, L1's `optimality_of_strip` no longer needs `Hyp_ContinuumCell` as an input.

No `sorry`, `admit`, `axiom`, `native_decide`.  `#print axioms` of every theorem listed below gives
`[propext, Classical.choice, Quot.sound]` (`OQP27/logs/L5_axioms.log`, which contains the checked file verbatim).

## Build

From `lean/`, in this order (each with `-o .lake/build/lib/lean/OQP27/<F>.olean -i .lake/build/lib/lean/OQP27/<F>.ilean`):

    CellRoots CellContour CellHerglotz CellMeanValue CellClausen CellQT1 CellLegendre CellEmbedding CellFinal CellStripFn
    CellRigidity   (needs module L6's RigidityStrip.olean; all other files are independent of L6)

e.g. `bash OQP27/leanrun.sh OQP27/CellRoots.lean -o .lake/build/lib/lean/OQP27/CellRoots.olean -i .lake/build/lib/lean/OQP27/CellRoots.ilean`.
All files build with no errors and no warnings; logs `OQP27/logs/<F>.log`.

Imports from other modules (read-only): L1 `OQP27.Skeleton` (`QConfig`, `siteIndex`, `pairCount`, `netCount`,
`delta`, `pairingIco`, `cellBoundary`, `cellPairKernel`, `cellKernelAvg`, `cellDirection`, `IsPosConeCell`,
`cellBoundary_add_period`, `corr`, `corr_neg`, `netCount_eq_corr`, `hStrip`, `posPartTrace`, `Hyp_StripInequality`,
`Hyp_CellInequalities`, `Hyp_ContinuumCell`, `Hyp_ContinuumCellEq`), L1 `OQP27.Statement` (`PVM.mul_eq_zero`), L4 `OQP27.CertDefs`
(`clausen2`, `coneG`, `IsConeCell`), L2 `OQP27.ReductionQ` (`Red.qd`, `Red.site`, `Red.label`, `Red.sum_zmod4d` and the
`qd` arithmetic), L3a `OQP27.StripKernel`/`OQP27.StripPoisson` (the kernel `StripL3a.stripKernel` -- the same formula as
L1's `stripPoissonKernel` -- its positivity, bound, integrability, mass `1 - x`), and, for `CellRigidity.lean` only,
L6 `OQP27.RigidityStrip` (`Rig.Hyp_CellIneqSinglePos`, `Rig.Hyp_CellIneqSingle`, `Rig.Hyp_ContinuumTight`,
`Rig.cellFunctional`, `Rig.windowValue`, `Rig.lamStar`, `Rig.ellFin`, `Rig.fieldB`, `cellT`, `stepField`, `stepField_eq`,
`conjField`, `Rig.continuumCellEq_of_tight`).  If any of these change, rebuild L5.

## What is proved, file by file

| Lean name | Paper statement | Status |
|---|---|---|
| **CellRoots** | eigenvalues of matrix families | |
| `mem_roots_eigvec`, `norm_le_mnorm` | a root of `charpoly X` is an eigenvalue; `‖ν‖ ≤ ∑_{ij} ‖X_ij‖` | PROVED |
| `card_roots_charpoly`, `charpoly_eq_prod_roots`, `eval_charpoly_eq_prod` | `charpoly X = ∏(X - ν)` over its `M` roots | PROVED |
| `tendsto_sum_roots` | `X_n → X` ⇒ `∑_{spec X_n} f → ∑_{spec X} f` for `f` continuous on a closed set containing the spectra ("eigenvalues move continuously", RIGIDITY_ALLD 3.5) | PROVED |
| `eventually_roots_near` | upper semicontinuity of the spectrum | PROVED |
| `differentiableOn_charpoly_coeff`, `eval_derivative_charpoly` | coefficients of `charpoly (X z)` holomorphic; `p'/p = ∑ 1/(ζ - ν)` | PROVED |
| **CellContour** | holomorphic functional calculus via contours (layer 2) | |
| `circleIntegral_logDeriv_charpoly` | `∮ (p'/p) f = 2πi ∑_{ν ∈ spec, |ν-c|<ε} f(ν)` | PROVED |
| `differentiableOn_circleIntegral_param` | circle integrals of holomorphic families are holomorphic (Cauchy formula + Fubini) | PROVED |
| `harmonicOnNhd_sum_roots` | `X` holomorphic on `U`, spectra in open `S`, `h` harmonic on `S` ⇒ `z ↦ ∑_{ν∈spec X(z)} h(ν)` harmonic on `U` (Q-T1 (ii), RIGIDITY_ALLD 3.4) | PROVED |
| **CellHerglotz** | Herglotz functions of arcs (layer 1) | |
| `arcH`, `differentiableOn_arcH`, `arcH_zero`, `sum_arcH` | `φ_{a,b}(z) = (b-a)/2π + (i/π)(Log(1-ze^{-ia}) - Log(1-ze^{-ib}))`; holomorphic on the disc; `φ(0) = (b-a)/2π`; partition sums to `1` | PROVED |
| `re_arcH_pos` | harmonic measure of a nonempty arc is `> 0` inside the disc | PROVED |
| `re_arcH_boundary`, `im_arcH_boundary`, `continuousAt_arcH_boundary` | boundary values: `Re = 1_{(a,b)}`, `Im = (ℓ(θ-a) - ℓ(θ-b))/π`, `ℓ(u) = log|2 sin(u/2)|` (RIGIDITY_ALLD (3.1)) | PROVED |
| `norm_arcH_le`, `intervalIntegrable_domH` | domination (RIGIDITY_ALLD (3.2)) | PROVED |
| **CellMeanValue** | mean value and boundary limit (layers 3-4) | |
| `roots_mem_strip`, `roots_mem_cstrip` | spectrum of `∑ w_k B_k` in the open/closed strip (RIGIDITY_ALLD 3.3) | PROVED |
| `herg`, `herg_zero`, `continuousAt_herg_boundary` | `F(z) = ∑_k φ_k(z) B_k`, `F(0) = β 1` | PROVED |
| `mean_value_boundary` | `∫₀^{2π} ∑_{ν∈spec F(e^{iθ})} h(ν) dθ = 2π M h(β)` for `h` harmonic on the open strip, continuous on the closed strip, of linear growth (RIGIDITY_ALLD (3.3)) | PROVED |
| **CellClausen** | the Clausen function as an integral | |
| `clausen2_eq_neg_integral`, `integral_ell_sub` | `Cl₂(x) = -∫₀ˣ log|2 sin(u/2)| du` for L4's Fourier-series `clausen2` | PROVED |
| `continuous_clausen2`, `clausen2_neg`, `clausen2_add_two_pi`, `clausen2_zero`, `clausen2_pi` | elementary properties | PROVED |
| **CellQT1** | Q-T1 for step fields | |
| `re_trace_mul_le_posPart`, `trace_compress`, `pointwise_star` | `Re Tr(A(g-λ)) ≤ Tr[(P(g-λ)P)_+] ≤ ∑ h(spec(B+ig))` (RIGIDITY_ALLD (3.4)) | PROVED (uses `(*)` as an argument) |
| `herg_boundary_eq` | on the arc `J_x` the boundary value is `B_x + i g(θ)` | PROVED |
| `stepField_ineq` | `(1/π)∑ κ(x,y) Re Tr(A_xB_y) - λ ∑|J_x| Re Tr A_x ≤ 2πM h(β)` (RIGIDITY_ALLD (3.5)) | PROVED (given `(*)` at `λ`) |
| **CellLegendre** | Legendre step (layer 5) | |
| `window_value` | `h(1/4) + λ*/4 = Cl₂(π/2)/π² = Φ_c(1/4,1/4)`, `λ* = log 2/(2π)`, via the one-dimensional window and the same mean-value identity (no dilogarithm needed) | PROVED |
| **CellEmbedding** | cell embedding (layer 6) | |
| `cellPartition`, `arcKernel_cellPartition` | the arcs `t_x = 2πL_x/N`; `K^ℓ = (N²/2π²) κ` | PROVED |
| `CellFamily`, `toCellFamily`, `CellFamily.rot` | 27B configurations and their rotations satisfy the operator constraints | PROVED |
| `cellFamily_ineq` | `Q^ℓ(Q) = ∑ K^ℓ(x,y) τ(A_xB_y) ≤ N²Φ_c(1/4,1/4)` (RIGIDITY_ALLD (1.3)) | PROVED (given `(*)` at `λ*`) |
| `sum_kernel_diag`, `averaged_ineq`, `fold_pairCount`, `netCount_reflect`, `netCount_d`, `window_identity` | rotation average and identity (1.4): `(1/d)∑_c [Q^ℓ(rot_c Q) - N²Φ_c] = ⟨u^ℓ, δ⟩` | PROVED |
| `cellIneq_pos` | QD2-L1 for positive cell vectors | PROVED (given `(*)` at `λ*`) |
| **CellFinal** | | |
| `cellIneq_all` | QD2-L1 for every cell vector (zero cells by continuity in `ℓ`) | PROVED (given `(*)` at `λ*`) |
| `continuumCell_of_regular` | `Hyp_hStripRegular → Hyp_ContinuumCell d` | PROVED |
| **CellStripFn** | regularity of L1's `hStrip` (Poisson integral) | |
| `stripKernel_eq_re`, `hStrip_eq_re`, `harmonicOnNhd_hStrip` | `K_x(y-s) = Re(i/(e^{iπw+πs}-1))`; `h_λ = Re H` with `H` holomorphic (differentiation under the integral); `h_λ` harmonic on the open strip | PROVED |
| `continuousOn_hStrip`, `abs_hStrip_le` | continuity on the closed strip (mass `1-x` and decay of `∫K_x|u|` as `x→0⁺`, `x→1⁻`); `|h_λ(w)| ≤ C(1+|w|)` | PROVED |
| `hStrip_regular` | `Hyp_hStripRegular` | PROVED |
| **`continuumCell`** | **`Hyp_ContinuumCell d` for every `d ≥ 1`** | **PROVED** |
| **CellRigidity** | continuum inputs of rigidity (RIGIDITY_ALLD s.3.7) | |
| `stepField_tight` | equality in Q-T1 for a step field ⇒ equality in `(*)` a.e. on every arc (vanishing integrated slack) | PROVED (given `(*)` at `λ`) |
| `cellFunctional_le_of_strip`, `cellIneqSinglePos_of_strip`, `cellIneqSingle_of_strip` | (1.3) in L6's form, positive cells / all cells | PROVED |
| `conjField_eq_gconj` | L6's conjugate function (3.1) `(1/π)∑_j (B_j - B_{j-1}) log|sin((θ-t_j)/2)|` equals `∑_y g_y(θ) B_y` | PROVED |
| `continuumTight_of_strip` | L6's `Rig.Hyp_ContinuumTight d` from `(*)` | PROVED |
| **`continuumCellEq`** | **L1's `Hyp_ContinuumCellEq d` for every `d ≥ 1`** | **PROVED** |

## Hypotheses

None remain in L5.  The strip inequality `(*)` itself is L1's `Hyp_StripInequality` (the antecedent of
`Hyp_ContinuumCell`; module L3).  `Hyp_StripInequality` is used only at `λ* = log 2/(2π)`.

## Notes

* No dilogarithm is used: the minimiser `λ*` and the value `Φ_c(1/4,1/4) = Cl₂(π/2)/π²` come out of the mean-value
  identity applied to the scalar window field (Q-R1, "∫_{B^c}(g-λ)_+ = h_λ(β)").
* With `continuumCell` and `continuumCellEq`, the skeleton hypotheses `Hyp_ContinuumCell d` and `Hyp_ContinuumCellEq d`
  are discharged for every `d`; what remains of the chain is `(*)` and its equality case (module L3), CONE_d (module L4),
  and the remaining hypotheses of modules L2/L6.
* Size: 11 files, about 5000 lines.
