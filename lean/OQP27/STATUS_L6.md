# STATUS of module L6 (`OQP27/Rigidity*.lean`): rigidity of DKZ for every d (Theorem R)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.  Status as of 2026-10-02.

Paper: `proofs/rigidity/RIGIDITY.md` (Theorem R, sections 1-6), with
`CGLMP/paper-classical-all-d/main.tex` (Theorem B, Corollary C, Section 2.4) and
`CGLMP/rigidity/RIGIDITY.md` (Theorems 3.8, 3.9, 4.1, Lemma 7.2).
Imported, not edited: `CGLMPRigidity/*` (algebraic rigidity, canonical model), module L1
(`Statement.lean`, `Skeleton.lean`), module L2 (`Reduction*.lean`), module L4 (`CertDefs.lean`, `CertPos.lean`),
module L5 (`CellFinal.lean`, `CellStripFn.lean` and their imports).
Namespace: `OQP27` (residue lemma) and `OQP27.Rig` (everything else).

No `sorry`, `admit`, `axiom` or `native_decide` in `OQP27/Rigidity*.lean`.  All fourteen files build with exit code 0
and no warnings.  `#print axioms` of the 55 main theorems listed in `OQP27/RigidityAxioms.lean` gives
`[propext, Classical.choice, Quot.sound]` (log `OQP27/logs/RigidityAxioms.log`).

Build (from `lean/`, in this order; each with
`-o .lake/build/lib/lean/OQP27/<F>.olean -i .lake/build/lib/lean/OQP27/<F>.ilean`):
RigidityResidue, RigidityClassical, RigiditySpectral, RigidityClassicalTwo, RigidityBlocks, RigidityUnits,
RigidityReduction, RigidityDKZ, RigidityMain, RigidityWindow, RigidityStrip, RigidityFinal, RigidityCellBridge
(needs L5's `CellFinal`), RigidityTight (needs L5's `CellStripFn`); then
`bash OQP27/leanrun.sh OQP27/RigidityAxioms.lean`.  Logs: `OQP27/logs/<F>.log`.

## 1. Main results

`RigidityStatement d` is module L1's statement: every projective strategy on `Φ_D` attaining `I_ME(d)` has
`D = dK` and a unitary `u : ℂ^D → ℂ^d ⊗ ℂ^K` with `u A_{x,a} u† = A^DKZ_{x,a} ⊗ 1_K`, `ū B_{y,b} ū† = B^DKZ_{y,b} ⊗ 1_K`.

| Lean (file) | statement | hypotheses |
|---|---|---|
| `OQP27.Rig.theoremR_of_strip` (RigidityTight) | **Theorem R, every `d ≥ 2`** | `Hyp_StripInequality`, `Hyp_StripEquality` (L1), `ConeCertPos d` (L4), `Hyp_ClassicalTheoremB d` |
| `OQP27.Rig.theoremR_two_of_strip` (RigidityTight) | Theorem R for `d = 2` | `Hyp_StripInequality`, `Hyp_StripEquality` only |
| `OQP27.Rig.theoremR_le_twenty_of_strip` (RigidityTight) | Theorem R for `2 ≤ d ≤ 20` | `Hyp_StripInequality`, `Hyp_StripEquality`, `Hyp_ClassicalTheoremB d` (CONE_d: L4, checked in Lean) |
| `OQP27.Rig.theoremR_every_d_of_strip` (RigidityTight) | Theorem R for every `d ≥ 2` | the above, Theorem B for every `d`, L4's `Hyp_ConeCertPos_large` (`d ≥ 21`) |
| `OQP27.Rig.maxEntClause_of_strip_thmB` (RigidityTight) | optimality and rigidity (`MaxEntClause d`) | as `theoremR_of_strip` |

Finer forms (each hypothesis below is now proved from `(*)` and its equality case, see section 2):
`rigidity_all_d` (RigidityMain: `Hyp_CellInequalities d`, `Hyp_CellEqualityAE d`, `ConeCertPos d`, Theorem B),
`rigidity_all_d'` (RigidityWindow: `Hyp_CellIneqSingle d`, `Hyp_ContinuumEquality d`, `ConeCertPos d`, Theorem B),
`rigidity_of_strip_tight` (RigidityStrip), `rigidity_of_strip_regular`, `rigidity_two_of_strip` (RigidityCellBridge),
`rigidity_two`, `rigidity_le_twenty`, `rigidity_every_d`, `rigidity_every_d_strip` (RigidityFinal),
`maxEntClause_of_strip_tight` (RigidityStrip), `optimality_of_single` (RigidityWindow: `OptimalityStatement d` from
`Hyp_CellIneqSingle d` and `ConeCert d`).

Skeleton hypotheses of module L1 discharged here: `OQP27.Hyp_ContinuumCellEq d` (`hyp_continuumCellEq`,
unconditionally), `OQP27.Hyp_ReductionRig d` (`hyp_reductionRig`, from `Hyp_ClassicalTheoremB d` only),
`OQP27.Hyp_CellEquality d` (`hyp_cellEquality_of_ae`), `OQP27.Hyp_CellInequalities d` (`cellInequalities_of_single`),
`OQP27.Hyp_ContinuumCell d` (`continuumCell_of_single`; also module L5's `OQP27.Cell.continuumCell`).

Remaining hypotheses of `theoremR_of_strip`:
1. `OQP27.Hyp_StripInequality`, `OQP27.Hyp_StripEquality` (module L1; the strip inequality `(*)` and its equality
   case, `Q_2bmv/PROOF.md` Theorem 2).  Module L3a's `OQP27.StripL3a.hyp_StripInequality_of_RI` and
   `hyp_StripEquality_of_RI` (`StripSkeleton.lean`) derive both from module L3b's `∀ M, OQP27.StripL3b.Hyp_RI M`.
2. `OQP27.ConeCertPos d` (module L4): proved in Lean for `2 ≤ d ≤ 20`; `Hyp_ConeCertPos_large` for `d ≥ 21`.
3. `OQP27.Rig.Hyp_ClassicalTheoremB d` (classical Theorem B): proved here for `d = 2`.

## 2. Table

| Lean name (file) | paper statement | status |
|---|---|---|
| `OQP27.residue_scalar`, `residue_lemma`, `residue_lemma_paper` (RigidityResidue) | Lemma 4.1 (residue lemma): `∑_j J_j cot((θ - t_j)/2) = 0` on a nonempty open interval off the poles, `t_j` distinct mod `2π` ⟹ all `J_j = 0`.  Proof: with `u = e^{iθ}`, `a_j = e^{it_j}`, `cot((θ-t_j)/2) = i(u+a_j)/(u-a_j)`; the cleared polynomial has infinitely many roots, and its value at `u = a_j` is the residue `2 a_j J_j ∏_{k≠j}(a_j - a_k)` | PROVED |
| `OQP27.log_residue` (RigidityResidue) | the log form: `∑_j c_j log\|sin((θ - t_j)/2)\| = 0` on an interval ⟹ all `c_j = 0` (differentiate, then Lemma 4.1) | PROVED |
| `OQP27.cellT`, `cellT_strictMono`, `sin_ne_zero_of_mem_arc`, `cellT_exp_injective` (RigidityResidue) | the cell geometry of `ℓ ∈ Δ_d^+` (s.3.1): endpoints `t_x = 2π L_x/N` strictly increasing, distinct mod `2π`, no pole on an open arc | PROVED |
| `OQP27.stepField`, `OQP27.conjField` (RigidityResidue) | step field `B(θ) = B_x` on `[t_x, t_{x+1})`; conjugate function (3.1) `g(θ) = (1/π)∑_j (B_j - B_{j-1}) log\|sin((θ-t_j)/2)\|` | definitions |
| `OQP27.commute_of_ae_commute` (RigidityResidue) | Proposition 4.2: `[B(θ), g(θ)] = 0` for a.e. `θ ∈ (0,2π)` and all cells positive ⟹ all `B_x` commute | PROVED |
| `IsConfig`, `redV`, `clockF`, `clockFa`, `FDKZ`, `IsOneStep` (RigidityClassical) | 27B configuration, reduced family (1.0), `F(V)`, `F(a)`, `F_DKZ`, one-step configurations | definitions |
| `clockF_eq_sum` (RigidityClassical) | commuting configuration: `F(V) = ∑_a tr(Π_a) F(a)`, `Π_a = ∏_k Q_{k - d a_k}` (computed in the commutative star algebra generated by the `Q_x`) | PROVED |
| `clockF_le`, `jp_eq_zero` (RigidityClassical) | Theorem B, operator form: `F(V) ≤ F_DKZ`; equality forces `Π_a = 0` for every non-one-step `a` | PROVED from `Hyp_ClassicalTheoremB` |
| `commuting_optimal_relations` (RigidityClassical) | s.6.1-6.2: commuting optimal configuration ⟹ the reduced family commutes and satisfies `(Y_{n,k} - 1)(Y_{n,k} - i) = 0` (`RIGIDITY.md` Lemma 7.2(b)), `1 ≤ n ≤ d` | PROVED from `Hyp_ClassicalTheoremB` |
| `classicalTheoremB_two` (RigidityClassicalTwo) | Theorem B for `d = 2` (the hypothesis below is satisfiable as stated) | PROVED |
| `specConfig_isConfig`, `redV_specConfig` (RigiditySpectral) | spectral projections of an order-4 unitary family form a configuration whose reduced family is the family (standalone; the main chain uses module L2's `Qcfg`) | PROVED |
| `links_of_Vred_comm`, `twoValued_of_Vred`, `rigidity_of_Vred` (RigidityBlocks) | Lemma 7.2 for module L2's reduced family `Vred`: `[V_0,V_1] = 0` ⟹ (E_1'); `(V_0V_n^* - 1)(V_0V_n^* - i) = 0` ⟹ (T_n); hence the conclusion of `CGLMPRigidity.rigidity` | PROVED |
| `exists_isometry_of_proj`, `exists_unitary_of_matrixUnits` (RigidityUnits) | `RIGIDITY.md` Theorem 3.9 with the unitary: matrix units in `M_D(ℂ)` ⟹ `D = dK` and `u` with `u e_{jk} u^* = \|j⟩⟨k\| ⊗ 1_K` | PROVED |
| `canonical_form` (RigidityReduction) | s.6: commuting configuration and `I_d = I_ME(d)` ⟹ `u R_i u^* = R^c_i ⊗ 1_K` (canonical DKZ tuple of `CGLMPRigidity.canonical_model`) | PROVED from `Hyp_ClassicalTheoremB` |
| `Gdkz_conj_canonR` (RigidityDKZ) | `main.tex` s.2.4: the chain of L1's `dkz d` is `G R^c G^*`, `G = diag(z^{-2j})` | PROVED |
| `pvm_inversion`, `isDKZTensorId_of_canonical` (RigidityDKZ) | `RIGIDITY.md` Theorem 4.1: from the chain to the PVMs (`P_a = (1/d)∑_n w^{-na} U^n`), Bob's frame `ū` by transposition | PROVED |
| `rigidity_clause`, `hyp_reductionRig` (RigidityMain) | `Hyp_ReductionRig d` of the skeleton (with L2's `toQConfig`) | PROVED from `Hyp_ClassicalTheoremB` |
| `hyp_cellEquality_of_ae` (RigidityMain) | `Hyp_CellEquality d` of the skeleton (Step 3) | PROVED from `Hyp_CellEqualityAE` |
| `cellFunctional`, `windowValue`, `rotateCfg` (RigidityWindow) | `Q^ℓ(Q) = ∑_{x,y} K^ℓ(x,y) τ(A_x B_y)` (L1's `cellPairKernel`), `N²Φ_c(1/4,1/4) = -2G(d) = (N²/π²)Cl₂(π/2)`, rotations `Q_x ↦ Q_{x-c}` | definitions |
| `window_sum`, `window_identity` (RigidityWindow) | **identity (1.4)**: `(1/d)∑_{c<d}[Q^ℓ(rot_c Q) - N²Φ_c] = ⟨u^ℓ, δ⟩` for every configuration and cell vector | PROVED |
| `cellInequalities_of_single`, `cellEqualityAE_of_continuum` (RigidityWindow) | QD2-L1 from (1.3); s.2 eq. (2.1): a tight `⟨u^ℓ,δ⟩ = 0` makes every rotated (1.3) tight | PROVED |
| `stepField_isProjection`, `conjField_isHermitian`, `continuumEquality_of_tight` (RigidityStrip) | s.3.7 step (b): a.e. tightness of `(*)` + equality case of `(*)` ⟹ `[B(θ), g(θ)] = 0` a.e. | PROVED from L1's `Hyp_StripEquality` |
| `cellIneqSinglePos_of_strip` (RigidityCellBridge) | (1.3) with all cells positive (module L5's `OQP27.Cell.cellFamily_ineq` divided by `M`, with L5's `hStrip_regular`) | PROVED from `Hyp_StripInequality` |
| `conjField_eq_gconj` (RigidityTight) | the conjugate function (3.1) equals module L5's `gconj` on the open arcs (cyclic summation by parts, `log\|2 sin\| = log 2 + log\|sin\|`) | PROVED |
| `pointwise_first` (RigidityTight) | first half of (3.4): `Re Tr(A g) - λ Re Tr A ≤ Tr[(P(g-λ)P)_+]` for projections `A ⟂ B`, `P = 1 - B` | PROVED |
| `continuumTight_of_strip` (RigidityTight) | **s.3.7 step (a)**: `Q^ℓ(Q) = N²Φ_c` with all cells positive ⟹ `(*)` is an equality at `λ* = log 2/(2π)` for `(B(θ), g(θ))` for a.e. `θ`.  Proof: the arc integrals of `L_x = Re Tr(A_x(g - λ*))` and of `u* = ∑_{ν ∈ spec(B_x + i g)} h_{λ*}(ν)` have equal sums (tightness, L5's mean value identity and window value); `L_x ≤ Tr[(P(g-λ*)P)_+] ≤ u*` on each open arc, so the slack vanishes a.e. (module L5's `OQP27.Cell.continuumTight_of_strip` is an independent proof) | PROVED from `Hyp_StripInequality` |
| `hyp_continuumEquality`, `hyp_cellEqualityAE` (RigidityTight) | s.2-3.7: equality in the cell inequality ⟹ `[B(θ), g(θ)] = 0` a.e. | PROVED from `Hyp_StripInequality`, `Hyp_StripEquality` |
| `hyp_continuumCellEq` (RigidityTight) | L1's `Hyp_ContinuumCellEq d`: `(*)` and its equality case ⟹ `Hyp_CellEquality d` | PROVED |
| `Hyp_ClassicalTheoremB d` (RigidityClassical) | Theorem B of `paper-classical-all-d` for one joint eigenvector: `F(a) ≤ F_DKZ` for all `a ∈ ℤ_4^d`, equality only for one-step `a` (main.tex s.3-4: Theorem A, the discrete rearrangement inequality, and Lemma `lem:cot`) | HYPOTHESIS (proved for `d = 2`) |
| `Hyp_CellIneqSingle d`, `Hyp_CellIneqSinglePos d` (RigidityWindow) | (1.3): `Q^ℓ(Q) ≤ N²Φ_c(1/4,1/4)` for every configuration and every `ℓ ∈ Δ_d` (resp. all cells positive) | hypotheses of the finer forms; the positive-cell form is PROVED from `(*)` (`cellIneqSinglePos_of_strip`), the all-cell form by L5's `OQP27.Cell.cellIneqSingle_of_strip` |
| `Hyp_ContinuumEquality d` (RigidityWindow), `Hyp_ContinuumTight d` (RigidityStrip), `Hyp_CellEqualityAE d` (RigidityMain) | the continuum equality analysis (s.2-3.7), in three granularities | hypotheses of the finer forms; PROVED from `(*)` and its equality case (rows above) |
| `OQP27.Hyp_StripInequality`, `OQP27.Hyp_StripEquality`, `OQP27.ConeCertPos d` | module L1 / L3 / L4 hypotheses (L4 proves `ConeCertPos d` for `d ≤ 20`) | HYPOTHESIS (other modules) |

## 3. Numerical sanity checks of the hypotheses as stated (not part of any proof)

* `OQP27/logs/L6_check_thmB.py` (`.log`): brute force over all `a ∈ ℤ_4^d`, `d = 2..8`, with the exact Lean formulas:
  `max F(a) - F_DKZ ≤ 7e-15`, and the equality set is exactly the `4d` one-step configurations.
* `OQP27/logs/L6_check_cell.py` (`.log`): `Q^ℓ(Q) ≤ -2G(d)` on random non-commuting configurations (`d = 3, 4, 5`), and
  `Q^ℓ(window) = -2G(d)` to 10 digits.
