# STATUS of module L7 (`OQP27/Classical*.lean`): the classical Theorem B for every `d`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.  Status as of 2026-10-02.

Paper: `CGLMP/paper-classical-all-d/main.tex` (Theorem A, Theorem B, Lemma `lem:cot`, Section 4).
Namespace: `OQP27.ClassB`.  Imported, not edited: module L4 (`CertDefs.lean`: `clausen2`), module L5
(`CellClausen`, `CellMeanValue`, `CellQT1`, `CellLegendre`, `CellEmbedding`, `CellStripFn`), module L6
(`RigidityClassical.lean` for the statement; `RigidityTight.lean` for the corollaries), module L1
(`Skeleton.lean`: `hStrip`, `posPartTrace`).

## Result

**`OQP27.ClassB.classicalTheoremB (d : ℕ) (hd : 1 ≤ d) : OQP27.Rig.Hyp_ClassicalTheoremB d`** -- PROVED,
no hypotheses, for **every `d ≥ 1`** (`d = 1` directly; `d ≥ 2` by Theorem A).  That is: for every
`a ∈ ℤ_4^d`, `clockFa a ≤ FDKZ d`, and `clockFa a = FDKZ d` implies `IsOneStep a`.
`classicalTheoremB_all : ∀ d [NeZero d], 2 ≤ d → Rig.Hyp_ClassicalTheoremB d` is the same statement in the
form taken by the every-`d` theorems of module L6 and of `Main.lean`.

No `sorry`, `admit`, `axiom` or `native_decide` in `OQP27/Classical*.lean`.  All files build with exit code 0
and no warnings.  `#print axioms` of the 32 theorems listed in `OQP27/ClassicalAxioms.lean` gives
`[propext, Classical.choice, Quot.sound]` (log `OQP27/logs/ClassicalAxioms.log`).

**Remaining hypotheses of module L7: none.**  (The corollaries in `ClassicalRigidity.lean` keep the hypotheses
of the other modules that module L6's theorems need: `Hyp_StripInequality`, `Hyp_StripEquality`,
`ConeCertPos d` / `Hyp_ConeCertPos_large`; only `Hyp_ClassicalTheoremB` is removed.)

## Build

From `lean/`, in this order, each with
`bash OQP27/leanrun.sh OQP27/<F>.lean -o .lake/build/lib/lean/OQP27/<F>.olean -i .lake/build/lib/lean/OQP27/<F>.ilean`:
`ClassicalDefs`, `ClassicalExchange`, `ClassicalWinding`, `ClassicalJunction`, `ClassicalCot`,
`ClassicalContinuum`, `ClassicalTheoremA`, `ClassicalTheoremB`, `ClassicalRigidity`; then
`bash OQP27/leanrun.sh OQP27/ClassicalAxioms.lean`.  Logs: `OQP27/logs/<F>.log`.  About 2900 lines in total.
If module L5 or L6 rebuilds its files, rebuild `ClassicalContinuum` and everything after it.

## Route (and where it differs from the paper)

`F(a) = ⟨S_a, S_a - d⟩/2 - d/2` with `⟨A, B⟩ = ∑_{x∈A, y∈B} cot(π(x-y)/N)`, `N = 4d` (Lemma `lem:cot`), so
Theorem B is Theorem A for `N = 4d`, `|A| = |B| = d`.  Theorem A follows the paper: a maximiser exists; the
exchange identity makes it cyclically ordered; the winding number `w` (number of junctions `B|A`) is `≥ 1`;
`w = 1` means adjacent intervals; `w ≥ 2` is excluded by `⟨A,B⟩ = ⟨A,B⟩_κ̄ + ⟨A,B⟩_e` (smearing), the
continuous inequality for `κ̄` and the junction inequality for `e = κ - κ̄`.  Differences:
1. **Smearing** is definitional: `κ̄ = kbar` is written directly as the second difference of the Clausen
   function, `κ̄(m) = (N²/(2π²)) (2 Cl₂(2πm/N) - Cl₂(2π(m+1)/N) - Cl₂(2π(m-1)/N))`, and `e := κ - κ̄`.
2. **Continuous inequality** (Proposition `prop:cont`, case `N = 4d`, `|A| = |B| = d`): instead of the
   distribution identity (Lemma `lem:boole`) and the bathtub principle, we use module L5's Q-T1 for step fields
   (`Cell.stepField_ineq`) in the scalar case `M = 1` on the uniform partition, with the `1 × 1` indicator
   matrices of `A` and `B`.  Its mean value identity is the dual (Legendre) form of the bathtub argument; the
   strip inequality `(*)` it needs is an equality for `1 × 1` matrices (`starAt_one`); at `λ* = log 2/(2π)`,
   module L5's `window_value` gives `h(1/4) + λ*/4 = Cl₂(π/2)/π²`, the value at adjacent arcs.
3. **Junction estimates** (Lemma `lem:junction`): instead of the partial-fraction series of `π cot πs`, a
   second-difference comparison lemma (two monotonicity arguments) applied to `Φ = -Cl₂` (`Φ'' = ½cot(·/2)`),
   with midpoint convexity of `cot` (`e(m) ≤ 0`), concavity of `cot y - 1/y` (Lazarević's inequality
   `y³ cos y ≤ sin³ y`), and the exact second difference of `y log y`.  The bounds are
   `|e(m)| ≤ (N/π)/(6m(m²-1))` (`2 ≤ m ≤ N/2 - 1`) and `|e(1)| ≥ (N/π)(2 log 2 - 1) - π/(2N) > (7/24) N/π`
   (`N ≥ 8`); the sums telescope (`sc ≤ (N/π)/12`, `fw ≤ (N/π)/8`), so no `ζ`-values are needed and the
   margin is `2 sc + fw ≤ (7/24) N/π < |e(1)|`.
4. Theorem A is formalised only in the case `N = 4d`, `|A| = |B| = d` used by Theorem B (the continuous
   inequality is only available there through `window_value`); the combinatorial part (`thmA_abstract`) is
   proved for an abstract kernel `κ = q + e` with the properties used by the paper.

## Table

| Lean name (file) | paper statement | status |
|---|---|---|
| `kap`, `kbarR`, `kbar`, `ejun`, `pairK`, `ico`, `CycOrd`, `wind`, `scSum`, `fwSum` (ClassicalDefs) | `κ`, `κ̄` (Lemma `lem:smear`), `e = κ - κ̄`, `⟨X,Y⟩`, intervals `r + [0,L)`, cyclically ordered colourings, winding number, `sc`, `fw` (Lemma `lem:junction`(4)) | definitions |
| `pairK_swap`, `pairK_self`, `pairK_univ`, `pairK_cyc` (ClassicalExchange) | Lemma `lem:cyclic`: `⟨A,B⟩ = ⟨B,C⟩ = ⟨C,A⟩` for odd kernels | PROVED |
| `pairK_image_add`, `image_add_ico` (ClassicalExchange) | rotation invariance | PROVED |
| `cycOrd_of_isMax` (ClassicalExchange) | Lemma `lem:swap` + Corollary `cor:monotone` (first part): every maximiser is cyclically ordered | PROVED |
| `one_le_wind`, `eq_ico_of_wind_eq_one` (ClassicalWinding) | Corollary `cor:monotone`: `w ≥ 1`; `w = 1` gives `(r + [0,a), r + [-b,0))` | PROVED |
| `wind_count_le`, `pairK_le_wind`, `pairK_ico_ge` (ClassicalWinding) | Lemma `lem:junctionineq`: `E(A,B) ≤ w e(1) + w sc` for cyclically ordered `(A,B)`, `E(A₀,B₀) ≥ e(1) - fw` | PROVED |
| `cot_le_kbarR`, `ejun_nonpos` (ClassicalJunction) | Lemma `lem:junction`(3): `e(m) ≤ 0` for `1 ≤ m ≤ N/2` | PROVED |
| `kbarR_sub_cot_le` (ClassicalJunction) | `|e(m)| ≤ (N/π)/(6m(m²-1))`, `2 ≤ m ≤ N/2 - 1` (variant of Lemma `lem:junction`(1),(3)) | PROVED |
| `kbarR_one_sub_cot` (ClassicalJunction) | `|e(1)| > (7/24) N/π`, `N ≥ 8` (variant of Lemma `lem:junction`(3)) | PROVED |
| `junction_margin` (ClassicalJunction) | the margin `2 sc + fw < |e(1)|` (eq. `eq:margin`) | PROVED |
| `kap_neg`, `kbar_neg`, `ejun_neg`, `kap_strictAnti` (ClassicalJunction) | `κ`, `κ̄`, `e` odd; `cot` strictly decreasing on `(0, π)` | PROVED |
| `starAt_one` (ClassicalContinuum) | the strip inequality `(*)` for `1 × 1` matrices (an equality) | PROVED |
| `kbar_pair_le`, `kbar_continuum`, `pairK_kbar_ico` (ClassicalContinuum) | Proposition `prop:cont` for unit cells, `N = 4d`, `|A| = |B| = d`: `⟨A,B⟩_κ̄ ≤ ⟨[0,d),[-d,0)⟩_κ̄ = (N²/π²) Cl₂(π/2)` | PROVED |
| `Sa`, `card_Sa`, `card_Sa_sub`, `disjoint_Sa`, `clockFa_eq_pairK`, `FDKZ_eq_pairK`, `isOneStep_of_Sa_eq` (ClassicalCot) | Lemma `lem:cot`: `F(a) = ⟨S_a, S_a - d⟩/2 - d/2`, `F_DKZ = ⟨[0,d),[-d,0)⟩/2 - d/2`, `S_a` an interval ⟹ `a` one-step | PROVED |
| `thmA_abstract`, `card_ico`, `disjoint_ico_ico` (ClassicalTheoremA) | conclusion of the proof of Theorem A (abstract kernel, `N = 4d`, `a = b = d`) | PROVED |
| `classical_thmA` (ClassicalTheoremB) | **Theorem A**, `N = 4d`, `a = b = d`, `d ≥ 2`, with its equality case | PROVED |
| `classicalTheoremB`, `classicalTheoremB_all` (ClassicalTheoremB) | **Theorem B for `M = 1`** = module L6's `Hyp_ClassicalTheoremB d`, every `d ≥ 1` | PROVED |
| `clockF_le_commuting`, `jp_eq_zero_commuting`, `commuting_optimal_relations'` (ClassicalRigidity) | **Theorem B** (commuting configurations, every `d ≥ 1`) and its equality case (module L6's `clockF_le`, `jp_eq_zero`, `commuting_optimal_relations` with Theorem B discharged) | PROVED |
| `hyp_reductionRig_all` (ClassicalRigidity) | module L1's `Hyp_ReductionRig d`, every `d ≥ 2` | PROVED |
| `theoremR_of_strip_cone`, `theoremR_le_twenty_of_strip'`, `theoremR_every_d_of_strip'`, `maxEntClause_of_strip_cone` (ClassicalRigidity) | module L6's Theorem R / max-ent clause without the hypothesis `Hyp_ClassicalTheoremB` | PROVED from the other modules' hypotheses (`(*)`, its equality case, CONE_d) |

Build logs: `OQP27/logs/ClassicalDefs.log`, `ClassicalExchange.log`, `ClassicalWinding.log`,
`ClassicalJunction.log`, `ClassicalCot.log`, `ClassicalContinuum.log`, `ClassicalTheoremA.log`,
`ClassicalTheoremB.log`, `ClassicalRigidity.log`, `ClassicalAxioms.log`.

## Numerical sanity checks (not part of any proof)

`OQP27/logs/L7_check_junction.py` (`.log`): in 30-digit arithmetic, for `4 ≤ N ≤ 80` and `N ∈ {100, 101, 128, 200}`,
the statements of `ClassicalJunction.lean` (no violation; the bound `kbarR_sub_cot_le` is sharp to within
`0.3%`, and `(2 sc + fw)/|e(1)| ≤ 0.679`).  Module L6's `OQP27/logs/L6_check_thmB.py` checks Theorem B itself
by exhaustion for `d ≤ 8`.

## Notes for the other modules

* Module L6's `OQP27.Rig.Hyp_ClassicalTheoremB d` is now a theorem for every `d ≥ 1`
  (`OQP27.ClassB.classicalTheoremB`); the theorems of module L6 and of `Main.lean` that take it as an argument
  can be applied to `classicalTheoremB d _` or `classicalTheoremB_all`.
* `ClassicalContinuum.lean` uses module L5's `Cell.stepField_ineq`, `Cell.window_value`,
  `Cell.hStrip_regular`, `Cell.hStrip_left/right`, `Cell.sum_roots_one_by_one`, `Cell.one_by_one_eq`,
  `Cell.sum_range_eq_sum_zmod`, and `Cell.clausen2_*`.  It does not use `Hyp_StripInequality`.
