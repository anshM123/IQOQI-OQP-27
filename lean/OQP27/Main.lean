import OQP27.Skeleton
import OQP27.Reduction
import OQP27.CellStripFn
import OQP27.CertAll
import OQP27.CertPos
import OQP27.StripSkeleton
import OQP27.RigidityTight
import OQP27.StripRIMain
import OQP27.ClassicalTheoremB

/-!
# OQP 27B (max-ent clause): the main theorems, assembled from the modules

This file only composes results proved in the other modules:

* `OQP27.Red.hyp_reduction` (module L2): the exact reduction strategy -> clock model -> Q-configuration
  -> linear form (`Hyp_Reduction d`, every `d`).
* `OQP27.Cell.continuumCell` (module L5): the strip inequality implies the cell-embedding inequalities
  (`Hyp_ContinuumCell d`, every `d`).
* `OQP27.coneCert_le_twenty`, `OQP27.coneCertPos_le_twenty` (module L4): `CONE_d` for `2 ≤ d ≤ 20`,
  checked by the kernel from explicit certificates.
* `OQP27.StripL3a.hyp_StripInequality_of_RI`, `hyp_StripEquality_of_RI` (modules L3a, L3b): the strip
  inequality `(*)` for every matrix size, and its equality case, from the Radon identity.
* `OQP27.Rig.theoremR_of_strip` (module L6): rigidity from `(*)`, its equality case, `CONE_d` with an
  all-positive cell vector, and the classical Theorem B.

The Radon identity is a theorem (`OQP27.StripL3b.hyp_RI`, module L3b), so the strip inequality `(*)`
for every matrix size and its equality case are proved outright (`OQP27.stripInequality`,
`OQP27.stripEquality` below), and so is the max-ent clause for `2 ≤ d ≤ 20` (`OQP27.optimality_le_twenty`).

The classical (commuting) Theorem B is a theorem as well (`OQP27.ClassB.classicalTheoremB_all`, module L7), so
rigidity for `2 ≤ d ≤ 20` is proved outright too (`OQP27.maxEntClause_le_twenty`).

The ONLY remaining named hypotheses are `OQP27.Hyp_ConeCert_large` / `OQP27.Hyp_ConeCertPos_large`: `CONE_d` for
`d ≥ 21`, established by interval-arithmetic certificates (`QD2/`: LP certificates for `d ≤ 200`, single-run
Gaussian-modulation certificates for `201 ≤ d ≤ 2000`, an analytic argument with certified bounds for `d ≥ 2001`).
-/

namespace OQP27

open OQP27.Rig

/-- **Optimality (OQP 27B, max-ent clause) for every `2 ≤ d ≤ 20`**, from the Radon identity alone. -/
theorem optimality_le_twenty_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) (d : ℕ) [NeZero d]
    (h2 : 2 ≤ d) (h20 : d ≤ 20) : OptimalityStatement d :=
  optimality_of_strip h2 (OQP27.StripL3a.hyp_StripInequality_of_RI hRI) (OQP27.Cell.continuumCell d)
    (coneCert_le_twenty d h2 h20) OQP27.Red.hyp_reduction

/-- **Optimality for every `d ≥ 2`**, from the Radon identity and the `CONE_d` certificates for `d ≥ 21`. -/
theorem optimality_all_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) (hcone : Hyp_ConeCert_large)
    (d : ℕ) [NeZero d] (h2 : 2 ≤ d) : OptimalityStatement d :=
  optimality_of_strip h2 (OQP27.StripL3a.hyp_StripInequality_of_RI hRI) (OQP27.Cell.continuumCell d)
    (coneCert_all hcone d h2) OQP27.Red.hyp_reduction

/-- **Rigidity for `d = 2`** from the Radon identity alone. -/
theorem rigidity_two_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) : RigidityStatement 2 :=
  theoremR_two_of_strip (OQP27.StripL3a.hyp_StripInequality_of_RI hRI)
    (OQP27.StripL3a.hyp_StripEquality_of_RI hRI)

/-- **Rigidity for every `2 ≤ d ≤ 20`** from the Radon identity and the classical Theorem B. -/
theorem rigidity_le_twenty_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) (d : ℕ) [NeZero d]
    (h2 : 2 ≤ d) (h20 : d ≤ 20) (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  theoremR_le_twenty_of_strip h2 h20 (OQP27.StripL3a.hyp_StripInequality_of_RI hRI)
    (OQP27.StripL3a.hyp_StripEquality_of_RI hRI) hB

/-- **The max-ent clause of OQP 27B (optimality and rigidity) for every `d ≥ 2`**, from the Radon identity,
the `CONE_d` certificates for `d ≥ 21` and the classical Theorem B; the DKZ strategy attains `I_ME(d)`. -/
theorem maxEntClause_every_d_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M)
    (hlarge : Hyp_ConeCertPos_large) (hB : ∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d)
    (d : ℕ) [NeZero d] (h2 : 2 ≤ d) : MaxEntClause d ∧ (dkz d).cglmp = IME d :=
  ⟨⟨optimality_of_strip h2 (OQP27.StripL3a.hyp_StripInequality_of_RI hRI) (OQP27.Cell.continuumCell d)
      (coneCertPos_all hlarge d h2).coneCert OQP27.Red.hyp_reduction,
    theoremR_every_d_of_strip hlarge (OQP27.StripL3a.hyp_StripInequality_of_RI hRI)
      (OQP27.StripL3a.hyp_StripEquality_of_RI hRI) hB d h2⟩, dkz_cglmp h2⟩

/-! ## Unconditional results (the Radon identity is a theorem) -/

/-- **The strip inequality `(*)` for every matrix size** (Theorem C), with no hypotheses. -/
theorem stripInequality : Hyp_StripInequality :=
  OQP27.StripL3a.hyp_StripInequality_of_RI OQP27.StripL3b.hyp_RI

/-- **Equality in `(*)` forces `[B, g] = 0`**, with no hypotheses. -/
theorem stripEquality : Hyp_StripEquality :=
  OQP27.StripL3a.hyp_StripEquality_of_RI OQP27.StripL3b.hyp_RI

/-- **OQP 27B, max-ent clause, optimality: for every `2 ≤ d ≤ 20`, every local dimension `D` and all projective
measurements on the maximally entangled state, `I_d ≤ I_ME(d)`** -- with no hypotheses. -/
theorem optimality_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) : OptimalityStatement d :=
  optimality_le_twenty_of_RI OQP27.StripL3b.hyp_RI d h2 h20

/-- **Optimality for every `d ≥ 2`**, assuming only the `CONE_d` certificates for `d ≥ 21`. -/
theorem optimality_every_d (hcone : Hyp_ConeCert_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d) :
    OptimalityStatement d :=
  optimality_all_of_RI OQP27.StripL3b.hyp_RI hcone d h2

/-- **Rigidity for `d = 2`**, with no hypotheses. -/
theorem rigidity_two : RigidityStatement 2 := rigidity_two_of_RI OQP27.StripL3b.hyp_RI

/-- **Rigidity for `2 ≤ d ≤ 20`**, assuming only the classical (commuting) Theorem B. -/
theorem rigidity_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_le_twenty_of_RI OQP27.StripL3b.hyp_RI d h2 h20 hB

/-- **The max-ent clause (optimality and rigidity) for every `d ≥ 2`**, assuming only the `CONE_d` certificates
for `d ≥ 21` and the classical Theorem B. -/
theorem maxEntClause_every_d (hlarge : Hyp_ConeCertPos_large)
    (hB : ∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d) (d : ℕ) [NeZero d] (h2 : 2 ≤ d) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d :=
  maxEntClause_every_d_of_RI OQP27.StripL3b.hyp_RI hlarge hB d h2

/-! ## Final statements (classical Theorem B is a theorem) -/

/-- **OQP 27B, max-ent clause (optimality AND rigidity), for every `2 ≤ d ≤ 20`** -- with no hypotheses:
`I_d ≤ I_ME(d)` for every local dimension and all projective measurements on the maximally entangled state,
equality only for DKZ ⊗ 1 up to a local unitary `u ⊗ ū`, and the DKZ strategy attains `I_ME(d)`. -/
theorem maxEntClause_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d :=
  ⟨⟨optimality_le_twenty d h2 h20,
    rigidity_le_twenty d h2 h20 (OQP27.ClassB.classicalTheoremB_all d h2)⟩, dkz_cglmp h2⟩

/-- **OQP 27B, max-ent clause (optimality AND rigidity), for every `d ≥ 2`**, assuming only the computer-assisted
`CONE_d` certificates for `d ≥ 21`. -/
theorem maxEntClause_all (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d :=
  maxEntClause_every_d hlarge OQP27.ClassB.classicalTheoremB_all d h2

end OQP27
