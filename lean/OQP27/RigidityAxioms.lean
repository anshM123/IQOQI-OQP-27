import OQP27.RigidityTight
import OQP27.RigiditySpectral

/-!
# Axiom check for module L6 (`OQP27/Rigidity*.lean`)

Every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`
(log: `OQP27/logs/RigidityAxioms.log`).
-/

-- Step 3: the residue lemma and Proposition 4.2
#print axioms OQP27.residue_scalar
#print axioms OQP27.residue_lemma
#print axioms OQP27.residue_lemma_paper
#print axioms OQP27.log_residue
#print axioms OQP27.commute_of_ae_commute
-- Step 5: the commutative sector
#print axioms OQP27.Rig.clockF_eq_sum
#print axioms OQP27.Rig.clockF_le
#print axioms OQP27.Rig.jp_eq_zero
#print axioms OQP27.Rig.commuting_optimal_relations
#print axioms OQP27.Rig.classicalTheoremB_two
#print axioms OQP27.Rig.specConfig_isConfig
#print axioms OQP27.Rig.redV_specConfig
-- Step 5: algebraic rigidity, matrix units, DKZ form
#print axioms OQP27.Rig.links_of_Vred_comm
#print axioms OQP27.Rig.twoValued_of_Vred
#print axioms OQP27.Rig.rigidity_of_Vred
#print axioms OQP27.Rig.exists_isometry_of_proj
#print axioms OQP27.Rig.exists_unitary_of_matrixUnits
#print axioms OQP27.Rig.canonical_form
#print axioms OQP27.Rig.Gdkz_conj_canonR
#print axioms OQP27.Rig.pvm_inversion
#print axioms OQP27.Rig.isDKZTensorId_of_canonical
#print axioms OQP27.Rig.rigidity_clause
#print axioms OQP27.Rig.hyp_reductionRig
-- Steps 1-2: identity (1.4), the cell hypotheses, the continuum equality analysis
#print axioms OQP27.Rig.window_sum
#print axioms OQP27.Rig.window_identity
#print axioms OQP27.Rig.cellInequalities_of_single
#print axioms OQP27.Rig.cellEqualityAE_of_continuum
#print axioms OQP27.Rig.hyp_cellEquality_of_ae
#print axioms OQP27.Rig.continuumEquality_of_tight
#print axioms OQP27.Rig.continuumCell_of_single
#print axioms OQP27.Rig.continuumCellEq_of_tight
-- Theorem R
#print axioms OQP27.Rig.rigidity_all_d
#print axioms OQP27.Rig.rigidity_all_d'
#print axioms OQP27.Rig.rigidity_all_d''
#print axioms OQP27.Rig.rigidity_of_strip_tight
#print axioms OQP27.Rig.optimality_of_single
#print axioms OQP27.Rig.maxEntClause_of_strip_tight
#print axioms OQP27.Rig.rigidity_two
#print axioms OQP27.Rig.rigidity_le_twenty
#print axioms OQP27.Rig.rigidity_every_d
#print axioms OQP27.Rig.rigidity_every_d_strip
-- The link to module L5 and the equality analysis (step (a) of s.3.7)
#print axioms OQP27.Rig.cellIneqSinglePos_of_strip
#print axioms OQP27.Rig.rigidity_of_strip_regular
#print axioms OQP27.Rig.rigidity_two_of_strip
#print axioms OQP27.Rig.conjField_eq_gconj
#print axioms OQP27.Rig.pointwise_first
#print axioms OQP27.Rig.continuumTight_of_strip
#print axioms OQP27.Rig.hyp_continuumEquality
#print axioms OQP27.Rig.hyp_cellEqualityAE
#print axioms OQP27.Rig.hyp_continuumCellEq
-- Theorem R from the strip inequality
#print axioms OQP27.Rig.theoremR_of_strip
#print axioms OQP27.Rig.maxEntClause_of_strip_thmB
#print axioms OQP27.Rig.theoremR_two_of_strip
#print axioms OQP27.Rig.theoremR_le_twenty_of_strip
#print axioms OQP27.Rig.theoremR_every_d_of_strip
