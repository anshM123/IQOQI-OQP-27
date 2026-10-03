import OQP27.ClassicalRigidity

/-!
# Axiom check for module L7 (`OQP27/Classical*.lean`)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Prints the axioms of the main theorems of module L7.  Expected output for every theorem:
`[propext, Classical.choice, Quot.sound]`.  Log: `OQP27/logs/ClassicalAxioms.log`.
-/

-- the classical Theorem B and Theorem A
#print axioms OQP27.ClassB.classicalTheoremB
#print axioms OQP27.ClassB.classicalTheoremB_all
#print axioms OQP27.ClassB.classical_thmA
#print axioms OQP27.ClassB.thmA_abstract
-- the cotangent representation
#print axioms OQP27.ClassB.clockFa_eq_pairK
#print axioms OQP27.ClassB.FDKZ_eq_pairK
#print axioms OQP27.ClassB.isOneStep_of_Sa_eq
#print axioms OQP27.ClassB.card_Sa
#print axioms OQP27.ClassB.disjoint_Sa
-- exchange identity and cyclic order
#print axioms OQP27.ClassB.pairK_cyc
#print axioms OQP27.ClassB.cycOrd_of_isMax
-- winding numbers and junction counting
#print axioms OQP27.ClassB.one_le_wind
#print axioms OQP27.ClassB.eq_ico_of_wind_eq_one
#print axioms OQP27.ClassB.pairK_le_wind
#print axioms OQP27.ClassB.pairK_ico_ge
-- junction estimates
#print axioms OQP27.ClassB.cot_le_kbarR
#print axioms OQP27.ClassB.kbarR_sub_cot_le
#print axioms OQP27.ClassB.kbarR_one_sub_cot
#print axioms OQP27.ClassB.junction_margin
#print axioms OQP27.ClassB.kap_strictAnti
#print axioms OQP27.ClassB.ejun_nonpos
-- the continuous inequality (scalar Q-T1)
#print axioms OQP27.ClassB.starAt_one
#print axioms OQP27.ClassB.kbar_pair_le
#print axioms OQP27.ClassB.kbar_continuum
-- consequences for the rigidity chain
#print axioms OQP27.ClassB.clockF_le_commuting
#print axioms OQP27.ClassB.jp_eq_zero_commuting
#print axioms OQP27.ClassB.commuting_optimal_relations'
#print axioms OQP27.ClassB.hyp_reductionRig_all
#print axioms OQP27.ClassB.theoremR_of_strip_cone
#print axioms OQP27.ClassB.theoremR_le_twenty_of_strip'
#print axioms OQP27.ClassB.theoremR_every_d_of_strip'
#print axioms OQP27.ClassB.maxEntClause_of_strip_cone
