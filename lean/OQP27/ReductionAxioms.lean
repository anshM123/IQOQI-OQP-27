import OQP27.Reduction

/-!
# Axiom check for module L2 (reduction)

Every main theorem of `OQP27/Reduction*.lean` depends only on `[propext, Classical.choice, Quot.sound]`.
Output: `OQP27/logs/ReductionAxioms.log`.
-/

-- scalar identities, Lemma 2.1, eq. (Strace)
#print axioms OQP27.Red.val_eq_fourier
#print axioms OQP27.Red.hd_mul_zd_pow
#print axioms OQP27.Red.cglmp_eq_chain
#print axioms OQP27.Red.chainS_trace
-- Theorem 2.3(2): the reduced family
#print axioms OQP27.Red.Vred_unitary
#print axioms OQP27.Red.Vred_pow_four
#print axioms OQP27.Red.ntr_Vred
#print axioms OQP27.Red.chainS_eq_clockF
#print axioms OQP27.Red.cglmp_eq_clockF
-- the Q-configuration and QD-L7
#print axioms OQP27.Red.Nnet_pair
#print axioms OQP27.Red.Qcfg_isConfig
#print axioms OQP27.Red.clockF_eq_csc
#print axioms OQP27.Red.Nnet_d
#print axioms OQP27.Red.Nnet_reflect
#print axioms OQP27.Red.Nnet_add_reflect_le
#print axioms OQP27.Red.Qcfg_famOf
-- eq. (projform)
#print axioms OQP27.Red.pairing_odd_kernel
#print axioms OQP27.Red.pairing_cot
#print axioms OQP27.Red.projform
-- Theorem 2.3(1): covariant strategies
#print axioms OQP27.Red.specPVM_isPVM
#print axioms OQP27.Red.pvmU_specPVM
#print axioms OQP27.Red.Lam_Rcov
#print axioms OQP27.Red.sum_cd_Lam_Rcov
#print axioms OQP27.Red.cglmp_cov
-- Theorem 2.3(2): direct summand
#print axioms OQP27.Red.Jt_isometry
#print axioms OQP27.Red.direct_summand
#print axioms OQP27.Red.redFamily_direct_summand
-- integration with modules L1 / Skeleton
#print axioms OQP27.Red.cglmp_strategy
#print axioms OQP27.Red.cglmp_eq_csc_strategy
#print axioms OQP27.Red.deficit_strategy
#print axioms OQP27.Red.cglmp_le_IME_iff
#print axioms OQP27.Red.cglmp_eq_cglmp_cov
#print axioms OQP27.Red.hyp_reduction
#print axioms OQP27.Red.optimality_of_clock
#print axioms OQP27.Red.clock_of_optimality
#print axioms OQP27.Red.optimality_iff_clock
#print axioms OQP27.Red.optimality_iff_config
