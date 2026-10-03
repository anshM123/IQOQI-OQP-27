import OQP27.StripTheorem2
import OQP27.StripLaplace
import OQP27.StripSkeleton

/-!
# Axiom check for module L3a

Every result of module L3a depends only on `propext`, `Classical.choice` and `Quot.sound`.
The mathematical hypotheses enter only as explicit arguments: `Hyp_BMV2` (Theorem 1 of the paper)
and `DensityReg` in `OQP27/StripFromBMV.lean`; in `OQP27/StripTheorem2.lean` both are discharged
from module L3b, leaving only `OQP27.StripL3b.Hyp_RI` (the Radon identity); `OQP27/StripSkeleton.lean`
proves the skeleton hypotheses `OQP27.Hyp_StripInequality` and `OQP27.Hyp_StripEquality` from it.
-/

-- the strip kernel (Lemma 5)
#print axioms OQP27.StripL3a.stripKernel_pos
#print axioms OQP27.StripL3a.stripKernel_le
#print axioms OQP27.StripL3a.fourier_stripKernel
#print axioms OQP27.StripL3a.integral_stripKernel
#print axioms OQP27.StripL3a.integral_mul_stripKernel
#print axioms OQP27.StripL3a.laplace_stripKernel
#print axioms OQP27.StripL3a.sin_mul_kernelLaplace
#print axioms OQP27.StripL3a.laplace_stripKernel_sub
-- Poisson measures, the ramp kernel, Fourier uniqueness
#print axioms OQP27.StripL3a.fourier_stripKernel_sub
#print axioms OQP27.StripL3a.fourier_rampKer
#print axioms OQP27.StripL3a.fourier_rampDefect
#print axioms OQP27.StripL3a.eq_zero_of_fourier_eq_zero
-- matrix facts
#print axioms OQP27.StripL3a.trace_pow_eq_sum_roots
#print axioms OQP27.StripL3a.trace_exp_smul_eq_sum_roots
#print axioms OQP27.StripL3a.re_mem_Icc_of_mem_roots
#print axioms OQP27.StripL3a.exists_compression_basis
#print axioms OQP27.StripL3a.posPartTrace_compress_eq
#print axioms OQP27.StripL3a.mass_moment_eq
#print axioms OQP27.StripL3a.stripD_sub_eq
#print axioms OQP27.StripL3a.stripD_eq_sub_pinch
#print axioms OQP27.StripL3a.stripD_zero_of_commute
#print axioms OQP27.StripL3a.commute_of_stripD_zero
-- Theorem 2 from Theorem 1
#print axioms OQP27.StripL3a.strip_defect_formula
#print axioms OQP27.StripL3a.strip_inequality
#print axioms OQP27.StripL3a.strip_equality_iff
-- Theorem 2 for the explicit density, from (RI)
#print axioms OQP27.StripL3a.hyp_BMV2_of_RI
#print axioms OQP27.StripL3a.strip_defect_formula_of_RI
#print axioms OQP27.StripL3a.strip_inequality_of_RI
#print axioms OQP27.StripL3a.strip_equality_iff_of_RI
-- the strip hypotheses of the skeleton (module L1), from (RI)
#print axioms OQP27.StripL3a.hyp_StripInequality_of_RI
#print axioms OQP27.StripL3a.hyp_StripEquality_of_RI
