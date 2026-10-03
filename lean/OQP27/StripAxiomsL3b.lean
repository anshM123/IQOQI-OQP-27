import OQP27.StripBMV
import OQP27.StripRIMain
import OQP27.StripRIChain

/-!
# Axiom check for module L3b

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Every result of module L3b depends only on `propext`, `Classical.choice` and `Quot.sound`.
The Radon identity `OQP27.StripL3b.Hyp_RI M` is proved for every `M` (`OQP27.StripL3b.hyp_RI`,
`OQP27/StripRIMain.lean`), so Theorem 1 (2BMV) holds without hypotheses (`theorem1_bmv2`,
`theorem1_package`), and so do Theorem 2 and the skeleton hypotheses `OQP27.Hyp_StripInequality`,
`OQP27.Hyp_StripEquality` (`OQP27/StripRIChain.lean`, through the bridges of module L3a).
-/

-- Lemma 2 (Jensen), Lemma 1, Lemma 3(b) (files `StripJensen`, `StripPencil`, `StripSlice`, `StripBounds`)
#print axioms OQP27.StripL3b.jensen_identity
#print axioms OQP27.StripL3b.tendsto_integral_log_norm_eval
#print axioms OQP27.StripL3b.measurable_stripF
#print axioms OQP27.StripL3b.pencilRoots_pinch_im
#print axioms OQP27.StripL3b.sum_pencilRoots_pinch
#print axioms OQP27.StripL3b.pencilRoots_eq_roots_det
#print axioms OQP27.StripL3b.stripF_eq_jensen
#print axioms OQP27.StripL3b.normSq_nonreal_root_le
#print axioms OQP27.StripL3b.stripF_le
#print axioms OQP27.StripL3b.stripF_eq_zero_of_semidef
#print axioms OQP27.StripL3b.stripF_support
#print axioms OQP27.StripL3b.stripF_bound
#print axioms OQP27.StripL3b.trace_exp_smul_isHermitian
#print axioms OQP27.StripL3b.integral_exp_mul_sliceU
-- Theorem 1 from (RI) (file `StripBMV`)
#print axioms OQP27.StripL3b.trace_exp_pinch
#print axioms OQP27.StripL3b.bmvD_eq_paper
#print axioms OQP27.StripL3b.radon_eq_sliceFun
#print axioms OQP27.StripL3b.integral_exp_mul_stripF
#print axioms OQP27.StripL3b.bmv2_real
#print axioms OQP27.StripL3b.bmv2_of_RI
#print axioms OQP27.StripL3b.bmv2_of_RI_complex
#print axioms OQP27.StripL3b.laplaceF_eq_iterated
#print axioms OQP27.StripL3b.bmv2_package
-- Proof of (RI) (files `StripRIContour` ... `StripRIMain`)
#print axioms OQP27.StripL3b.circleIntegral_mul_logDeriv
#print axioms OQP27.StripL3b.hasDerivAt_circleIntegral
#print axioms OQP27.StripL3b.penPolyDt_eq
#print axioms OQP27.StripL3b.pencilRoot_im_bounds
#print axioms OQP27.StripL3b.pencilRoot_norm_bound
#print axioms OQP27.StripL3b.pencilRoot_norm_bound_all
#print axioms OQP27.StripL3b.norm_Sup_sub_le
#print axioms OQP27.StripL3b.upper_global
#print axioms OQP27.StripL3b.lower_global
#print axioms OQP27.StripL3b.upper_end
#print axioms OQP27.StripL3b.lower_end
#print axioms OQP27.StripL3b.jensen_error
#print axioms OQP27.StripL3b.norm_det_add_I_mono
#print axioms OQP27.StripL3b.tendsto_imAbsSum_vertical
#print axioms OQP27.StripL3b.tendsto_im_omegaF
#print axioms OQP27.StripL3b.hasDerivAt_Efun
#print axioms OQP27.StripL3b.exp_Gup_add_Glo
#print axioms OQP27.StripL3b.hasDerivAt_PsiD
#print axioms OQP27.StripL3b.tendsto_PsiD
#print axioms OQP27.StripL3b.exists_int_Gup_add_Glo
#print axioms OQP27.StripL3b.Psi_sub_E_affine
#print axioms OQP27.StripL3b.tendsto_im_Psi
#print axioms OQP27.StripL3b.tendsto_im_Efun
#print axioms OQP27.StripL3b.radon_identity
#print axioms OQP27.StripL3b.integrableOn_imAbsSum
#print axioms OQP27.StripL3b.hyp_RI
-- Theorem 1 without hypotheses (file `StripRIMain`)
#print axioms OQP27.StripL3b.theorem1_bmv2
#print axioms OQP27.StripL3b.theorem1_iterated
#print axioms OQP27.StripL3b.theorem1_package
#print axioms OQP27.StripL3b.radon_slices
-- The strip chain without hypotheses (file `StripRIChain`)
#print axioms OQP27.StripL3b.hyp_BMV2_stripF
#print axioms OQP27.StripL3b.strip_defect_formula_noHyp
#print axioms OQP27.StripL3b.strip_inequality_noHyp
#print axioms OQP27.StripL3b.strip_equality_iff_noHyp
#print axioms OQP27.StripL3b.hyp_StripInequality
#print axioms OQP27.StripL3b.hyp_StripEquality
