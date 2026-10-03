import OQP27.Skeleton
import OQP27.CertAll

/-!
# `ConeCertPos d` for 2 ≤ d ≤ 20 (module L4, for the skeleton of module L1)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

The skeleton (`OQP27/Skeleton.lean`, module L1) uses, for the rigidity chain, the strengthening
`OQP27.ConeCertPos d` of `CONE_d`: one cell vector with all cells positive carries positive weight.

* `OQP27.ConeCertificate.coneCertPos_of_check`: a certificate whose complete check passes and which contains an
  integer cell with all entries `≥ 1` proves `ConeCertPos d` (all weights of a passing certificate are positive,
  `OQP27.ConeCertificate.fullCheck_sound_strong`).
* `OQP27.coneCertPos_le_twenty`: `ConeCertPos d` for every `2 ≤ d ≤ 20` (every certificate of `CertSmall`,
  `CertMid`, `CertD13`, …, `CertD20` contains the uniform cell `(1, …, 1)`).  No hypotheses.
* `OQP27.coneCertPos_all`: `ConeCertPos d` for every `d ≥ 2`, assuming the named hypothesis
  `OQP27.Hyp_ConeCertPos_large` (`d ≥ 21`; computer-assisted in Python, not formalised: `OQP27/STATUS_L4.md`).

Paper references: `QD2/LOG.md` sections 1-4 (CONE_d), `Q_rig/RIGIDITY_ALLD.md` s.5 (positive cells), both under
`iqoqi/programs/oqp27B_all/`.
-/

namespace OQP27

namespace ConeCertificate

theorem fullCheck_q_pos (c : ConeCertificate) (h : c.fullCheck = true) : 0 < c.q := by
  unfold fullCheck at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  unfold check at h2
  simp only [Bool.and_eq_true] at h2
  have h3 := h2.1
  unfold cellsOK at h3
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  exact h3.1

/-- A passing certificate with an all-positive integer cell proves `ConeCertPos`. -/
theorem coneCertPos_of_check (c : ConeCertificate) (h : c.fullCheck = true) (k0 : ℕ)
    (hk0 : k0 < c.cells.length) (hpos : ∀ r < c.d, 1 ≤ (c.cells.getD k0 []).getD r 0) :
    ConeCertPos c.d := by
  obtain ⟨hcell, x, hxpos, hxeq⟩ := c.fullCheck_sound_strong h
  have hq : (0 : ℝ) < c.q := by exact_mod_cast c.fullCheck_q_pos h
  refine ⟨c.cells.length, fun k => cellVec c.q (c.cells.getD k []), fun k => x k,
    fun k => hcell k k.2, fun k => (hxpos k k.2).le, hxeq, ⟨k0, hk0⟩, hxpos k0 hk0, fun r hr => ?_⟩
  have h1 : (1 : ℝ) ≤ ((c.cells.getD k0 []).getD r 0 : ℝ) := by exact_mod_cast hpos r hr
  exact div_pos (by linarith) hq

end ConeCertificate

/-- `ConeCertPos 2`: cell 0 of `cert2` is all-positive. -/
theorem coneCertPos_2 : ConeCertPos 2 :=
  cert2.coneCertPos_of_check cert2_check 0 (by decide) (by decide)

/-- `ConeCertPos 3`: cell 1 of `cert3` is all-positive. -/
theorem coneCertPos_3 : ConeCertPos 3 :=
  cert3.coneCertPos_of_check cert3_check 1 (by decide) (by decide)

/-- `ConeCertPos 4`: cell 2 of `cert4` is all-positive. -/
theorem coneCertPos_4 : ConeCertPos 4 :=
  cert4.coneCertPos_of_check cert4_check 2 (by decide) (by decide)

/-- `ConeCertPos 5`: cell 3 of `cert5` is all-positive. -/
theorem coneCertPos_5 : ConeCertPos 5 :=
  cert5.coneCertPos_of_check cert5_check 3 (by decide) (by decide)

/-- `ConeCertPos 6`: cell 4 of `cert6` is all-positive. -/
theorem coneCertPos_6 : ConeCertPos 6 :=
  cert6.coneCertPos_of_check cert6_check 4 (by decide) (by decide)

/-- `ConeCertPos 7`: cell 5 of `cert7` is all-positive. -/
theorem coneCertPos_7 : ConeCertPos 7 :=
  cert7.coneCertPos_of_check cert7_check 5 (by decide) (by decide)

/-- `ConeCertPos 8`: cell 0 of `cert8` is all-positive. -/
theorem coneCertPos_8 : ConeCertPos 8 :=
  cert8.coneCertPos_of_check cert8_check 0 (by decide) (by decide)

/-- `ConeCertPos 9`: cell 0 of `cert9` is all-positive. -/
theorem coneCertPos_9 : ConeCertPos 9 :=
  cert9.coneCertPos_of_check cert9_check 0 (by decide) (by decide)

/-- `ConeCertPos 10`: cell 0 of `cert10` is all-positive. -/
theorem coneCertPos_10 : ConeCertPos 10 :=
  cert10.coneCertPos_of_check cert10_check 0 (by decide) (by decide)

/-- `ConeCertPos 11`: cell 0 of `cert11` is all-positive. -/
theorem coneCertPos_11 : ConeCertPos 11 :=
  cert11.coneCertPos_of_check cert11_check 0 (by decide) (by decide)

/-- `ConeCertPos 12`: cell 0 of `cert12` is all-positive. -/
theorem coneCertPos_12 : ConeCertPos 12 :=
  cert12.coneCertPos_of_check cert12_check 0 (by decide) (by decide)

/-- `ConeCertPos 13`: cell 0 of `cert13` is all-positive. -/
theorem coneCertPos_13 : ConeCertPos 13 :=
  cert13.coneCertPos_of_check cert13_check 0 (by decide) (by decide)

/-- `ConeCertPos 14`: cell 0 of `cert14` is all-positive. -/
theorem coneCertPos_14 : ConeCertPos 14 :=
  cert14.coneCertPos_of_check cert14_check 0 (by decide) (by decide)

/-- `ConeCertPos 15`: cell 0 of `cert15` is all-positive. -/
theorem coneCertPos_15 : ConeCertPos 15 :=
  cert15.coneCertPos_of_check cert15_check 0 (by decide) (by decide)

/-- `ConeCertPos 16`: cell 0 of `cert16` is all-positive. -/
theorem coneCertPos_16 : ConeCertPos 16 :=
  cert16.coneCertPos_of_check cert16_check 0 (by decide) (by decide)

/-- `ConeCertPos 17`: cell 0 of `cert17` is all-positive. -/
theorem coneCertPos_17 : ConeCertPos 17 :=
  cert17.coneCertPos_of_check cert17_check 0 (by decide) (by decide)

/-- `ConeCertPos 18`: cell 0 of `cert18` is all-positive. -/
theorem coneCertPos_18 : ConeCertPos 18 :=
  cert18.coneCertPos_of_check cert18_check 0 (by decide) (by decide)

/-- `ConeCertPos 19`: cell 0 of `cert19` is all-positive. -/
theorem coneCertPos_19 : ConeCertPos 19 :=
  cert19.coneCertPos_of_check cert19_check 0 (by decide) (by decide)

/-- `ConeCertPos 20`: cell 0 of `cert20` is all-positive. -/
theorem coneCertPos_20 : ConeCertPos 20 :=
  cert20.coneCertPos_of_check cert20_check 0 (by decide) (by decide)

/-- **`ConeCertPos d` for every `2 ≤ d ≤ 20`**, fully checked in Lean. -/
theorem coneCertPos_le_twenty (d : ℕ) (h2 : 2 ≤ d) (h20 : d ≤ 20) : ConeCertPos d := by
  interval_cases d
  · exact coneCertPos_2
  · exact coneCertPos_3
  · exact coneCertPos_4
  · exact coneCertPos_5
  · exact coneCertPos_6
  · exact coneCertPos_7
  · exact coneCertPos_8
  · exact coneCertPos_9
  · exact coneCertPos_10
  · exact coneCertPos_11
  · exact coneCertPos_12
  · exact coneCertPos_13
  · exact coneCertPos_14
  · exact coneCertPos_15
  · exact coneCertPos_16
  · exact coneCertPos_17
  · exact coneCertPos_18
  · exact coneCertPos_19
  · exact coneCertPos_20

/-- `ConeCertPos d` for every `d ≥ 21`.  Not formalised.  Computer-assisted (Python interval arithmetic): the LP
certificates `QD2/certs/cert_d{d}.json` (all cells with `n_r ≥ 1`, all weights certified `> 0`) for `21 ≤ d ≤ 200`
(QD2-T1); the Gaussian-modulation certificates (QD2-T2, `QD2/CONE_PROOF.md` Lemma B) for `201 ≤ d ≤ 2000`; the
analytic argument `QD2/CONE_ALLD_PROOF.md` for `d ≥ 2001` (QD2-T3); the positivity of the cells for `d ≥ 201` is
`Q_rig/RIGIDITY_ALLD.md` s.5.  All paths relative to `iqoqi/programs/oqp27B_all/`; see `OQP27/STATUS_L4.md`. -/
def Hyp_ConeCertPos_large : Prop := ∀ d : ℕ, 21 ≤ d → ConeCertPos d

/-- **`ConeCertPos d` for every `d ≥ 2`**, given the (computer-assisted, not formalised) hypothesis for
`d ≥ 21`. -/
theorem coneCertPos_all (h : Hyp_ConeCertPos_large) (d : ℕ) (hd : 2 ≤ d) : ConeCertPos d := by
  rcases le_or_gt d 20 with h20 | h20
  · exact coneCertPos_le_twenty d hd h20
  · exact h d h20

end OQP27

#print axioms OQP27.ConeCertificate.coneCertPos_of_check
#print axioms OQP27.coneCertPos_le_twenty
#print axioms OQP27.coneCertPos_all
