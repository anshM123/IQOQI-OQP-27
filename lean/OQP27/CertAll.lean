import OQP27.CertSmall
import OQP27.CertMid
import OQP27.CertD13
import OQP27.CertD14
import OQP27.CertD15
import OQP27.CertD16
import OQP27.CertD17
import OQP27.CertD18
import OQP27.CertD19
import OQP27.CertD20

/-!
# CONE_d for 2 ≤ d ≤ 20, checked in Lean (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

* `OQP27.coneCert_le_twenty`: `OQP27.ConeCert d` for every `2 ≤ d ≤ 20`.  Each case is a certificate checked by
  the Lean kernel (files `CertSmall`, `CertMid`, `CertD13`, …, `CertD20`) through the verified checker
  `OQP27.ConeCertificate.fullCheck_sound` (files `CertInterval`, `CertTrig`, `CertClausen`, `CertCheck`,
  `CertPipeline`).  No hypotheses; no `native_decide`.
* `OQP27.coneCert_all`: `ConeCert d` for every `d ≥ 2`, assuming the named hypothesis `OQP27.Hyp_ConeCert_large`
  (CONE_d for `d ≥ 21`), which is established by computer-assisted interval computations in Python that are not
  formalised (see `OQP27/STATUS_L4.md` for exactly what they check).

Mathematics of CONE_d: `iqoqi/programs/oqp27B_all/QD2/LOG.md`, sections 1-4.
-/

namespace OQP27

/-- CONE_d for every `d ≥ 21`.  Not formalised.  Established (computer-assisted, Python interval arithmetic) by:
the LP certificates `QD2/certs/cert_d{d}.json` checked by `QD2/verify_cone.py` for `21 ≤ d ≤ 200` (QD2-T1);
the Gaussian-modulation certificates `QD2/verify_gauss.py` + `QD2/verify_fixedpoint.py` with Lemma B of
`QD2/CONE_PROOF.md` for `201 ≤ d ≤ 2000` (QD2-T2); the analytic argument `QD2/CONE_ALLD_PROOF.md` with the interval
checks `QD2/a01..a12`, `QD2/audit_alld.py` for `d ≥ 2001` (QD2-T3).  All paths relative to
`iqoqi/programs/oqp27B_all/`; see `OQP27/STATUS_L4.md`. -/
def Hyp_ConeCert_large : Prop := ∀ d : ℕ, 21 ≤ d → ConeCert d

/-- **CONE_d for every `2 ≤ d ≤ 20`**, fully checked in Lean. -/
theorem coneCert_le_twenty (d : ℕ) (h2 : 2 ≤ d) (h20 : d ≤ 20) : ConeCert d := by
  interval_cases d
  · exact coneCert_2
  · exact coneCert_3
  · exact coneCert_4
  · exact coneCert_5
  · exact coneCert_6
  · exact coneCert_7
  · exact coneCert_8
  · exact coneCert_9
  · exact coneCert_10
  · exact coneCert_11
  · exact coneCert_12
  · exact coneCert_13
  · exact coneCert_14
  · exact coneCert_15
  · exact coneCert_16
  · exact coneCert_17
  · exact coneCert_18
  · exact coneCert_19
  · exact coneCert_20

/-- **CONE_d for every `d ≥ 2`**, given the (computer-assisted, not formalised) hypothesis for `d ≥ 21`. -/
theorem coneCert_all (h : Hyp_ConeCert_large) (d : ℕ) (hd : 2 ≤ d) : ConeCert d := by
  rcases le_or_gt d 20 with h20 | h20
  · exact coneCert_le_twenty d hd h20
  · exact h d h20

end OQP27

#print axioms OQP27.ConeCertificate.sound
#print axioms OQP27.ConeCertificate.fullCheck_sound
#print axioms OQP27.coneCert_le_twenty
#print axioms OQP27.coneCert_all
