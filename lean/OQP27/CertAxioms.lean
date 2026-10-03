import OQP27.CertLP
import OQP27.CertPos

/-!
# Axiom audit of module L4

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Prints the axioms of the main theorems of module L4 (`OQP27/Cert*.lean`).  Every line of the build log
`OQP27/logs/CertAxioms.log` must read `[propext, Classical.choice, Quot.sound]`.  Nothing is proved here.
-/

#print axioms OQP27.ConeCertificate.sound
#print axioms OQP27.ConeCertificate.sound_strong
#print axioms OQP27.ConeCertificate.fullCheck_sound
#print axioms OQP27.ConeCertificate.fullCheck_sound_strong
#print axioms OQP27.ConeCertificate.fullCheckU_sound
#print axioms OQP27.ConeCertificate.fullCheckWith_sound
#print axioms OQP27.ConeCertificate.coneCertPos_of_check
#print axioms OQP27.clausen2_rat
#print axioms OQP27.tail_bounds
#print axioms OQP27.mem_sinPi
#print axioms OQP27.mem_gEnc
#print axioms OQP27.mem_uList
#print axioms OQP27.coneCert_le_twenty
#print axioms OQP27.coneCertPos_le_twenty
#print axioms OQP27.coneCert_all
#print axioms OQP27.coneCertPos_all
#print axioms OQP27.coneCert_2_lp
#print axioms OQP27.coneCert_3_lp
