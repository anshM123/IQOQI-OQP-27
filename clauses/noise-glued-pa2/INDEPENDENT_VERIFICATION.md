# Independent verification: PA2-eps certificates

One independent re-check was done on 2026-10-20, using separately written scripts. Those scripts are not part of this
folder.

1. **Validity of the relaxation: PASS.**
   - Every moment code was compared with the true cyclic product of inner products of the unreduced word, for
     k = 3, 4, 5 and seven configurations each. The configurations were random families in C^k, C^{k+1} and C^{2k+1},
     DKZ embedded in C^{k+2}, DKZ with Bob tilted, and two degenerate cases. There were zero mismatches.
   - M_s is Hermitian and PSD, b.y = S, |y_c| <= 1 and sum Tr M_s <= k n were all verified.
   - Averaging over the shift and over conjugation is legitimate.
2. **The certified bound: PASS.**
   - The dual pairing is consistent between the solver interface and the certifier.
   - E and C are exactly Hermitian. The interval phases and I_ME are correctly enclosed.
   - The coefficients are exactly (k - 1 - 2n)/(k - 1).
   - In 120 near-singular tests checked against exact leading minors, the interval Cholesky never accepted a matrix
     that is not positive definite.
3. **Exact re-certification: PASS.** From the numerical duals, the bounds were recomputed exactly, in Q(sqrt3) for
   k = 3 and in rationals for k = 4, with positive-definiteness checked by exact leading minors. The excesses are
   6.465e-7 (k = 3) and 3.28e-6 (k = 4), matching the certifier.
4. **The glued-facet identity: PASS.**
   - Checked over 9 compositions x 21 strategies: local bound 0 in normalised form, and the ratio identity to 2e-15.
   - The behaviour convention matches PA2: core.py's Bob matrix holds the conjugates of the measured vectors.
   - The consequence requires r >= 2 blocks. This is stated in THEOREM.md.

The certificates for k = 5..10 were not re-run in this re-check. Those for k = 7..10 come from the same certifier,
with SCS producing the numerical dual. The rounding, the residuals and the Cholesky step are unchanged, and any dual
gives a valid bound. Their larger excesses come from SCS's accuracy and stay inside the margins of THEOREM.md.
