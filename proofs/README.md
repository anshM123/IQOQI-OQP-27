# Proofs and their re-verification

The complete, polished proofs are in the mathematical paper, [`papers/math/main.pdf`](../papers/math/main.pdf). This folder
holds the working write-ups the paper was assembled from. Each one sits next to the report of a separate re-verification
(re-derivation of the proof and numerics re-implemented with separately written code) and the scripts of that check.
These reports are internal checks, not peer review; the work has not yet been reviewed by outside experts.

| Folder | Contents | Verification |
|---|---|---|
| [`strip-inequality/`](strip-inequality/) | Theorem 4 (two-variable BMV with an explicit positive density) and Theorem 3 (the strip inequality for every matrix size, exact defect, equality case), via Paley–Wiener–Schwartz and Fourier-slice inversion | `INDEPENDENT_VERIFICATION.md`: correct |
| [`radon-identity/`](radon-identity/) | an elementary, distribution-free proof of the Radon identity (complex Burgers equation for the pencil roots), and from it Theorems 3 and 4; this is the route formalised in Lean | `INDEPENDENT_VERIFICATION.md`: correct |
| [`rank-one-alternative/`](rank-one-alternative/) | a second proof of Theorem 3 for rank-one B, by a different method (reduction to Cauchy quantiles, and an argument-principle count of critical points), which gives Theorem 3 for all M ≤ 5 | `INDEPENDENT_VERIFICATION.md`: correct |
| [`rigidity/`](rigidity/) | Theorem 2 for every d (equality analysis, residue lemma, positive cells, classical theorem) | covered by the report in `reduction-chain/` |
| [`reduction-chain/`](reduction-chain/) | re-verification of the reduction, the continuum theorem, the cell inequalities, the cone logic and rigidity | `INDEPENDENT_VERIFICATION.md`: correct |

The check scripts use paths relative to their own folder, so run each one from the folder it is in (Python 3 with `numpy`,
`scipy` and `mpmath`). `common/` holds a small helper module shared by several checks (`fcore.py`: the harmonic function
h_λ and related routines) and two stored test configurations; `reduction-chain/spot/` is the copy of the certificate code
and of one of its outputs that the re-verification worked on.

Internal labels used in these documents:
- `Q_2bmv` = `strip-inequality/`
- `Q_RI` = `radon-identity/`
- `Q_r1` = `rank-one-alternative/`
- `Q_rig` = `rigidity/`
- `QD2` = `../cone-certificates/`
- `Q_2bmv_check/REFEREE.md`, `Q_RI_check/REPORT.md`, `Q_chain_check/REPORT.md` = the re-verification reports
  `INDEPENDENT_VERIFICATION.md` in `strip-inequality/`, `radon-identity/` and `reduction-chain/`

Labels such as `Q-L9`, `QD2-L1` and `QD-L7` refer to lemmas of the working notes (`SHARED_LEMMAS`, not included here);
every one used in the final argument is stated and proved in the mathematical paper. The Lean formalisation (`../lean/`) checks the whole chain, as described in
the main README.
