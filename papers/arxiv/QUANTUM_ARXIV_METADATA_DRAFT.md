# Quantum / arXiv submission metadata — DRAFT (co-author approval required)

## Title
Optimal CGLMP measurements in every dimension and the clauses of IQOQI Vienna Open Quantum Problem 27B

## Authors
Ansh Mishra; Aryan Senthilkumar

## Primary category
quant-ph

## Cross-lists (optional)
math-ph; math.FA

## Abstract
We investigate the Fourier-type Durt–Kaszlikowski–Żukowski (DKZ) measurements for the CGLMP inequalities on maximally entangled states, addressing Part B of IQOQI Vienna Open Quantum Problem 27. For every outcome number and local dimension, we obtain the DKZ projective-measurement bound and characterize equality up to local unitaries and an inert ancillary factor. The proof uses a new matrix strip inequality, a two-variable Bessis–Moussa–Villani positivity formula, and a cone condition certified by interval arithmetic. The argument is formalized in Lean 4 without additional hypotheses for dimensions at most 20; the higher-dimensional Lean theorems assume the cone condition, established separately by computer-assisted certificates. We also study noise resistance and Kullback–Leibler discrimination. For white-noise resistance against the CGLMP inequality, DKZ is optimal in all dimensions. For resistance to any Bell inequality under complete von Neumann measurements, the claim holds for dimensions at most four, with the four-outcome case proved by exact computer-assisted enumeration, and remains open in higher dimensions. The KL-optimality clause fails in dimensions four and above. A concurrent preprint by Turturean and Bao proves overlapping projective optimality and rigidity statements by a different method.

## Comments
Source, certificates, checkers, and Lean files: https://github.com/anshM123/IQOQI-OQP-27

## DOI / journal reference
Leave blank for the new arXiv preprint unless the authors have a manuscript-specific DOI appropriate to list.

## Outstanding actions
- Both authors confirm statements and individual contributions.
- Both authors confirm full disclosure of any AI-assisted code, calculations, proofs, bibliographic work, figures, and writing.
- Both authors review the d=4 noise result and its precise scope.
- Independently check technical claims and the cone certificates; no external expert validation is implied by this draft.
- Compile the revised main source, including the existing figures/fig2.pdf, and visually inspect the resulting PDF.
- Submit on arXiv under quant-ph; a Zenodo record is not accepted as an arXiv substitute by Quantum.
