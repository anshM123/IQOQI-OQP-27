# arXiv submission metadata

## Title
Optimal CGLMP measurements in every dimension and the clauses of IQOQI Vienna Open Quantum Problem 27B

## Authors
Ansh Mishra, Aryan Senthilkumar

(Affiliations appear in the PDF only: Independent researcher, Cumming, GA, USA; Independent researcher, Johns Creek, GA, USA.
Corresponding author: Ansh Mishra, ansh.mishra2025@gmail.com.)

## Abstract (plain text, 1908 characters; arXiv limit 1920)

Open Quantum Problem 27 of IQOQI Vienna, "The power of CGLMP inequalities", asks (A) whether every nontrivial facet of the local polytope with two settings and $d$ outcomes per party is of CGLMP type, and (B) to show that the Fourier-type measurements of Durt, Kaszlikowski and Żukowski (DKZ) are necessarily optimal for the CGLMP inequality on a maximally entangled state, and that they also give the highest resistance of the violation to noise and the best Kullback-Leibler discrimination. Part A was answered negatively by Bancal, Gisin and Pironio in 2010. We prove the first clause of Part B and partly answer the other two. (i) For every $d$, every local dimension and all projective measurements on maximally entangled states, the CGLMP value is at most the DKZ value, and DKZ is the only maximizer up to local unitaries and an inert ancilla. The proof combines an exact reduction to a clock model, a new strip inequality for a projection and a Hermitian matrix, obtained from a two-variable Bessis-Moussa-Villani theorem with an explicit density, and a cone condition on Clausen kernels certified in interval arithmetic for every $d$; it is formalised in Lean 4, completely for $d \le 20$ and, for $d \ge 21$, up to the certified cone condition. (ii) The noise clause holds for every $d$ for the violation of the CGLMP inequality under white noise, with DKZ the unique optimum. For the violation of any Bell inequality under uniformly random outcomes, it fails for every $d \ge 4$ once measurements may have outcomes that never occur, by coarse-grained CHSH-type measurements whose critical visibility we compute exactly; for complete von Neumann measurements it remains open for $d \ge 4$. (iii) The Kullback-Leibler clause fails for every $d \ge 4$: explicit orthonormal-basis measurements reach a statistical strength of at least 0.0703 bits, DKZ at most 0.0688 bits; for $d = 3$ it remains open.

## Categories
- Primary: **quant-ph**
- Cross-lists: **math-ph**, **math.FA**

Justification. The question and its answer concern Bell nonlocality and optimal quantum measurements (quant-ph); rigorous
results on Bell inequalities with complete proofs fit math-ph. The new mathematics of the paper is analytic: a strip
inequality for a projection and a Hermitian matrix with an exact defect formula, a two-variable positivity theorem of
Bessis-Moussa-Villani (Stahl) type with an explicit density for matrix pencils, and a noncommutative continuum theorem for
conjugate functions (periodic Hilbert transforms) of operator-valued step fields. These are matrix/operator inequalities
and Laplace- and Hilbert-transform positivity results (MSC 47A63, 15A42, 44A10, 42A50), which is math.FA. math.OA
(C*- and von Neumann algebras) is less apt: no operator-algebraic structure is used beyond finite matrices, a normalised
trace and a tracial moment relaxation.

## Comments
23 pages, 1 figure, 4 tables; code, certificates, re-verification reports and Lean 4 formalisations: https://github.com/anshM123/IQOQI-OQP-27

## Optional fields
- MSC classes: 81P40 (Primary); 15A42, 47A63, 42A50, 44A10, 65G40 (Secondary)
- Report number / journal reference / DOI: none
- License: authors' choice (the code and data repository is under the MIT license)

## Files to upload
`arxiv_source.zip` (contains `main.tex` and `figures/fig2.pdf` only). Single LaTeX file with an inline
`thebibliography` (no BibTeX run needed); intended for arXiv's default pdflatex.
