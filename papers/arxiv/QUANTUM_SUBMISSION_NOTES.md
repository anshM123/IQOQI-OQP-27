# OQP27 → Quantum: editorial changes and submission checklist

This is a review draft, **not a finalized submission**. The original main.tex is unchanged on the default branch. The revised full source is in `papers/arxiv/quantum_revised.tex` on branch `quantum-submission-review-2026-11-16`.

## Changes made to the existing manuscript
1. Added a citation to the October 2026 Turturean–Bao preprint, describing overlapping optimality/rigidity claims without making unsupported priority claims.
2. Added a brief literature-overlap discussion near the start of the introduction and a comparison before the back matter.
3. Reconciled the status of complete von Neumann noise robustness: proven for d = 2, 3, 4; the d = 4 proof is computer-assisted and not externally refereed; open for d ≥ 5.
4. Updated abstract, result summary, status table, noise discussion, and open-problem table to reflect the d = 4 result.
5. Added an author-contribution / AI-tool disclosure section, **explicitly marked for author approval**. No individual research contributions or earlier AI tools were invented.

## Important remaining steps
- The source ZIP `papers/arxiv/arxiv_source.zip` on the original branch has the existing figure. To make a complete package, replace its main.tex with quantum_revised.tex (renamed to main.tex), retaining figures/fig2.pdf.
- Recompile in pdflatex and proofread every page, particularly tables and citations.
- Review every new statement scientifically; all proof claims remain the responsibility of the authors.
- Co-authors must finalize the author contributions and the actual complete AI-use disclosure.
- The original repository's `FOR_REVIEWERS.md` and certificate scripts are useful supporting resources, but the d ≥ 21 cone condition is outside Lean.
- Upload the final package to arXiv in quant-ph first. Quantum accepts only an arXiv identifier, not a Zenodo DOI.
- Then submit via https://quantum-journal.scholasticahq.com/ .

## Author approval checklist
- [ ] Scientific claims checked
- [ ] Literature citation and priority wording approved
- [ ] Contributions specified for both authors
- [ ] AI-use details factually complete and approved
- [ ] Revised manuscript compiled with figure
- [ ] arXiv metadata approved
