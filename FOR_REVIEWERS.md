# For reviewers

This page is for experts who check our work on Part B of IQOQI Vienna Open Quantum Problem 27. It lists exactly what we
claim, how each claim is established, where to check it, and what is not covered. None of these results has yet been
reviewed by outside experts; the re-verification reports in `proofs/` and `clauses/` are internal checks.

## What we claim

| # | Claim | How it is established |
|---|---|---|
| 1 | **Optimality (27B, first clause).** For every d ≥ 2, every local dimension D and all projective measurements on Φ_D, the CGLMP value satisfies I_d ≤ I_ME(d), and the DKZ measurements attain it. | Proof in `papers/math` (Theorem A). Lean: no hypotheses for d ≤ 20; for d ≥ 21 assuming the cone condition CONE_d, which is certified outside Lean (claim 5). |
| 2 | **Uniqueness.** Equality holds if and only if d divides D and, up to a local unitary u ⊗ ū, the strategy is DKZ ⊗ 1. For D = d this says that the optimal complete von Neumann measurements on Φ_d are exactly the images of DKZ under u ⊗ ū. | `papers/math` (Theorem B). Lean as for claim 1; the uniqueness of u and the strict inequality for d ∤ D are proved on paper only. |
| 3 | **Strip inequality and two-variable BMV positivity** (Theorems C and D), for matrices of every size. | `papers/math`, Section 3, and a second, distribution-free proof in Appendix B. Lean: complete, no hypotheses. |
| 4 | **Noise clause, CGLMP violation.** Under white noise on Φ_d (equivalently, uniformly random outcomes), the DKZ measurements have the lowest critical visibility for violating CGLMP, and they are the only measurements that reach it. | A corollary of claims 1–2 (`papers/math`, Corollary in Section 9). Lean as for claim 1. |
| 5 | **The cone condition CONE_d for every d** (Theorem E). | Computer-assisted: rational certificates checked in interval arithmetic for d ≤ 200, one certificate per d for 201 ≤ d ≤ 2000, and a uniform interval Taylor-model argument with certified error terms for d ≥ 2001. Lean re-checks the certificates for d ≤ 20 in the kernel. |
| 6 | **Noise clause, violation of local realism** (all Bell inequalities). True for d = 2 and d = 3 on Φ_d. For every d ≥ 4 it fails once measurements may have outcomes that never occur (zero projectors), or are POVMs: explicit strategies on Φ_d have a lower critical visibility than DKZ. **For complete von Neumann measurements on Φ_d it is open for d ≥ 4.** | `clauses/noise-literal/THEOREM.md` (computer-assisted for 4 ≤ d ≤ 9, exact certificates). Not in Lean. |
| 7 | **Kullback–Leibler clause.** False for every d ≥ 4: explicit complete von Neumann measurements on Φ_d have a larger statistical strength than DKZ (all three strengths of van Dam, Grünwald and Gill). **Open for d = 3**, where DKZ is a strict local maximum. | `clauses/kl-divergence/THEOREM.md` (computer-assisted, rigorous enclosures). d = 4 was found first by Y. Zhang. Not in Lean. |
| 8 | **POVMs for 3 ≤ d ≤ 8.** Claims 1 and 2 hold for arbitrary POVMs on maximally entangled states of every local dimension. | Exact sum-of-squares certificates, `clauses/povm/`. Not in Lean. Open for d ≥ 9. |

Part A of the problem was answered negatively by Bancal, Gisin and Pironio (2010); we claim nothing there.

## Suggested order of checking

1. **The statement.** [`formal-conjectures-27/STATEMENT_FOR_REVIEW.md`](formal-conjectures-27/STATEMENT_FOR_REVIEW.md)
   gives the Lean definitions and statements in the formulation of Formal Conjectures issue #3444 (the state Φ_d,
   complete von Neumann measurements, the Born rule, the CGLMP functional of the problem page), copied verbatim from the
   Lean file. Points that deserve attention: the conventions of the CGLMP functional (tied to the expression I_d of
   Collins et al. by a proved identity, and checked on local models and on the computational basis), the DKZ phases
   α = (1/2, 0) and β = (−1/4, 1/4) in the orientation of the problem page, and the uniqueness condition (an "if and only
   if" with the local unitaries u ⊗ ū, which are proved to be exactly those that fix Φ_d).
2. **The proof of claims 1–3.** [`papers/math/main.pdf`](papers/math/main.pdf). The reduction to the clock model
   (Section 2) is from our earlier work and is formalised in Lean. The new steps are the strip inequality and the
   two-variable BMV positivity (Section 3, and Appendix B for the distribution-free route that Lean follows), the
   noncommutative continuum theorem (Section 4), the cell embeddings (Section 5), the logic of the cone condition
   (Section 6) and rigidity (Section 7).
3. **The computer-assisted step.** [`cone-certificates/README.md`](cone-certificates/README.md), `CONE_PROOF.md` and
   `CONE_ALLD_PROOF.md`. The regime d ≥ 2001 is the least standard part: an analytic argument whose estimates are
   evaluated with interval Taylor models.
4. **The other clauses.** [`clauses/LEDGER.md`](clauses/LEDGER.md) quotes the problem and gives the status of each
   clause; each folder of `clauses/` has a `THEOREM.md` with statement, proof and verifier.

## Reproducing

| What | Command | Time and memory (our runs) |
|---|---|---|
| Lean, single file in the issue-#3444 formulation | see [`formal-conjectures-27/README.md`](formal-conjectures-27/README.md) | about 50 min, up to about 12 GB |
| Lean, full development | `cd lean && lake exe cache get && bash check.sh` | about 2 h, up to about 8 GB per file |
| CONE_d audit, every d | `cd cone-certificates && python audit_alld.py` | a consistency audit: it re-checks the stored certified bounds against every condition of the proof, and the coverage of all d, but does not recompute the bounds; re-running the 201 ≤ d ≤ 2000 certifier takes about 12 CPU-hours |
| Noise clause, local realism | `cd clauses/noise-literal && python verify_theorem.py` | about 3 min |
| Kullback–Leibler clause | `cd clauses/kl-divergence && python verify_main.py` | see `THEOREM.md` |
| POVMs, 3 ≤ d ≤ 8 | `cd clauses/povm/certs && python ../verify_povm.py 3 4 5 6 7 8` | exact arithmetic |

Python 3 with numpy, scipy, sympy and mpmath; run each script from its own folder with `OMP_NUM_THREADS=1`.

## Known limitations

- CONE_d for d ≥ 21 is not checked by the Lean kernel; the Lean theorems for every d take it as an explicit hypothesis.
- General POVMs are covered only for 3 ≤ d ≤ 8.
- The uniqueness of u (up to 1 ⊗ u′) and the strict inequality for d ∤ D in claim 2 are proved on paper, not in Lean.
- The counterexample in claim 6 needs unused outcomes or POVMs; it says nothing about complete von Neumann measurements.
- The maximum of I_d over all states (not only maximally entangled ones) is known exactly only for d ≤ 8; for d = 3 a
  non-maximally entangled state does better than Φ_3 (Acín, Durt, Gisin and Latorre 2002; proved in the Lean file).
