# Lean formalisation of OQP 27B (maximally entangled clause, every d): architecture and conventions

## Environment
- Lean v4.33.1 and Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474 (`lean-toolchain`, `lake-manifest.json`).
- Namespace `OQP27`.  Every file is checked separately with
    lake env lean OQP27/<File>.lean -o .lake/build/lib/lean/OQP27/<File>.olean -i .lake/build/lib/lean/OQP27/<File>.ilean
  in the order of `OQP27/BUILD_ORDER.txt`, so that later files can `import OQP27.<File>` (`check.sh` does this for all files).
  During development the wrapper `OQP27/leanrun.sh` was used; it limits the number of concurrent Lean processes and waits
  for 5 GB of free memory.
- Specific Mathlib modules are imported rather than `import Mathlib`, to keep elaboration fast.

## Rules for finished files
- No `sorry`, `admit`, `axiom` or `native_decide`.  `#print axioms` of every main theorem shows only
  [propext, Classical.choice, Quot.sound] (the files `*Axioms.lean` and their logs).
- A result proved on paper but not (yet) formalised may enter only as an explicit hypothesis: a `Prop`-valued `def` passed
  as an argument to a theorem, named `Hyp_...`, stating a precise mathematical statement (never a `True` placeholder), with a
  reference to the paper proof.  In the final state the only such hypotheses used by the main theorems are
  `Hyp_ConeCert_large` / `Hyp_ConeCertPos_large` (CONE_d for d >= 21).
- Each file starts with a header comment: what is proved, which hypotheses remain, and where the paper proof is.
- Each module has a report `OQP27/STATUS_<module>.md`: a table of Lean name, paper statement and status (PROVED or
  HYPOTHESIS), and the build log.  Build logs are in `OQP27/logs/<File>.log`.

## Modules
- L1 `Statement.lean`, `Skeleton.lean`: the statement of the theorem in the internal model of the proof (concrete matrices over C, projective measurements,
  the max-ent probabilities p(a,b|x,y) = Tr(A_{x,a}^T B_{y,b})/D, the CGLMP functional exactly as in the classical all-d
  paper of the CGLMP repository, I_ME(d)), the rigidity statement, and the logical chain from named hypotheses (strip
  inequality, continuum theorem / cell inequalities, CONE_d) to the main theorems.
- L2 `Reduction*.lean`: strategy -> clock model -> Q-configuration -> linear form, and the equivalence of F <= F_DKZ with
  I_d <= I_ME(d).  Reuses `CGLMPRigidity/*.lean`.
- L3a `Strip*.lean` (kernel part): the strip Poisson kernel K_X, its Laplace transform, h_lam as a Poisson integral, and the
  strip inequality (*) with exact defect and its equality case, from the two-variable BMV theorem.
- L3b `Strip*.lean` (pencil part): pencil facts, the Jensen-type identity, the slice identity, the Radon identity (proved by
  the elementary complex-Burgers argument, `proofs/radon-identity/PROOF.md`) and the two-variable BMV theorem.
- L4 `Cert*.lean`: the Lean statement of CONE_d, a certificate format, the soundness theorem "valid certificate => CONE_d",
  the Clausen function with rigorous enclosures, and kernel-checked certificates for 2 <= d <= 20.
- L5 `Cell*.lean`: the continuum theorem for step fields and the cell-embedding inequalities, from the strip inequality.
- L6 `Rigidity*.lean`: the equality chain (residue lemma, commuting configuration => DKZ, using `CGLMPRigidity`).
- L7 `Classical*.lean`: the classical (commuting) Theorem B for every d.
- `Main.lean` discharges the hypotheses of the skeleton with the theorems of the other modules; `MainAxioms.lean` audits it.

## Shared conventions
- Matrices: `Matrix (Fin M) (Fin M) ℂ`; projection: `B.IsHermitian ∧ B * B = B`; Hermitian: `Matrix.IsHermitian`.
- Eigenvalues of a non-Hermitian matrix X: the multiset `(Matrix.charpoly X).roots` over ℂ.
- Positive part of a Hermitian matrix's spectrum: `∑ i, max (hA.eigenvalues i) 0`.
- The strip: `0 ≤ re ≤ 1`. h_lam on the closed strip: (y - lam)_+ at re = 0, 0 at re = 1, and the Poisson integral inside.
