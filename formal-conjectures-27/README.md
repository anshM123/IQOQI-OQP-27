# OQP 27B in Lean, in the formulation of Formal Conjectures issue #3444

`27.lean` is a single Lean 4 file, `FormalConjectures/OpenQuantumProblems/27.lean`, written for the
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository. It states Part B
of IQOQI Vienna Open Quantum Problem 27 from scratch, in the formulation of
[issue #3444](https://github.com/google-deepmind/formal-conjectures/issues/3444), and proves its main statement. It builds
inside that repository with the repository's own Lake configuration, Mathlib and continuous-integration flag `--wfail`,
and imports only `FormalConjecturesUtil` (Mathlib and the repository's attributes).

The file is not a contribution to formal-conjectures: that repository's guidelines do not accept long proofs (this one has
about 35,000 lines). It is provided so that the statement can be checked against the repository's conventions and the
proof can be built with its toolchain.

## What to check

[`STATEMENT_FOR_REVIEW.md`](STATEMENT_FOR_REVIEW.md) collects everything a reviewer needs to validate the statement: the
definitions of Part 0 and the full statements of the main results, copied verbatim from `27.lean`. The proofs (Parts
1–86) are checked by Lean and need not be read to validate the statement.

**Part 0, the problem** (Mathlib only, written from scratch):
- behaviours p(a,b|x,y), deterministic strategies and the local polytope;
- the CGLMP functional of the problem page, E[m(A₁−B₁)] + E[m(B₁−A₂)] + E[m(A₂−B₂)] + E[m(B₂−A₁−1)] with m(t) = t mod d,
  whose local bound is d − 1 (smaller values are violations);
- the maximally entangled state Φ_d of C^d ⊗ C^d, density matrices and the Born rule p = Tr[ρ (A ⊗ B)];
- complete von Neumann measurements: rank-one projections U|a⟩⟨a|U† for a unitary U;
- the DKZ measurements: the computational basis transformed by the discrete Fourier transform and diagonal phases;
- white noise: ρ_v = v |Φ_d⟩⟨Φ_d| + (1 − v) 1/d².

**Checks of the definitions** (special cases and a related question):
- every local model satisfies the CGLMP inequality, and the bound d − 1 is attained;
- measuring Φ_d in the computational basis gives exactly d − 1 (no violation);
- the Born rule on Φ_D equals Tr(AᵀB)/D;
- complete von Neumann measurements are projective with rank-one outcomes, and the DKZ bases are orthonormal;
- the local unitaries that fix Φ_d are exactly the u ⊗ ū used in the uniqueness statement;
- the CGLMP expression I_d of Collins et al. equals 4 − 2F(p′)/(d − 1), where F is the functional of the problem page and
  p′ is p with the two inputs exchanged;
- d = 2: the bound is Tsirelson's bound, CHSH ≤ 2√2, attained by DKZ;
- a counterexample to a related question: for d = 3 a non-maximally entangled state with the DKZ measurements gives a
  larger violation than any complete von Neumann measurements on Φ_3 (Acín, Durt, Gisin and Latorre 2002), so the
  restriction to Φ_d in the problem matters.

**Part 87, the bridge and the results.** Part 87 proves that the definitions of Part 0 reduce to the internal model of
the proof (Parts 1–86, assembled from [`../lean/`](../lean/)), and states:

| Theorem (namespace `OpenQuantumProblem27`) | Statement | Hypotheses |
|---|---|---|
| `dkz_optimal_of_le_twenty` | 2 ≤ d ≤ 20: no complete von Neumann measurements on Φ_d give a smaller CGLMP functional than DKZ | none |
| `dkz_unique_of_le_twenty` | 2 ≤ d ≤ 20: the optimal ones are exactly those that a local unitary u ⊗ ū maps to DKZ | none |
| `dkz_noise_of_le_twenty` | 2 ≤ d ≤ 20: noise clause for white noise on Φ_d and the violation of the CGLMP inequality, with uniqueness | none |
| `dkz_optimal`, `dkz_unique`, `dkz_noise` | the same for every d ≥ 2 | `Hyp_ConeCertPos_large` |
| `dkz_optimal_any_dim_of_le_twenty`, `dkz_unique_any_dim_of_le_twenty` | 2 ≤ d ≤ 20: all d-outcome projective measurements of any ranks on Φ_D, every local dimension D | none |
| `strip_inequality`, `strip_equality` | the matrix inequality behind the proof, and its equality case, for every matrix size | none |

## The hypothesis for d ≥ 21

`Hyp_ConeCertPos_large` (∀ d ≥ 21, `ConeCertPos d`) is the cone condition CONE_d. For 2 ≤ d ≤ 20 it is proved in the file
(`coneCertPos_le_twenty`) from explicit certificates that the Lean kernel evaluates (`decide +kernel`). For d ≥ 21 it is
established outside Lean by interval-arithmetic certificates ([`../cone-certificates/`](../cone-certificates/),
`python audit_alld.py`), so the theorems for every d take it as an explicit hypothesis. It is not an axiom.

Not formalised here: Part A, the Kullback–Leibler clause, the noise clause for all Bell inequalities, and measurements that
are not projective.

## Build

```bash
git clone https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures
git checkout df3f12d7
lake exe cache get
cp <this folder>/27.lean FormalConjectures/OpenQuantumProblems/27.lean
lake --wfail build 'FormalConjectures.OpenQuantumProblems.«27»'
```

SHA-256 of `27.lean`: `a67878c530a1aab9680c78225f094bb5a5a94ae2f04345af070f5dd1716f89d5`.

Our build of this file ([`build.log`](build.log)): exit 0, no warnings. It took about 50 minutes and up to about 12 GB of
memory (committed; peak resident 7–9 GB in our runs) on one machine; the kernel-checked certificates for d ≤ 20 dominate
both. The file sets `Elab.async false` and removes the heartbeat limit (`maxHeartbeats 0`) only for the certificate
theorems, which keeps the memory bounded.

Axioms: with `Axioms27.lean` placed at the root of the formal-conjectures checkout,

```bash
lake env lean Axioms27.lean
```

prints, for every listed theorem, `[propext, Classical.choice, Quot.sound]` ([`print_axioms.txt`](print_axioms.txt)).
The file contains no `sorry`, `admit`, `axiom` declaration or `native_decide`.

## How the file is made

[`generator/gen27.py`](generator/gen27.py) assembles `27.lean` from the Lean sources in [`../lean/`](../lean/) (the
modules `OQP27/*` and `CGLMPRigidity/*` that the main theorems need, in dependency order) and five pieces written for this
file: `fc27_head.lean` (header and module docstring), `fc27_problem.lean` (Part 0), `fc27_checks.lean` (checks of Part 0),
`fc27_adgl.lean` (the d = 3 example) and `fc27_tail.lean` (Part 87). It renames the namespace, tags every declaration with
the repository's attributes and applies two small source patches needed under full Mathlib (documented in the script).
`python generator/gen27.py` writes `generator/27.out.lean`, which is byte-for-byte equal to `27.lean`.
