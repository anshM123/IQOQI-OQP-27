# Lean 4 formalisation of OQP 27B (maximally entangled clause, every d)

This folder is a Lean 4 project (Lean v4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`). It contains a formal
proof of the maximally entangled clause of OQP 27B, stated in the internal model of the proof (see "The statement" below):
98 files in `OQP27/` (33,424 lines), plus three files of algebraic rigidity in `CGLMPRigidity/` (898 lines, from our
earlier repository [CGLMP](https://github.com/anshM123/CGLMP)). The statement in the formulation of Formal Conjectures
issue #3444 (the state Φ_d, complete von Neumann measurements, the CGLMP functional of the problem page), with a
Lean-checked reduction to this model, is in [`../formal-conjectures-27/`](../formal-conjectures-27/).

## What is proved

| Lean theorem (file `OQP27/Main.lean` unless noted) | Statement | Hypotheses |
|---|---|---|
| `OQP27.maxEntClause_le_twenty` | for every 2 ≤ d ≤ 20: optimality and rigidity of DKZ (Theorems 1 and 2), and DKZ attains I_ME(d) | **none** |
| `OQP27.maxEntClause_all` | Theorems 1 and 2 for every d ≥ 2 | `Hyp_ConeCertPos_large` (CONE_d for d ≥ 21) |
| `OQP27.stripInequality`, `OQP27.stripEquality` | the strip inequality (Theorem 3) for every matrix size M, and its equality case | **none** |
| `OQP27.StripL3b.theorem1_bmv2` (`StripRIMain.lean`) | the two-variable BMV theorem with explicit density (Theorem 4), for all complex (a, t) | **none** |
| `OQP27.StripL3b.hyp_RI` | the Radon identity | **none** |
| `OQP27.Red.hyp_reduction` | the exact reduction: strategy → clock model → projection configuration → linear form | **none** |
| `OQP27.Cell.continuumCell` | the continuum theorem: Theorem 3 implies every cell inequality | **none** |
| `OQP27.ClassB.classicalTheoremB_all` | the classical (commuting) theorem for every d | **none** |
| `OQP27.coneCertPos_le_twenty` | CONE_d for 2 ≤ d ≤ 20, from explicit certificates evaluated by the Lean kernel | **none** |
| `OQP27.ConeCertificate.fullCheck_sound` (`CertPipeline.lean`) | soundness of the certificate checker: a certificate that passes the check proves CONE_d | **none** |
| `OQP27.dkz_cglmp` | the DKZ strategy attains I_ME(d), for every d | **none** |
| `OQP27.cglmpOf_noisy`, `OQP27.noisy_violation_iff` (`CglmpNoise.lean`) | uniform noise at visibility v multiplies the CGLMP value by v; a strategy's CGLMP noise threshold is 2/I_d | **none** |
| `OQP27.noisy_violation_imp_le_twenty`, `OQP27.noisy_violation_imp` | no strategy has a lower CGLMP noise threshold than DKZ (2/I_ME(d)) | none for d <= 20; `Hyp_ConeCertPos_large` for d >= 21 |

`#print axioms` of each of these gives `[propext, Classical.choice, Quot.sound]`, Lean's three standard axioms
(`OQP27/logs/fullbuild/MainAxioms.log`; in total 265 theorems are audited in the eight `*Axioms.lean` files, all with
this result). The code of every
file is free of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` and `opaque`
(`python scan_forbidden.py`). The certificates are checked with `decide +kernel`, so the Lean kernel itself evaluates them
in exact rational arithmetic; the compiler is not trusted.

**In words:** for 2 ≤ d ≤ 20 the theorems above are proved in Lean with no hypotheses. For d ≥ 21 the
formal proof is complete except for one named input, the cone condition CONE_d, which is established outside Lean by the
interval-arithmetic certificates in [`../cone-certificates/`](../cone-certificates/).

## The statement

This is the internal model of the proof, not the textbook formulation of the problem: strategies may use any local
dimension D and projections of any rank, the Born rule on Φ_D is used in the closed form Tr(Aᵀ B)/D, and
`Strategy.cglmp` is the CGLMP expression I_d of Collins et al. (local bound 2) rather than the functional of the problem
page. The reduction from the problem-page formulation to this model (the Born rule on Φ_d, complete von Neumann
measurements, the exchange of the two inputs and the identity I_d(p) = 4 − 2F(p′)/(d − 1)) is proved in
`../formal-conjectures-27/27.lean`, Part 87.

From `OQP27/Statement.lean` (concrete matrices over ℂ; `Strategy d D` is a pair of d-outcome projective measurements for
each party on ℂ^D, and the probabilities are those of the maximally entangled state, p(a,b|x,y) = Tr(A_{x,a}^T B_{y,b})/D):

```lean
/-- `I_ME(d) = 4/(d(d-1)) ∑_{j=1}^{d-1} (d - j) sec(π j/(2d))` -/
noncomputable def IME (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) * ∑ j ∈ Ico 1 d, ((d : ℝ) - j) / Real.cos (π * j / (2 * d))

def OptimalityStatement (d : ℕ) : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, S.cglmp ≤ IME d

def RigidityStatement (d : ℕ) : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, S.cglmp = IME d → S.IsDKZTensorId

def MaxEntClause (d : ℕ) : Prop := OptimalityStatement d ∧ RigidityStatement d
```

`Strategy.cglmp` is the CGLMP expression I_d written out term by term, and `IsDKZTensorId` says that d divides D and that a
local unitary u ⊗ ū maps the strategy to DKZ ⊗ 1. The file also proves that these definitions are not vacuous: the DKZ
strategy is a `Strategy d d`, it attains `IME d`, and it satisfies `IsDKZTensorId`.

The main theorems:

```lean
theorem maxEntClause_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d

theorem maxEntClause_all (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d
```

## How the proof is organised

The formalisation follows the layers of the argument:

| Layer | Files | Main results |
|---|---|---|
| statement (internal model) | `Statement.lean` | the definitions above, non-vacuity |
| reduction to CONE + (*) | `Skeleton.lean`, `Reduction*.lean` | strategy → clock model → configuration of 4d projections → linear form ⟨v, δ⟩; the logical chain from (*), the cell inequalities and CONE_d to Theorems 1 and 2 |
| (*) for every M | `Strip*.lean` | the Radon identity (complex Burgers argument), the two-variable BMV theorem, the strip inequality with exact defect |
| equality case of (*) | `StripTheorem2.lean`, `StripSkeleton.lean`, `StripRIChain.lean` | equality at one λ forces B and g to commute |
| cell inequalities | `Cell*.lean` | continuum theorem for step fields (explicit Herglotz functions), all cell inequalities |
| uniqueness chain | `Rigidity*.lean`, `Classical*.lean`, `../CGLMPRigidity/` | tightness → residue lemma → all projections commute → classical Theorem B → DKZ ⊗ 1 |
| certificates | `Cert*.lean`, `certdata/` | Clausen enclosures in exact rational interval arithmetic, the checker and its soundness theorem, kernel-checked certificates for d ≤ 20 |
| assembly | `Main.lean`, `MainAxioms.lean` | the main theorems and their axiom audit |

The reports `OQP27/STATUS_L1.md` … `STATUS_L7.md` list every theorem of each module with its paper statement. Module labels:
L1 statement and skeleton, L2 reduction, L3a/L3b strip inequality, L4 certificates, L5 cell inequalities, L6 rigidity,
L7 classical theorem. Conventions are in `OQP27/LEAN_BRIEF.md`.

## What is not formalised

- **CONE_d for d ≥ 21.** It enters as the hypothesis `Hyp_ConeCertPos_large`, a precise Lean statement (for every d ≥ 21,
  the vector v is a finite nonnegative combination of cell vectors in which some cell vector with all cells positive has a
  positive weight). It is established
  by the certificates in `../cone-certificates/` (`python audit_alld.py` prints `ALL-D CERTIFIED (every d >= 2)`).
- The rigidity statement checked in Lean is "d divides D, and a local unitary u ⊗ ū maps the strategy to DKZ ⊗ 1".
  Uniqueness of u (up to 1 ⊗ u′) and the strict inequality when d does not divide D are proved in the papers.
- Facts used only in remarks (continuity of the density F, the sum rule ∫F ds = ‖BgP‖², the dilogarithm formula for h_λ)
  are not needed: in Lean, h_λ is defined as a Poisson integral and F only needs to be measurable.

## How to check

You need [elan](https://github.com/leanprover/elan) (it installs the Lean version in `lean-toolchain`), Python 3 for the scan,
and about 10 GB of free memory.

```bash
lake exe cache get    # prebuilt Mathlib for the pinned revision
bash check.sh         # every file, in dependency order, then the forbidden-token scan and the axiom audit
```

`check.sh` checks the three `CGLMPRigidity` files and then the 98 files of `OQP27/BUILD_ORDER.txt`, one Lean process at a
time, and ends with `OK: all 265 audited theorems (files *Axioms.lean) use only propext, Classical.choice, Quot.sound`.
It takes about two hours on a laptop (our clean rebuild: 1.7 hours of Lean time); the certificate files `CertD18`–`CertD20`
need up to about 8 GB of memory each, and `CertLP` about 45 minutes. `lake build` also works, but it runs files in parallel
and therefore needs more memory.

## Logs

- `OQP27/logs/fullbuild/`: a clean rebuild of the first 96 files in dependency order on 2026-10-02. `SUMMARY.log` lists
  the exit code and time of every file; the first attempt at `CertD20` ran out of memory while other programs were
  running, and the rebuild was resumed from `CertD20` with nothing else running.
- The two files added afterwards, `CglmpNoise.lean` and `CglmpNoiseAxioms.lean`, were built on top of that rebuild
  (`OQP27/logs/CglmpNoise.log`, `OQP27/logs/CglmpNoiseAxioms.log`).
- `OQP27/logs/<File>.log`: the build logs of each file from development; `OQP27/logs/*Axioms.log`, `L1_axioms.log`,
  `L5_axioms.log`: the axiom audits.
- `OQP27/logs/*.py`: numerical checks of the Lean definitions (not part of any proof).

## References inside the Lean comments

Comments in the Lean files cite the working documents under their development paths. In this repository they are:

| Path in comments | In this repository |
|---|---|
| `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md` | [`proofs/strip-inequality/PROOF.md`](../proofs/strip-inequality/PROOF.md) |
| `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md` | [`proofs/radon-identity/PROOF.md`](../proofs/radon-identity/PROOF.md) |
| `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md` | [`proofs/rigidity/RIGIDITY.md`](../proofs/rigidity/RIGIDITY.md) |
| `iqoqi/programs/oqp27B_all/QD2/` (e.g. `LOG.md`, `certs/`, `cells.py`) | [`cone-certificates/`](../cone-certificates/) (`LOG.md` is `RESEARCH_LOG.md`) |
| `iqoqi/programs/oqp27B_all/SHARED_LEMMAS.md` | working notes, not included; the lemmas used are proved in [`papers/math`](../papers/math/main.pdf) |
| `publish/CGLMP/...` | the repository [github.com/anshM123/CGLMP](https://github.com/anshM123/CGLMP) |
| `formal-conjectures/` | this folder (the Lean project root) |
