/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Open Quantum Problem 27: The power of CGLMP inequalities

## Mathematical problem
Problem 27 of the IQOQI Vienna list (proposed by R. Gill, 2006) concerns the Bell scenario with two
parties, two inputs per party and $d$ outputs. Part A asks to show that every face of the local
polytope that is not contained in a face of the no-signalling polytope is of CGLMP type; this is
false (Bancal, Gisin and Pironio, 2010). Part B asks to show that the observables that maximally
violate the CGLMP inequality on a maximally entangled state are necessarily the measurements found
numerically by Durt, Kaszlikowski and Zukowski (DKZ): measurements in the computational basis,
transformed only by the discrete Fourier transform and diagonal unitaries. It also asks to show that
these measurements give the highest resistance of the violation to noise, and the best
discrimination against local realism in the Kullback-Leibler sense.

## What this file formalizes
Part B in the formulation of Formal Conjectures issue #3444: the maximally entangled state $\Phi_d$
of $\mathbb{C}^d \otimes \mathbb{C}^d$ is fixed, and the CGLMP functional is optimized over complete
von Neumann $d$-outcome measurements. All definitions are in Part 0, written from scratch with
Mathlib only:
- `Behaviour d`, `deterministicBehaviour`, `IsLocalBehaviour`: behaviours $p(a,b \mid x,y)$ and the
  local polytope;
- `cglmpFunctional`: the CGLMP functional of the OQP page,
  $E[m(A_1 - B_1)] + E[m(B_1 - A_2)] + E[m(A_2 - B_2)] + E[m(B_2 - A_1 - 1)]$ with
  $m(t) = t \bmod d$; local models give at least $d - 1$, smaller values are violations;
- `maxEntangledState`, `densityMatrix`, `bornProb`, `quantumBehaviour`: the state $\Phi_d$ and the
  quantum behaviours $p(a,b \mid x,y) = \operatorname{Tr}[\rho (A_{x,a} \otimes B_{y,b})]$;
- `vonNeumannMeasurement`, `vonNeumannBehaviour`: the complete von Neumann measurement in the
  orthonormal basis given by the columns of a unitary $U$, with rank-one projections
  $U |a\rangle\langle a| U^{\dagger}$;
- `dftMatrix`, `phaseDiagonal`, `dkzUnitaryA`, `dkzUnitaryB`: the DKZ measurements, i.e. the
  computational basis transformed by the discrete Fourier transform and diagonal phase unitaries;
- `whiteNoiseState`, `noisyVonNeumannBehaviour`: the state
  $\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1}/d^2$.

### Main results (Part 87)
- `dkz_optimal_of_le_twenty`, `dkz_unique_of_le_twenty`: for $2 \le d \le 20$, no complete von
  Neumann measurements on $\Phi_d$ give a smaller value of the CGLMP functional than the DKZ
  measurements, whose value is $\frac{d-1}{2}(4 - I_{ME}(d)) < d - 1$ (`cglmpFunctional_dkz`);
  and the minimum is attained exactly by the measurements that a local unitary $u \otimes \bar u$
  maps to the DKZ measurements (`IsDKZUpToLocalUnitary`). No hypotheses.
- `dkz_noise_of_le_twenty`: the noise clause, for white noise on $\Phi_d$ and the violation of the
  CGLMP inequality: whenever complete von Neumann measurements violate it on $\rho_v$, so do the DKZ
  measurements; measurements that violate it at every visibility at which DKZ does are DKZ up to
  $u \otimes \bar u$. No hypotheses.
- `dkz_optimal`, `dkz_unique`, `dkz_noise`: the same for every $d \ge 2$, assuming
  `Hyp_ConeCertPos_large`.
- `dkz_optimal_any_dim_of_le_twenty`, `dkz_unique_any_dim_of_le_twenty`: a strengthening to all
  $d$-outcome projective measurements (of any ranks) on maximally entangled states $\Phi_D$ of every
  local dimension $D$; optimizers have $D = dK$ and are DKZ $\otimes 1_K$ up to local unitaries.
- `strip_inequality`, `strip_equality`: the matrix inequality $(*)$ on which the proof rests, and
  its equality case. No hypotheses.

The uniqueness statements characterize all optimal strategies: they are exactly the images of the
DKZ measurements under the local unitaries $u \otimes \bar u$, which are the local unitaries that
leave $\Phi_d$ invariant (`kronecker_mulVec_maxEntangledState_eq_iff`). Every other symmetry of the problem (for example a relabelling of outputs
that preserves the functional) therefore maps the DKZ measurements to measurements of this form.

### Checks of the definitions (end of Part 0)
- `le_cglmpFunctional_of_isLocalBehaviour` (the CGLMP inequality for local models) and
  `cglmpFunctional_deterministicBehaviour_zero` (the local bound $d - 1$ is attained);
- `cglmpFunctional_computationalBasis`: measuring $\Phi_d$ in the computational basis gives exactly
  $d - 1$, no violation;
- `bornProb_maxEntangledState`: $\operatorname{Tr}[|\Phi_D\rangle\langle\Phi_D| (A \otimes B)] =
  \operatorname{Tr}(A^{T} B)/D$;
- `isProjectiveMeasurement_vonNeumannMeasurement`, `trace_vonNeumannMeasurement`: complete von
  Neumann measurements are projective with rank-one outcomes; `dkzUnitaryA_mem_unitaryGroup`,
  `dkzUnitaryB_mem_unitaryGroup` (Part 87): the DKZ bases are orthonormal;
- `kronecker_mulVec_maxEntangledState_eq_iff`: for a unitary $u$, $(u \otimes v) \Phi_d = \Phi_d$
  if and only if $v = \bar u$;
- `cglmpExpr_eq_cglmpFunctional`: for every normalized behaviour $p$, the CGLMP expression of
  Collins et al. (2002), eq. (4), with which the proof works, is $I_d(p) = 4 - \frac{2}{d-1} F(p')$,
  where $F$ is the functional of the OQP page and $p'$ is $p$ with the two inputs exchanged;
- `cglmpMaxEntValue_two`, `dkz_tsirelson`: for $d = 2$ the bound is Tsirelson's bound $2\sqrt{2}$;
- `adglState_beats_maxEntangledState` (Part 87), a counterexample to a related question: for
  $d = 3$ a non-maximally entangled state with the DKZ measurements violates the CGLMP inequality
  more than any complete von Neumann measurements on $\Phi_3$ (Acín, Durt, Gisin and Latorre 2002),
  so the restriction to $\Phi_d$ in the problem matters.

### The hypothesis for $d \ge 21$
The proof needs the cone condition $\mathrm{CONE}_d$ with an all-positive cell vector
(`ConeCertPos d`). For $2 \le d \le 20$ it is proved in this file from explicit certificates that
the Lean kernel checks (`decide +kernel`). For $d \ge 21$ it is the statement
`Hyp_ConeCertPos_large`, which rests on interval-arithmetic certificates checked outside Lean:
linear-programming certificates for $21 \le d \le 200$, Gaussian-modulation certificates for
$201 \le d \le 2000$, and an analytic argument with certified bounds for $d \ge 2001$ (folder
`cone-certificates/` of [MS26]). It is not checked by the Lean kernel here, so the results for every
$d \ge 2$ take it as an explicit hypothesis.

### Scope
Part A, the Kullback-Leibler clause and general (non-projective) measurements are not formalized
here.

### Organization
Part 0 states the problem; Parts 1-86 contain the proof, which follows [MS26] and works with an
internal model (`Strategy`: projective measurements on $\Phi_D$, statistics
$\operatorname{Tr}(A^{T} B)/D$, the CGLMP expression of Collins et al.); Part 87 proves that the
definitions of Part 0 reduce to the internal model and states the main results. The proof parts are:
- `CGLMPRigidity*`: CGLMP rigidity in abstract $*$-algebras;
- `Statement`, `Skeleton`: the internal model and the chain of the proof as named hypotheses;
- `Reduction*`: exact reduction of a strategy to a clock model and a configuration of projections;
- `Strip*`: the strip inequality $(*)$ for every matrix size, via the Radon identity;
- `Cell*`: from $(*)$ to the cell inequalities;
- `Cert*`: the cone condition $\mathrm{CONE}_d$ for $2 \le d \le 20$, from kernel-checked
  certificates;
- `Rigidity*`, `Classical*`: the equality case (uniqueness), with the classical commuting case;
- `Main`, `CglmpNoise`: assembly of the main theorems of the internal model.

The comments refer to the parts by the labels of the original development: L1 (statement and
skeleton), L2 (reduction), L3a and L3b (strip inequality), L4 (cone certificates), L5 (cell
inequalities), L6 (rigidity) and L7 (classical Theorem B). Labels such as `QD2-L1` or `Q-L9` refer to
lemmas of the working notes behind [MS26] (see `proofs/README.md` there); each one used is stated and
proved in `papers/math`.

## References
- Formal Conjectures issue #3444, *Formalize Open Quantum Problem #27: The power of CGLMP
  inequalities*: https://github.com/google-deepmind/formal-conjectures/issues/3444
- D. Collins, N. Gisin, N. Linden, S. Massar and S. Popescu, *Bell inequalities for arbitrarily
  high-dimensional systems*, Phys. Rev. Lett. 88, 040404 (2002).
- T. Durt, D. Kaszlikowski and M. Zukowski, *Violations of local realism with quantum systems
  described by N-dimensional Hilbert spaces up to N = 16*, Phys. Rev. A 64, 024101 (2001).
- A. Acín, T. Durt, N. Gisin and J. I. Latorre, *Quantum nonlocality in two three-level systems*,
  Phys. Rev. A 65, 052325 (2002).
- J.-D. Bancal, N. Gisin and S. Pironio, *Looking for symmetric Bell inequalities*,
  J. Phys. A 43, 385303 (2010).
- R. D. Gill, *Better Bell inequalities (passion at a distance)*, IMS Lecture Notes 55 (2007),
  arXiv:math/0610115.
- [MS26] A. Mishra and A. Senthilkumar, *A strip inequality for projections, two-variable BMV
  positivity, and optimal CGLMP measurements in every dimension* (2026), with proofs, certificates
  and checks at
  [IQOQI-OQP-27](https://github.com/anshM123/IQOQI-OQP-27).
  Paths such as `papers/math`, `proofs/...`, `cone-certificates/...` and `lean/...` in the
  comments of this file refer to that repository, and paths `CGLMP/...` to
  [anshM123/CGLMP](https://github.com/anshM123/CGLMP).
- IQOQI Vienna Open Quantum Problems, problem 27:
  https://oqp.iqoqi.oeaw.ac.at/the-power-of-cglmp-inequalities
-/

@[expose] public section
