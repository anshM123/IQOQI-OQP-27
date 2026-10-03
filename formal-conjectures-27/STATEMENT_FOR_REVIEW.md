# OQP 27B in Lean: the statement, for review

This digest contains only what a reviewer must check: the definitions (Part 0 of `27.lean`, Mathlib only)
and the full statements of the main results (Part 87), copied verbatim. The proofs (Parts 1-86, about 34,000 lines) are
checked by Lean and do not need to be read to validate the statement. File:
`FormalConjectures/OpenQuantumProblems/27.lean` in google-deepmind/formal-conjectures (upstream df3f12d7).

The formulation follows Formal Conjectures issue #3444: the maximally entangled state Phi_d of
C^d (x) C^d, complete von Neumann d-outcome measurements, the CGLMP functional of the OQP page
(local bound d-1, violation = smaller value), Born rule Tr[rho (A (x) B)], white noise on the state.

## 1. Definitions (Part 0)

```lean
/- ## Part 0: the problem

OQP 27B in the formulation of Formal Conjectures issue #3444, with all definitions written from
scratch with Mathlib only: the Bell scenario with two inputs and $d$ outputs per party, local
deterministic strategies and the local polytope, the CGLMP functional in the form of the OQP page,
quantum behaviours $p(a,b \mid x,y) = \operatorname{Tr}[\rho (A_{x,a} \otimes B_{y,b})]$, the
maximally entangled state $\Phi_d$ of $\mathbb{C}^d \otimes \mathbb{C}^d$, complete von Neumann
measurements, the Fourier-phase (DKZ) measurements and white noise. The main theorems at the end of
the file are stated with these definitions; Part 87 reduces them to the internal model of the proof
(Parts 1-86). -/

namespace OpenQuantumProblem27

open Matrix
open scoped Kronecker

section Problem

/- ### The Bell scenario and the CGLMP functional -/

/-- A behaviour of the Bell scenario with two inputs and `d` outputs per party: `p x y a b` is the
probability $p(a, b \mid x, y)$ of Alice's output `a` and Bob's output `b` on Alice's input `x` and
Bob's input `y`. The inputs `0, 1 : Fin 2` are the inputs $1, 2$ of the OQP page. -/
abbrev Behaviour (d : ℕ) := Fin 2 → Fin 2 → Fin d → Fin d → ℝ

/-- The deterministic local strategy in which Alice outputs `f x` on input `x` and Bob outputs
`g y` on input `y`: $p(a,b \mid x,y) = \delta_{a,f(x)} \delta_{b,g(y)}$. -/
noncomputable def deterministicBehaviour {d : ℕ} (f g : Fin 2 → Fin d) : Behaviour d :=
  fun x y a b => if a = f x ∧ b = g y then 1 else 0

/-- `p` lies in the local polytope: it is a convex combination of deterministic local strategies. -/
def IsLocalBehaviour {d : ℕ} (p : Behaviour d) : Prop :=
  ∃ q : (Fin 2 → Fin d) × (Fin 2 → Fin d) → ℝ, (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧
    ∀ x y a b, p x y a b = ∑ s, q s * deterministicBehaviour s.1 s.2 x y a b

/-- **The CGLMP functional**, in the form of the OQP page and of Formal Conjectures issue #3444:
$$E[m(A_1 - B_1)] + E[m(B_1 - A_2)] + E[m(A_2 - B_2)] + E[m(B_2 - A_1 - 1)],$$
where $A_x$ and $B_y$ are the outputs on the inputs $x, y \in \{1, 2\}$ and
$m(t) = t \bmod d \in \{0, \dots, d - 1\}$. Every local model satisfies the CGLMP inequality
$\ge d - 1$ (`le_cglmpFunctional_of_isLocalBehaviour`); a smaller value is a violation. -/
noncomputable def cglmpFunctional {d : ℕ} (p : Behaviour d) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    (p 0 0 a b * ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 1 0 a b * ((((b : ℕ) - (a : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 1 1 a b * ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 0 1 a b * ((((b : ℕ) - (a : ℕ) - 1 : ℤ) % d : ℤ) : ℝ))

/- ### Quantum behaviours -/

/-- A pure state of two $D$-level systems: a vector of $\mathbb{C}^D \otimes \mathbb{C}^D$, whose
coordinate `(i, j)` is the amplitude of $|i\rangle_A |j\rangle_B$ (Alice's system first). -/
abbrev BipartiteState (D : ℕ) := EuclideanSpace ℂ (Fin D × Fin D)

/-- The maximally entangled state $|\Phi_D\rangle = D^{-1/2} \sum_{j<D} |j\rangle_A |j\rangle_B$. -/
noncomputable def maxEntangledState (D : ℕ) : BipartiteState D :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then ((Real.sqrt D : ℝ) : ℂ)⁻¹ else 0

/-- The density matrix $|\psi\rangle\langle\psi|$ of a pure state. -/
noncomputable def densityMatrix {D : ℕ} (ψ : BipartiteState D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))

/-- The maximally entangled state of two qudits mixed with white noise:
$\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1} / d^2$. -/
noncomputable def whiteNoiseState (d : ℕ) (v : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (v : ℂ) • densityMatrix (maxEntangledState d) + (((1 - v) / (d : ℝ) ^ 2 : ℝ) : ℂ) • 1

/-- The Born rule: in the state `ρ`, the probability of the joint outcome with projections `A`
(Alice) and `B` (Bob) is $\operatorname{Tr}[\rho (A \otimes B)]$. -/
noncomputable def bornProb {D : ℕ} (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (ρ * (A ⊗ₖ B)).trace.re

/-- The quantum behaviour $p(a,b \mid x,y) = \operatorname{Tr}[\rho (A_{x,a} \otimes B_{y,b})]$ when
Alice measures `A x` and Bob measures `B y` on the state `ρ`. -/
noncomputable def quantumBehaviour {d D : ℕ} (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ) : Behaviour d :=
  fun x y a b => bornProb ρ (A x a) (B y b)

/-- `P` is a projective measurement with outcomes `Fin m` on $\mathbb{C}^D$: every `P a` is an
orthogonal projection (Hermitian and idempotent), and $\sum_a P_a = 1$. -/
def IsProjectiveMeasurement {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ a, (P a).IsHermitian ∧ P a * P a = P a) ∧ ∑ a, P a = 1

/-- The complete von Neumann measurement in the orthonormal basis formed by the columns
$u_0, \dots, u_{d-1}$ of a unitary `U`: outcome `a` has the rank-one projection
$|u_a\rangle\langle u_a| = U |a\rangle\langle a| U^{\dagger}$. -/
noncomputable def vonNeumannMeasurement {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  U * single a a 1 * Uᴴ

/-- The behaviour of complete von Neumann measurements in the bases `UA x` (Alice) and `UB y` (Bob)
on the maximally entangled state $\Phi_d$ of two qudits. -/
noncomputable def vonNeumannBehaviour (d : ℕ) (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    Behaviour d :=
  quantumBehaviour (densityMatrix (maxEntangledState d)) (fun x => vonNeumannMeasurement (UA x))
    (fun y => vonNeumannMeasurement (UB y))

/- ### The Fourier-phase (DKZ) measurements -/

/-- The discrete Fourier transform $F_{jk} = d^{-1/2} e^{2\pi i jk/d}$. -/
noncomputable def dftMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k => ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) / d)

/-- The diagonal phase unitary $\mathrm{diag}(e^{2\pi i j \theta / d})_{j<d}$. -/
noncomputable def phaseDiagonal (d : ℕ) (θ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun j => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (θ : ℂ) / d)

/-- Alice's DKZ phases $\alpha = (1/2, 0)$ for the inputs $1, 2$. -/
noncomputable def dkzAlpha : Fin 2 → ℝ := ![1 / 2, 0]

/-- Bob's DKZ phases $\beta = (-1/4, 1/4)$ for the inputs $1, 2$. -/
noncomputable def dkzBeta : Fin 2 → ℝ := ![-1 / 4, 1 / 4]

/-- Alice's DKZ basis for input `x` (Durt, Kaszlikowski and Zukowski 2001; Collins et al. 2002):
the computational basis transformed by the inverse discrete Fourier transform and the diagonal
unitary $\mathrm{diag}(e^{-2\pi i j \alpha_x / d})$, that is the basis
$|k\rangle_{A,x} = d^{-1/2} \sum_j e^{-2\pi i j (k + \alpha_x)/d} |j\rangle$. -/
noncomputable def dkzUnitaryA (d : ℕ) (x : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  phaseDiagonal d (-dkzAlpha x) * (dftMatrix d)ᴴ

/-- Bob's DKZ basis for input `y`: the computational basis transformed by the discrete Fourier
transform and the diagonal unitary $\mathrm{diag}(e^{-2\pi i j \beta_y / d})$, that is the basis
$|l\rangle_{B,y} = d^{-1/2} \sum_j e^{2\pi i j (l - \beta_y)/d} |j\rangle$. -/
noncomputable def dkzUnitaryB (d : ℕ) (y : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  phaseDiagonal d (-dkzBeta y) * dftMatrix d

/- ### White noise -/

/-- The behaviour of complete von Neumann measurements in the bases `UA x`, `UB y` on the noisy
state $\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1} / d^2$. -/
noncomputable def noisyVonNeumannBehaviour (d : ℕ) (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (v : ℝ) : Behaviour d :=
  quantumBehaviour (whiteNoiseState d v) (fun x => vonNeumannMeasurement (UA x))
    (fun y => vonNeumannMeasurement (UB y))

/- ### The CGLMP expression of Collins et al. (2002), eq. (4) -/

/-- $P(A_x = B_y + k)$ for the behaviour `p`: the probability that Alice's output equals Bob's
output plus `k`, modulo `d`. -/
noncomputable def probAEqBAdd {d : ℕ} (p : Behaviour d) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- $P(B_y = A_x + k)$ for the behaviour `p`, modulo `d`. -/
noncomputable def probBEqAAdd {d : ℕ} (p : Behaviour d) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- The CGLMP expression of Collins, Gisin, Linden, Massar and Popescu (2002), eq. (4):
$$I_d = \sum_{k=0}^{\lfloor d/2 \rfloor - 1} \Big(1 - \frac{2k}{d-1}\Big)
\Big(\big[P(A_1 = B_1 + k) + P(B_1 = A_2 + k + 1) + P(A_2 = B_2 + k) + P(B_2 = A_1 + k)\big]$$
$$- \big[P(A_1 = B_1 - k - 1) + P(B_1 = A_2 - k) + P(A_2 = B_2 - k - 1)
+ P(B_2 = A_1 - k - 1)\big]\Big),$$
with $P(A_x = B_y + k)$ the probability that $A_x - B_y \equiv k \pmod d$; local models give
$I_d \le 2$. The proof works with this form. It is the functional `cglmpFunctional` after an affine
change and the exchange of the two inputs (`cglmpExpr_eq_cglmpFunctional`). -/
noncomputable def cglmpExpr {d : ℕ} (p : Behaviour d) : ℝ :=
  ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((probAEqBAdd p 0 0 k + probBEqAAdd p 1 0 (k + 1) + probAEqBAdd p 1 1 k +
        probBEqAAdd p 0 1 k) -
      (probAEqBAdd p 0 0 (-(k : ℤ) - 1) + probBEqAAdd p 1 0 (-(k : ℤ)) +
        probAEqBAdd p 1 1 (-(k : ℤ) - 1) + probBEqAAdd p 0 1 (-(k : ℤ) - 1)))

/-- Exchange the two inputs of both parties. -/
def swapInputs {d : ℕ} (p : Behaviour d) : Behaviour d := fun x y a b => p x.rev y.rev a b

/-- $I_{ME}(d) = \frac{4}{d(d-1)} \sum_{j=1}^{d-1} \frac{d - j}{\cos(\pi j / (2d))}$, the maximal
value of `cglmpExpr` on $\Phi_d$ (`cglmpFunctional_dkz`). -/
noncomputable def cglmpMaxEntValue (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) *
    ∑ j ∈ Finset.Ico 1 d, ((d : ℝ) - j) / Real.cos (Real.pi * j / (2 * d))

end Problem

end OpenQuantumProblem27
```

## 2. The uniqueness condition

```lean
/-- The uniqueness condition: a unitary `u` such that `u ⊗ ū` maps the measurements `A`, `B`
on $\mathbb{C}^d$ to the DKZ measurements of Part 0. -/
def IsDKZUpToLocalUnitary (A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ u ∈ unitaryGroup (Fin d) ℂ,
    (∀ x a, u * A x a * uᴴ = vonNeumannMeasurement (dkzUnitaryA d x) a) ∧
    (∀ y b, u.map star * B y b * (u.map star)ᴴ = vonNeumannMeasurement (dkzUnitaryB d y) b)
```

The local unitaries in this condition are exactly those that fix the state (checked at the end of Part 0):

```lean
/-- **The local unitaries that leave $\Phi_d$ invariant** are the $u \otimes \bar u$: for a unitary
`u` and any matrix `v`, $(u \otimes v) \Phi_d = \Phi_d$ if and only if $v = \bar u$. These are the
local unitaries of the uniqueness condition `IsDKZUpToLocalUnitary` (Part 87). -/
@[category test, AMS 15 81]
theorem kronecker_mulVec_maxEntangledState_eq_iff {d : ℕ} [NeZero d]
    (u v : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ) :
    (u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d) = WithLp.ofLp (maxEntangledState d) ↔
      v = u.map star := ...
```

## 3. Main results and checks (statements only)

```lean
/-- **OQP 27B, optimality of the DKZ measurements, for $2 \le d \le 20$.** On the maximally
entangled state $\Phi_d$ of two qudits, no complete von Neumann measurements give a smaller value of
the CGLMP functional (a larger violation of the CGLMP inequality) than the DKZ measurements, whose
value is $\frac{d-1}{2}(4 - I_{ME}(d)) < d - 1$ (`cglmpFunctional_dkz`). Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := ...

/-- **OQP 27B, the optimal measurements are necessarily the DKZ measurements, for
$2 \le d \le 20$.** Complete von Neumann measurements on $\Phi_d$ attain the DKZ value of the CGLMP
functional if and only if a local unitary $u \otimes \bar u$ (these are exactly the local unitaries
that leave $\Phi_d$ invariant) maps them to the DKZ measurements. Since this characterizes all
optimal strategies, every symmetry of the problem (for instance a relabelling of outputs that
preserves the functional) maps the DKZ measurements to measurements of this form. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_unique_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := ...

/-- **OQP 27B, noise clause, for $2 \le d \le 20$**: the DKZ measurements have the highest
resistance to white noise of the violation of the CGLMP inequality. Mix $\Phi_d$ with white noise,
$\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1}/d^2$ with $v \ge 0$. Whenever
complete von Neumann measurements violate the CGLMP inequality on $\rho_v$, so do the DKZ
measurements; and measurements that violate it at every visibility at which DKZ does are DKZ up to
a local unitary $u \otimes \bar u$. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_noise_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := ...

/-- **OQP 27B, optimality, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_optimal_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := ...

/-- **OQP 27B, uniqueness, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_unique_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_unique (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := ...

/-- **OQP 27B, noise clause, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_noise_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_noise (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := ...

/-- **Optimality for all projective measurements on maximally entangled states of every local
dimension $D$**, for $2 \le d \le 20$: $F \ge \frac{d-1}{2}(4 - I_{ME}(d))$ for all $d$-outcome
projective measurements (of any ranks) on $\Phi_D$. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ≤
      cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) := ...

/-- **Uniqueness for all projective measurements on $\Phi_D$, every $D$**, for $2 \le d \le 20$:
the bound of `dkz_optimal_any_dim_of_le_twenty` is attained if and only if $D = dK$ and a unitary
$V : \mathbb{C}^D \to \mathbb{C}^d \otimes \mathbb{C}^K$ maps the measurements to the DKZ measurements
tensored with the identity, $V A_{x,a} V^{\dagger} = A^{DKZ}_{x,a} \otimes 1_K$ and
$\bar V B_{y,b} \bar V^{\dagger} = B^{DKZ}_{y,b} \otimes 1_K$ (then
$(V \otimes \bar V) \Phi_D = \Phi_d \otimes \Phi_K$). Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_unique_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) =
        ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ↔
      ∃ K : ℕ, D = d * K ∧ ∃ V : Matrix (Fin d × Fin K) (Fin D) ℂ, V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        (∀ x a, V * A x a * Vᴴ =
          vonNeumannMeasurement (dkzUnitaryA d x) a ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) ∧
        (∀ y b, V.map star * B y b * (V.map star)ᴴ =
          vonNeumannMeasurement (dkzUnitaryB d y) b ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) := ...

/-- **The value of the DKZ measurements**:
$F(\mathrm{DKZ}) = \frac{d-1}{2} (4 - I_{ME}(d))$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_dkz [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) =
      ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 := ...

/-- The DKZ measurements violate the CGLMP inequality: $F(\mathrm{DKZ}) < d - 1$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_dkz_lt [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) < (d : ℝ) - 1 := ...

/-- **Special case $d = 2$: Tsirelson's bound.** For $d = 2$ the CGLMP functional is the CHSH
functional $\frac{4 - \mathrm{CHSH}}{2}$; on two maximally entangled qubits no complete von Neumann
measurements go below $2 - \sqrt{2}$ (that is, CHSH $\le 2\sqrt{2}$), and the DKZ measurements attain
it. -/
@[category test, AMS 15 81]
theorem dkz_tsirelson (UA UB : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 2) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 2) ℂ) :
    2 - Real.sqrt 2 ≤ cglmpFunctional (vonNeumannBehaviour 2 UA UB) ∧
      cglmpFunctional (vonNeumannBehaviour 2 (dkzUnitaryA 2) (dkzUnitaryB 2)) = 2 - Real.sqrt 2 := ...

/-- **The maximally entangled state is not optimal for $d = 3$** (Acín, Durt, Gisin and Latorre
2002), a counterexample to a question related to OQP 27: with the DKZ measurements, the
non-maximally entangled state $(|00\rangle + \tfrac{4}{5} |11\rangle + |22\rangle)/\sqrt{2 + 16/25}$
gives a smaller value of the CGLMP functional, $\frac{82}{33} - \frac{80}{99}\sqrt{3}$, than any
complete von Neumann measurements on $\Phi_3$, whose minimum is $\frac{24 - 8\sqrt{3}}{9}$. -/
@[category test, AMS 15 81]
theorem adglState_beats_maxEntangledState (UA UB : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 3) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 3) ℂ) :
    cglmpFunctional (quantumBehaviour (densityMatrix (adglState (4 / 5)))
      (fun x => vonNeumannMeasurement (dkzUnitaryA 3 x))
      (fun y => vonNeumannMeasurement (dkzUnitaryB 3 y))) <
      cglmpFunctional (vonNeumannBehaviour 3 UA UB) := ...

/-- **The two forms of the CGLMP functional agree**: for every behaviour `p` in which each
$p(\cdot,\cdot \mid x,y)$ is a probability distribution, the CGLMP expression of Collins et al. is
$I_d(p) = 4 - \frac{2}{d-1} F(p')$, where $F$ is the functional of the OQP page and $p'$ is `p`
with the two inputs exchanged. In particular $I_d(p) \le 2$ if and only if $F(p') \ge d - 1$. -/
@[category API, AMS 15 81]
theorem cglmpExpr_eq_cglmpFunctional {d : ℕ} (hd : 2 ≤ d) (p : Behaviour d)
    (hp : ∀ x y, ∑ a, ∑ b, p x y a b = 1) :
    cglmpExpr p = 4 - 2 * cglmpFunctional (swapInputs p) / ((d : ℝ) - 1) := ...

/-- **The CGLMP inequality**: every local model gives at least $d - 1$. -/
@[category test, AMS 15 81]
theorem le_cglmpFunctional_of_isLocalBehaviour {d : ℕ} [NeZero d] {p : Behaviour d}
    (hp : IsLocalBehaviour p) : (d : ℝ) - 1 ≤ cglmpFunctional p := ...

/-- On $\Phi_d$, measuring both systems in the computational basis for both inputs gives exactly
the local bound $d - 1$: there is no violation without the Fourier-phase bases. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_computationalBasis {d : ℕ} [NeZero d] :
    cglmpFunctional (vonNeumannBehaviour d (fun _ => 1) (fun _ => 1)) = (d : ℝ) - 1 := ...

/-- **The Born rule on the maximally entangled state**:
$\operatorname{Tr}[|\Phi_D\rangle\langle\Phi_D| (A \otimes B)] = \operatorname{Tr}(A^{T} B) / D$. -/
@[category API, AMS 15 81]
theorem bornProb_maxEntangledState {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    bornProb (densityMatrix (maxEntangledState D)) A B = (Aᵀ * B).trace.re / D := ...

/-- **The strip inequality $(*)$.** For every $M$, every orthogonal projection $B$ on
$\mathbb{C}^M$ (with $P = 1 - B$), every Hermitian $g$ and every real $\lambda$,
$\operatorname{Tr}[(P(g - \lambda)P)_+] \le \sum_{\nu \in \operatorname{spec}(B + ig)} h_\lambda(\nu)$,
the eigenvalues counted with algebraic multiplicity (`posPartTrace`, `stripSum`, `hStrip`).
Unconditional. -/
@[category research solved, AMS 15 81]
theorem strip_inequality (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ) (hB : B.IsHermitian)
    (hB2 : B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ≤ stripSum lam B g := ...

/-- **Equality case of the strip inequality $(*)$**: equality forces $B$ and $g$ to commute.
Unconditional. -/
@[category research solved, AMS 15 81]
theorem strip_equality (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ) (hB : B.IsHermitian)
    (hB2 : B * B = B) (hg : g.IsHermitian) (lam : ℝ)
    (h : stripSum lam B g = posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))) :
    B * g = g * B := ...
```

## 4. Further definitions used in the statements

`adglState` (the counterexample of the related question) and the hypothesis `Hyp_ConeCertPos_large` that the results
for every d >= 2 assume (the cone condition for d >= 21, established outside Lean; for 2 <= d <= 20 it is proved in the
file from kernel-checked certificates). `ConeCertPos` refers to internal objects of the proof (cell vectors and
directions, part `Skeleton`/`CertDefs`); only the results for every d use it, as an explicit hypothesis.

```lean
/-- The state $(|00\rangle + \gamma |11\rangle + |22\rangle) / \sqrt{2 + \gamma^2}$ of two qutrits. -/
noncomputable def adglState (γ : ℝ) : BipartiteState 3 :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then
    ((((if (ij.1 : ℕ) = 1 then γ else 1) / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) else 0

/-- **CONE_d.** The DKZ vector `v` lies in the convex cone generated by the cell directions `u^ℓ`:
there are finitely many cells `ℓ^(k)` and weights `λ_k ≥ 0` with `∑_k λ_k u^{ℓ^(k)}_m = v_m` for every
`m = 1, …, d-1`. -/
def ConeCert (d : ℕ) : Prop :=
  ∃ (K : ℕ) (ell : Fin K → ℕ → ℝ) (lam : Fin K → ℝ),
    (∀ k, IsConeCell d (ell k)) ∧ (∀ k, 0 ≤ lam k) ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ d - 1 → ∑ k, lam k * coneU d (ell k) m = coneV d m

/-- `CONE_d` with one all-positive cell vector of positive weight (`proofs/rigidity/RIGIDITY.md` s.5: all LP
certificates for `d ≤ 200` have every `n_r ≥ 1`; for `d ≥ 201` the Dirichlet-type measures charge only
all-positive cell vectors). -/
def ConeCertPos : Prop :=
  ∃ (K : ℕ) (ell : Fin K → ℕ → ℝ) (lam : Fin K → ℝ),
    (∀ k, IsConeCell d (ell k)) ∧ (∀ k, 0 ≤ lam k) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ d - 1 → ∑ k, lam k * coneU d (ell k) m = coneV d m) ∧
    ∃ k, 0 < lam k ∧ ∀ r < d, 0 < ell k r

/-- `ConeCertPos d` for every `d ≥ 21`.  Not formalised.  Computer-assisted (Python interval arithmetic): the LP
certificates `cone-certificates/certs/cert_d{d}.json` (all cells with `n_r ≥ 1`, all weights certified `> 0`) for `21 ≤ d ≤ 200`
(QD2-T1); the Gaussian-modulation certificates (QD2-T2, `cone-certificates/CONE_PROOF.md` Lemma B) for `201 ≤ d ≤ 2000`; the
analytic argument `cone-certificates/CONE_ALLD_PROOF.md` for `d ≥ 2001` (QD2-T3); the positivity of the cells for `d ≥ 201` is
`proofs/rigidity/RIGIDITY.md` s.5.  -/
def Hyp_ConeCertPos_large : Prop := ∀ d : ℕ, 21 ≤ d → ConeCertPos d
```
