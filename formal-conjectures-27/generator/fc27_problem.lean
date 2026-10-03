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
