import OQP27.ClassicalDefs
import OQP27.CellStripFn

/-!
# The continuous rearrangement inequality for unit cells (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Lemma `lem:smear` and Proposition `prop:cont`
(the continuous rearrangement inequality, via the circle Stein-Weiss/Laeng distribution identity and the
bathtub principle), in the case `N = 4d`, `|A| = |B| = d` used for Theorem B.

Main result (`OQP27.ClassB.kbar_continuum`): for disjoint `A, B ⊆ ℤ_{4d}` with `|A| = |B| = d`,
    `∑_{x ∈ A, y ∈ B} κ̄(x - y) ≤ ∑_{x ∈ [0,d), y ∈ [-d,0)} κ̄(x - y) = (N²/π²) Cl₂(π/2)`,
where `κ̄ = kbar N` is the smeared cotangent kernel (`OQP27.ClassB.kbar`): `κ̄(x - y)` is the continuous
pairing `∫_{[x,x+1)} ∫_{[y,y+1)} cot(π(ξ - η)/N) dη dξ` of two unit cells.

Route.  We do not formalise the distribution identity separately.  The scalar (`M = 1`) case of module L5's
Q-T1 for step fields (`OQP27.Cell.stepField_ineq`, on the uniform partition `t_k = 2πk/N` of the circle,
with `A_x`, `B_x` the indicator `1 × 1` matrices of `A`, `B`) is exactly the dual (Legendre) form of the
bathtub argument: `(1/π) ∑ arcKernel - λ ∑ |J_x| [x ∈ A] ≤ 2π h_λ(1/4)`, where the mean value identity
(`OQP27.Cell.mean_value_boundary`) plays the role of the distribution identity.  The strip inequality `(*)`
that `stepField_ineq` takes as an argument is trivial (an equality) for `1 × 1` matrices
(`OQP27.ClassB.starAt_one`): a `1 × 1` projection is `0` or `1`, and `h_λ` has the boundary values
`(y - λ)_+` and `0`.  At `λ* = log 2/(2π)` module L5's window value (`OQP27.Cell.window_value`) gives
`h_{λ*}(1/4) + λ*/4 = Cl₂(π/2)/π²`.  Finally `∑_{[0,d) × [-d,0)} κ̄` telescopes to `(N²/π²) Cl₂(π/2)`.

No hypotheses.  Uses module L5 (`OQP27/Cell*.lean`, in particular `CellQT1`, `CellLegendre`,
`CellStripFn`) and module L4's `clausen2`.
-/

set_option autoImplicit false

namespace OQP27.ClassB

open Real Finset Matrix Complex

/-! ## The Clausen function: periodicity -/

lemma clausen2_periodic : Function.Periodic clausen2 (2 * π) := fun x => Cell.clausen2_add_two_pi x

lemma clausen2_add_int_mul (x : ℝ) (q : ℤ) : clausen2 (x + q * (2 * π)) = clausen2 x :=
  (clausen2_periodic.int_mul q) x

/-- `κ̄` is `N`-periodic. -/
lemma kbarR_add_int_mul (N : ℕ) [NeZero N] (m : ℝ) (q : ℤ) :
    kbarR N (m + q * N) = kbarR N m := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  unfold kbarR
  have e0 : 2 * π * (m + q * N) / N = 2 * π * m / N + q * (2 * π) := by field_simp
  have e1 : 2 * π * (m + q * N + 1) / N = 2 * π * (m + 1) / N + q * (2 * π) := by
    field_simp; ring
  have e2 : 2 * π * (m + q * N - 1) / N = 2 * π * (m - 1) / N + q * (2 * π) := by
    field_simp; ring
  rw [e0, e1, e2, clausen2_add_int_mul, clausen2_add_int_mul, clausen2_add_int_mul]

/-- `κ̄(t mod N) = κ̄(t)` for every integer `t`. -/
lemma kbar_intCast (N : ℕ) [NeZero N] (t : ℤ) : kbar N (t : ZMod N) = kbarR N t := by
  unfold kbar
  have h1 : (((t : ZMod N).val : ℤ) : ℝ) = ((t % (N : ℤ) : ℤ) : ℝ) := by
    rw [ZMod.val_intCast]
  have h2 : ((t % (N : ℤ) : ℤ) : ℝ) = (t : ℝ) + ((-(t / (N : ℤ)) : ℤ) : ℝ) * N := by
    have := Int.mul_ediv_add_emod t (N : ℤ)
    push_cast
    have h3 : (N : ℝ) * ((t / (N : ℤ) : ℤ) : ℝ) + ((t % (N : ℤ) : ℤ) : ℝ) = (t : ℝ) := by
      exact_mod_cast this
    linarith
  have h4 : (((t : ZMod N).val : ℕ) : ℝ) = (((t : ZMod N).val : ℤ) : ℝ) := by push_cast; rfl
  rw [h4, h1, h2, kbarR_add_int_mul]

lemma kbar_natCast_sub (N : ℕ) [NeZero N] (x y : ℕ) :
    kbar N ((x : ZMod N) - (y : ZMod N)) = kbarR N ((x : ℝ) - y) := by
  have : (x : ZMod N) - (y : ZMod N) = (((x : ℤ) - y : ℤ) : ZMod N) := by push_cast; ring
  rw [this, kbar_intCast]
  push_cast
  ring_nf

/-! ## The uniform partition of the circle -/

/-- The uniform arc partition `t_k = 2πk/N`. -/
noncomputable def unifP (N : ℕ) [NeZero N] : Cell.ArcPartition N where
  t := fun k => 2 * π * k / N
  t_zero := by simp
  t_last := by
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    field_simp
  t_lt := by
    intro k _
    have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    apply div_lt_div_of_pos_right _ hN
    push_cast
    nlinarith [Real.pi_pos]

lemma unifP_t (N : ℕ) [NeZero N] (k : ℕ) : (unifP N).t k = 2 * π * k / N := rfl

lemma unifP_len (N : ℕ) [NeZero N] (k : ℕ) : (unifP N).t (k + 1) - (unifP N).t k = 2 * π / N := by
  rw [unifP_t, unifP_t]
  push_cast
  ring

/-- The arc kernel of the uniform partition is `(2π²/N²) κ̄`. -/
lemma arcKernel_unifP (N : ℕ) [NeZero N] (x y : ℕ) :
    Cell.arcKernel (unifP N) x y = 2 * π ^ 2 / (N : ℝ) ^ 2 * kbarR N ((x : ℝ) - y) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold Cell.arcKernel kbarR
  simp only [unifP_t]
  push_cast
  have a1 : 2 * π * (x : ℝ) / N - 2 * π * y / N = 2 * π * ((x : ℝ) - y) / N := by ring
  have a2 : 2 * π * ((x : ℝ) + 1) / N - 2 * π * y / N = 2 * π * ((x : ℝ) - y + 1) / N := by ring
  have a3 : 2 * π * (x : ℝ) / N - 2 * π * ((y : ℝ) + 1) / N = 2 * π * ((x : ℝ) - y - 1) / N := by
    ring
  have a4 : 2 * π * ((x : ℝ) + 1) / N - 2 * π * ((y : ℝ) + 1) / N = 2 * π * ((x : ℝ) - y) / N := by
    ring
  rw [a1, a2, a3, a4]
  field_simp
  ring

/-! ## Indicator matrices -/

/-- The `1 × 1` indicator matrix of `S` at `x mod N`. -/
noncomputable def ind {N : ℕ} (S : Finset (ZMod N)) (x : ℕ) : Matrix (Fin 1) (Fin 1) ℂ :=
  if (x : ZMod N) ∈ S then 1 else 0

lemma ind_proj {N : ℕ} (S : Finset (ZMod N)) (x : ℕ) : Cell.IsProj (ind S x) := by
  unfold ind
  split_ifs
  · exact ⟨Matrix.isHermitian_one, by simp⟩
  · exact ⟨Matrix.isHermitian_zero, by simp⟩

lemma ind_mul_ind {N : ℕ} {A B : Finset (ZMod N)} (hAB : Disjoint A B) (x : ℕ) :
    ind A x * ind B x = 0 := by
  unfold ind
  by_cases hA : (x : ZMod N) ∈ A
  · have hB : (x : ZMod N) ∉ B := Finset.disjoint_left.1 hAB hA
    simp [hA, hB]
  · simp [hA]

lemma ind_trace_re {N : ℕ} (S : Finset (ZMod N)) (x : ℕ) :
    (ind S x).trace.re = if (x : ZMod N) ∈ S then 1 else 0 := by
  unfold ind
  split_ifs <;> simp

lemma ind_mul_trace_re {N : ℕ} (A B : Finset (ZMod N)) (x y : ℕ) :
    (ind A x * ind B y).trace.re = if (x : ZMod N) ∈ A ∧ (y : ZMod N) ∈ B then 1 else 0 := by
  unfold ind
  by_cases hA : (x : ZMod N) ∈ A <;> by_cases hB : (y : ZMod N) ∈ B <;> simp [hA, hB]

/-- The operator constraint for the indicator field of `B` on the uniform partition. -/
lemma op_unif (N : ℕ) [NeZero N] (B : Finset (ZMod N)) :
    ∑ k ∈ range N, ((((unifP N).t (k + 1) - (unifP N).t k) / (2 * π) : ℝ) : ℂ) • ind B k =
      ((((B.card : ℝ) / N) : ℝ) : ℂ) • 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hlen : ∀ k, ((unifP N).t (k + 1) - (unifP N).t k) / (2 * π) = 1 / N := by
    intro k
    rw [unifP_len]
    field_simp
  simp only [hlen]
  rw [← Finset.smul_sum]
  have hsum : ∑ k ∈ range N, ind B k = (B.card : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    unfold ind
    rw [Cell.sum_range_eq_sum_zmod N (fun z => if z ∈ B then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0)]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [hsum, smul_smul]
  congr 1
  push_cast
  ring

/-! ## The strip inequality for `1 × 1` matrices -/

lemma posPartTrace_one_by_one (Y : Matrix (Fin 1) (Fin 1) ℂ) (hY : Y.IsHermitian) :
    OQP27.posPartTrace Y = max (Y 0 0).re 0 := by
  unfold OQP27.posPartTrace
  rw [dif_pos hY, Fin.sum_univ_one]
  congr 1
  have h := hY.trace_eq_sum_eigenvalues
  rw [Fin.sum_univ_one, Matrix.trace_fin_one] at h
  rw [h]
  simp

/-- **The strip inequality `(*)` for `1 × 1` matrices** (it is an equality). -/
lemma starAt_one (lam : ℝ) : Cell.StarAt 1 (OQP27.hStrip lam) lam := by
  intro Bm g hB hg
  rw [Cell.sum_roots_one_by_one]
  have hg00 : (g 0 0).im = 0 := by
    have h := hg.apply 0 0
    exact Complex.conj_eq_iff_im.1 h
  have hg_eq : g 0 0 = ((g 0 0).re : ℂ) := by
    apply Complex.ext <;> simp [hg00]
  -- a `1 × 1` projection is `0` or `1`
  have hb : Bm 0 0 * Bm 0 0 = Bm 0 0 := by
    have h := congrFun (congrFun hB.2 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at h
    exact h
  have hb01 : Bm 0 0 = 0 ∨ Bm 0 0 = 1 := by
    have h : Bm 0 0 * (Bm 0 0 - 1) = 0 := by linear_combination hb
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hBm : Bm = Bm 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := Cell.one_by_one_eq Bm
  rcases hb01 with h0 | h1
  · -- `B = 0`
    rw [h0, zero_smul] at hBm
    subst hBm
    have hY : (g - (lam : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).IsHermitian := by
      apply hg.sub
      rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    simp only [sub_zero, one_mul, mul_one]
    rw [posPartTrace_one_by_one _ hY]
    have e1 : ((0 : Matrix (Fin 1) (Fin 1) ℂ) + I • g) 0 0 = ((g 0 0).re : ℂ) * I := by
      simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.smul_apply, smul_eq_mul]
      rw [hg_eq]
      simp only [Complex.ofReal_re]
      ring
    rw [e1, Cell.hStrip_left]
    apply le_of_eq
    congr 1
    simp [Matrix.sub_apply, Matrix.smul_apply]
  · -- `B = 1`
    rw [h1, one_smul] at hBm
    subst hBm
    have e0 : (1 - (1 : Matrix (Fin 1) (Fin 1) ℂ)) * (g - (lam : ℂ) • 1) * (1 - 1) = 0 := by simp
    rw [e0, posPartTrace_one_by_one _ Matrix.isHermitian_zero]
    have e1 : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + I • g) 0 0 = 1 + ((g 0 0).re : ℂ) * I := by
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [hg_eq]
      simp only [Complex.ofReal_re]
      ring
    rw [e1, Cell.hStrip_right]
    simp

/-! ## The continuous inequality -/

/-- `∑_{[0,d) × [-d,0)} κ̄ = (N²/π²) Cl₂(π/2)` (`N = 4d`; telescoping second differences). -/
lemma pairK_kbar_ico (d : ℕ) [NeZero d] :
    pairK (kbar (4 * d)) (ico 0 d) (ico (-(d : ZMod (4 * d))) d) =
      ((4 * d : ℕ) : ℝ) ^ 2 / π ^ 2 * clausen2 (π / 2) := by
  set N := 4 * d with hNdef
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hdN : d < N := by have := Nat.pos_of_ne_zero (NeZero.ne d); omega
  have hN : (N : ℝ) ≠ 0 := by rw [hNdef]; push_cast; positivity
  have hπ : π ≠ 0 := Real.pi_ne_zero
  -- injectivity of the interval maps
  have hinj : ∀ r : ZMod N, Set.InjOn (fun i : ℕ => r + (i : ZMod N)) (range d : Set ℕ) := by
    intro r i hi j hj hij
    simp only at hij
    have h := add_left_cancel hij
    have hi' : i < N := lt_trans (Finset.mem_range.1 hi) hdN
    have hj' : j < N := lt_trans (Finset.mem_range.1 hj) hdN
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this
  unfold pairK ico
  rw [Finset.sum_image (hinj 0)]
  simp_rw [Finset.sum_image (hinj _)]
  -- the summand as a real second difference
  set F : ℕ → ℝ := fun k => clausen2 (2 * π * k / N) with hF
  have hterm : ∀ i ∈ range d, ∀ j ∈ range d,
      kbar N ((0 : ZMod N) + (i : ZMod N) - (-(d : ZMod N) + (j : ZMod N))) =
        kbarR N ((i : ℝ) + d - j) := by
    intro i _ j _
    have e : (0 : ZMod N) + (i : ZMod N) - (-(d : ZMod N) + (j : ZMod N)) =
        (((i : ℤ) + d - j : ℤ) : ZMod N) := by push_cast; ring
    rw [e, kbar_intCast]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i hi j hj]
  -- reflect the inner index
  have hrefl : ∀ i : ℕ, ∑ j ∈ range d, kbarR N ((i : ℝ) + d - j) =
      ∑ j ∈ range d, kbarR N ((i : ℝ) + 1 + j) := by
    intro i
    rw [← Finset.sum_range_reflect (fun j => kbarR N ((i : ℝ) + 1 + j)) d]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  simp_rw [hrefl]
  -- each term is a difference of consecutive differences
  set D : ℕ → ℝ := fun k => F (k + 1) - F k with hD
  have hk : ∀ i j : ℕ, kbarR N ((i : ℝ) + 1 + j) =
      (N : ℝ) ^ 2 / (2 * π ^ 2) * (D (i + j) - D (i + j + 1)) := by
    intro i j
    unfold kbarR
    simp only [hD, hF]
    push_cast
    have b1 : 2 * π * ((i : ℝ) + 1 + j) / N = 2 * π * ((i : ℝ) + j + 1) / N := by ring
    have b2 : 2 * π * ((i : ℝ) + 1 + j + 1) / N = 2 * π * ((i : ℝ) + j + 1 + 1) / N := by ring
    have b3 : 2 * π * ((i : ℝ) + 1 + j - 1) / N = 2 * π * ((i : ℝ) + j) / N := by ring
    rw [b1, b2, b3]
    ring
  simp_rw [hk, ← Finset.mul_sum]
  have hinner : ∀ i : ℕ, ∑ j ∈ range d, (D (i + j) - D (i + j + 1)) = D i - D (i + d) := by
    intro i
    have := Finset.sum_range_sub' (fun j => D (i + j)) d
    simp only [add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_assoc]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib]
  have hs1 : ∑ i ∈ range d, D i = F d - F 0 := Finset.sum_range_sub F d
  have hs2 : ∑ i ∈ range d, D (i + d) = F (2 * d) - F d := by
    have := Finset.sum_range_sub (fun i => F (i + d)) d
    simp only [zero_add] at this
    rw [show d + d = 2 * d by ring] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hD]
    rw [show i + 1 + d = i + d + 1 by ring]
  rw [hs1, hs2]
  have hF0 : F 0 = 0 := by simp [hF, Cell.clausen2_zero]
  have hFd : F d = clausen2 (π / 2) := by
    simp only [hF]
    congr 1
    rw [hNdef]
    push_cast
    field_simp
    ring
  have hF2d : F (2 * d) = 0 := by
    simp only [hF]
    rw [show 2 * π * (((2 * d : ℕ) : ℝ)) / N = π by
      rw [hNdef]; push_cast; field_simp; ring]
    exact Cell.clausen2_pi
  rw [hF0, hFd, hF2d]
  field_simp
  ring

lemma sum_univ_ite_mem {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (f : ZMod N → ℝ) :
    ∑ x : ZMod N, (if x ∈ S then f x else 0) = ∑ x ∈ S, f x := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The kernel side of Q-T1 on the uniform partition: `∑_{x,y<N} arcKernel · [x ∈ A][y ∈ B] = (2π²/N²) ⟨A,B⟩_κ̄`. -/
lemma sum_arcKernel_ind {N : ℕ} [NeZero N] (A B : Finset (ZMod N)) :
    ∑ x ∈ range N, ∑ y ∈ range N, Cell.arcKernel (unifP N) x y * (ind A x * ind B y).trace.re =
      2 * π ^ 2 / (N : ℝ) ^ 2 * pairK (kbar N) A B := by
  set G : ZMod N → ZMod N → ℝ := fun u v =>
    2 * π ^ 2 / (N : ℝ) ^ 2 * (if u ∈ A then (if v ∈ B then kbar N (u - v) else 0) else 0) with hG
  have h1 : ∀ x ∈ range N, ∀ y ∈ range N,
      Cell.arcKernel (unifP N) x y * (ind A x * ind B y).trace.re = G (x : ZMod N) (y : ZMod N) := by
    intro x _ y _
    rw [hG, arcKernel_unifP, ind_mul_trace_re]
    show _ = 2 * π ^ 2 / (N : ℝ) ^ 2 * (if (x : ZMod N) ∈ A then
      (if (y : ZMod N) ∈ B then kbar N ((x : ZMod N) - (y : ZMod N)) else 0) else 0)
    rw [kbar_natCast_sub]
    by_cases hx : (x : ZMod N) ∈ A <;> by_cases hy : (y : ZMod N) ∈ B <;> simp [hx, hy]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => h1 x hx y hy]
  have h2 : ∀ x : ℕ, ∑ y ∈ range N, G (x : ZMod N) (y : ZMod N) = ∑ v : ZMod N, G (x : ZMod N) v :=
    fun x => Cell.sum_range_eq_sum_zmod N (G (x : ZMod N))
  simp_rw [h2]
  rw [Cell.sum_range_eq_sum_zmod N (fun u => ∑ v : ZMod N, G u v)]
  simp only [hG, ← Finset.mul_sum]
  congr 1
  unfold pairK
  have h3 : ∀ u : ZMod N, ∑ v : ZMod N, (if u ∈ A then (if v ∈ B then kbar N (u - v) else 0) else 0) =
      if u ∈ A then ∑ v ∈ B, kbar N (u - v) else 0 := by
    intro u
    by_cases hu : u ∈ A
    · simp only [hu, if_true]
      exact sum_univ_ite_mem B (fun v => kbar N (u - v))
    · simp [hu]
  simp_rw [h3]
  exact sum_univ_ite_mem A (fun u => ∑ v ∈ B, kbar N (u - v))

/-- `∑_{x<N} |J_x| [x ∈ A] = 2π |A|/N` on the uniform partition. -/
lemma sum_len_ind {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    ∑ x ∈ range N, ((unifP N).t (x + 1) - (unifP N).t x) * (ind A x).trace.re =
      2 * π / N * A.card := by
  simp only [unifP_len, ind_trace_re]
  rw [Cell.sum_range_eq_sum_zmod N (fun z => 2 * π / N * (if z ∈ A then (1 : ℝ) else 0))]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_univ_ite_mem, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Q-T1 for `1 × 1` indicator fields at `λ*`**: for disjoint `A, B ⊆ ℤ_N` with `|A| = |B| = N/4`,
`⟨A, B⟩_κ̄ ≤ (N²/π²) Cl₂(π/2)`. -/
theorem kbar_pair_le {N : ℕ} [NeZero N] (A B : Finset (ZMod N)) (hAB : Disjoint A B)
    (hA : 4 * A.card = N) (hB : 4 * B.card = N) :
    pairK (kbar N) A B ≤ (N : ℝ) ^ 2 / π ^ 2 * clausen2 (π / 2) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hπ := Real.pi_pos
  have hAr : (A.card : ℝ) = N / 4 := by
    have : ((4 * A.card : ℕ) : ℝ) = N := by rw [hA]
    push_cast at this
    linarith
  have hBr : (B.card : ℝ) = N / 4 := by
    have : ((4 * B.card : ℕ) : ℝ) = N := by rw [hB]
    push_cast at this
    linarith
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := Cell.hStrip_regular
  have hop : ∑ k ∈ range N, ((((unifP N).t (k + 1) - (unifP N).t k) / (2 * π) : ℝ) : ℂ) • ind B k =
      (((1 / 4 : ℝ)) : ℂ) • 1 := by
    rw [op_unif, hBr]
    congr 2
    field_simp
  have hineq := Cell.stepField_ineq (unifP N) (ind A) (ind B) (fun x => ind_proj A x)
    (fun x => ind_proj B x) (fun x => ind_mul_ind hAB x) (by norm_num) (by norm_num) hop hharm hcont
    hCg hgrowth (starAt_one Cell.lamStar)
  have hw := Cell.window_value hharm hcont hCg hgrowth (Cell.hStrip_left Cell.lamStar)
    (Cell.hStrip_right Cell.lamStar)
  rw [sum_arcKernel_ind, sum_len_ind, hAr] at hineq
  have hval : OQP27.hStrip Cell.lamStar ((1 / 4 : ℝ) : ℂ) =
      clausen2 (π / 2) / π ^ 2 - Cell.lamStar / 4 := by linarith
  rw [hval] at hineq
  set S := pairK (kbar N) A B
  -- `hineq : (2π²/N²) S/π - λ* (2π/N)(N/4) ≤ 2π (Cl₂(π/2)/π² - λ*/4)`
  have hS : 2 * π ^ 2 / (N : ℝ) ^ 2 * S ≤ 2 * clausen2 (π / 2) := by
    have e1 : Cell.lamStar * (2 * π / N * (N / 4)) = Cell.lamStar * (π / 2) := by
      field_simp; ring
    rw [e1] at hineq
    have h1 : 2 * π ^ 2 / (N : ℝ) ^ 2 * S / π ≤
        2 * π * (((1 : ℕ) : ℝ) * (clausen2 (π / 2) / π ^ 2 - Cell.lamStar / 4)) +
          Cell.lamStar * (π / 2) := by linarith
    rw [div_le_iff₀ hπ] at h1
    have h2 : (2 * π * (((1 : ℕ) : ℝ) * (clausen2 (π / 2) / π ^ 2 - Cell.lamStar / 4)) +
        Cell.lamStar * (π / 2)) * π = 2 * clausen2 (π / 2) := by
      push_cast
      field_simp
      ring
    linarith
  have hS' : S = (N : ℝ) ^ 2 / (2 * π ^ 2) * (2 * π ^ 2 / (N : ℝ) ^ 2 * S) := by
    field_simp
  calc S = (N : ℝ) ^ 2 / (2 * π ^ 2) * (2 * π ^ 2 / (N : ℝ) ^ 2 * S) := hS'
    _ ≤ (N : ℝ) ^ 2 / (2 * π ^ 2) * (2 * clausen2 (π / 2)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (N : ℝ) ^ 2 / π ^ 2 * clausen2 (π / 2) := by field_simp

/-- **The continuous rearrangement inequality for unit cells** (`N = 4d`, `|A| = |B| = d`):
`∑_{A × B} κ̄ ≤ ∑_{[0,d) × [-d,0)} κ̄`. -/
theorem kbar_continuum {d : ℕ} [NeZero d] (A B : Finset (ZMod (4 * d))) (hAB : Disjoint A B)
    (hA : A.card = d) (hB : B.card = d) :
    pairK (kbar (4 * d)) A B ≤ pairK (kbar (4 * d)) (ico 0 d) (ico (-(d : ZMod (4 * d))) d) := by
  rw [pairK_kbar_ico]
  exact kbar_pair_le A B hAB (by rw [hA]) (by rw [hB])

end OQP27.ClassB
