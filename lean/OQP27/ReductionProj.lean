import OQP27.ReductionCsc

/-!
# OQP 27B, module L2 (reduction), part 8: the cotangent form, paper eq. (projform)

Sources: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 6.3, eq. (projform);
`iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, items 1.3 and 1.4(b).

With `N = 4d`, `κ(u) = cot(π u/N)` (`κ(0) = 0`), `A_x = Q_x`, `B_x = Q_{x+d}` and
`⟨A, B⟩_τ = ∑_{x,y ∈ ℤ_N} κ(x - y) τ(A_x B_y)`:

Main results (all PROVED, no hypotheses):
* `OQP27.Red.pairing_odd_kernel` (R1.4(b), general kernel): for every odd `K` on `ℤ_N`,
  `∑_{x,y} K(x - y) τ(A_x B_y) = ∑_{m=1}^{2d-1} K(m) N(m)`, for every family `Q` (no constraint).
* `OQP27.Red.pairing_odd_kernel_fold`: for a 27B configuration, `= d K(d) + ∑_{m=1}^{d-1} (K(m) + K(2d-m)) N(m)`.
* `OQP27.Red.pairing_cot` (R1.4(b)): `⟨A, B⟩_τ = d + ∑_{m=1}^{d-1} 2 csc(π m/(2d)) N(m)`.
* `OQP27.Red.projform` (**paper eq. (projform)**): `F(V) = (1/2) ⟨A, B⟩_τ - d/2`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

variable {d : ℕ} [NeZero d] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Folding sums over `ℤ_{4d}` -/

omit [NeZero d] in
lemma natCast_four_d_sub {m : ℕ} (hm : m ≤ 4 * d) :
    ((4 * d - m : ℕ) : ZMod (4 * d)) = -(m : ZMod (4 * d)) := by
  rw [Nat.cast_sub hm, ZMod.natCast_self, zero_sub]

omit [NeZero d] in
lemma neg_two_d : -((2 * d : ℕ) : ZMod (4 * d)) = ((2 * d : ℕ) : ZMod (4 * d)) := by
  have h : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self _
  have e : ((4 * d : ℕ) : ZMod (4 * d)) = ((2 * d : ℕ) : ZMod (4 * d)) + ((2 * d : ℕ) : ZMod (4 * d)) := by
    push_cast
    ring
  rw [e] at h
  linear_combination -h

/-- `∑_{n ∈ ℤ_{4d}} G(n) = G(0) + G(2d) + ∑_{m=1}^{2d-1} (G(m) + G(-m))`. -/
lemma sum_zmod4d_fold {M : Type*} [AddCommMonoid M] (G : ZMod (4 * d) → M) :
    ∑ n, G n = G 0 + G ((2 * d : ℕ) : ZMod (4 * d))
      + ∑ m ∈ Ico 1 (2 * d), (G m + G (-(m : ZMod (4 * d)))) := by
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [sum_zmod_eq_sum_range]
  have h4 : 4 * d = (2 * d + 1) + (2 * d - 1) := by omega
  rw [show range (4 * d) = range (2 * d + 1 + (2 * d - 1)) by rw [← h4], sum_range_add, sum_range_succ,
    sum_range_eq_add_Ico _ (by omega : 0 < 2 * d)]
  have hrefl : ∑ j ∈ range (2 * d - 1), G ((2 * d + 1 + j : ℕ) : ZMod (4 * d))
      = ∑ m ∈ Ico 1 (2 * d), G (-(m : ZMod (4 * d))) := by
    refine Finset.sum_nbij' (fun j => 2 * d - 1 - j) (fun m => 2 * d - 1 - m) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_range] at hj
      rw [mem_Ico]
      omega
    · intro m hm
      rw [mem_Ico] at hm
      rw [mem_range]
      omega
    · intro j hj
      rw [mem_range] at hj
      omega
    · intro m hm
      rw [mem_Ico] at hm
      omega
    · intro j hj
      rw [mem_range] at hj
      congr 1
      rw [← natCast_four_d_sub (d := d) (show 2 * d - 1 - j ≤ 4 * d by omega)]
      congr 1
      omega
  rw [hrefl, Nat.cast_zero, sum_add_distrib]
  abel

/-- Folding `[1, 2d)` at `d` with a reflection: `∑_{m=1}^{2d-1} f(m) = f(d) + ∑_{m=1}^{d-1} (f(m) + f(2d-m))`. -/
lemma sum_Ico_two_d_fold {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ Ico 1 (2 * d), f m = f d + ∑ m ∈ Ico 1 d, (f m + f (2 * d - m)) := by
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [← sum_Ico_consecutive _ (by omega : 1 ≤ d) (by omega : d ≤ 2 * d),
    sum_eq_sum_Ico_succ_bot (by omega : d < 2 * d), sum_add_distrib]
  have hrefl : ∑ m ∈ Ico (d + 1) (2 * d), f m = ∑ m ∈ Ico 1 d, f (2 * d - m) := by
    refine Finset.sum_nbij' (fun m => 2 * d - m) (fun m => 2 * d - m) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      rw [mem_Ico] at hm ⊢
      omega
    · intro m hm
      rw [mem_Ico] at hm ⊢
      omega
    · intro m hm
      rw [mem_Ico] at hm
      omega
    · intro m hm
      rw [mem_Ico] at hm
      omega
    · intro m hm
      rw [mem_Ico] at hm
      congr 1
      omega
  rw [hrefl]
  abel

/-! ### The pairing with an odd kernel -/

omit [DecidableEq κ] in
/-- `∑_{x,y} K(x - y) τ(Q_x Q_{y+n'}) = ∑_n K(n) C(n' - n)`. -/
lemma pairing_kernel_corr (Q : ZMod (4 * d) → Matrix κ κ ℂ) (K : ZMod (4 * d) → ℝ) (c : ZMod (4 * d)) :
    ∑ x, ∑ y, K (x - y) * (ntr (Q x * Q (y + c))).re = ∑ n, K n * Ccorr d Q (c - n) := by
  rw [sum_comm]
  have e : ∀ y : ZMod (4 * d), ∑ x, K (x - y) * (ntr (Q x * Q (y + c))).re
      = ∑ n, K n * (ntr (Q (y + n) * Q (y + c))).re := by
    intro y
    refine Fintype.sum_equiv (Equiv.subRight y) _ _ (fun x => ?_)
    simp only [Equiv.subRight_apply, add_sub_cancel]
  rw [sum_congr rfl fun y _ => e y, sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [← mul_sum, Ccorr]
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight n) _ _ (fun y => ?_)
  simp only [Equiv.coe_addRight]
  rw [show y + n + (c - n) = y + c by ring]

omit [DecidableEq κ] in
/-- **R1.4(b), general odd kernel**: for every odd `K` on `ℤ_{4d}` and every family `Q`,
`∑_{x,y} K(x - y) τ(A_x B_y) = ∑_{m=1}^{2d-1} K(m) N(m)` (`A_x = Q_x`, `B_y = Q_{y+d}`). -/
theorem pairing_odd_kernel (Q : ZMod (4 * d) → Matrix κ κ ℂ) (K : ZMod (4 * d) → ℝ)
    (hK : ∀ n, K (-n) = -K n) :
    ∑ x, ∑ y, K (x - y) * (ntr (Q x * Q (y + d))).re = ∑ m ∈ Ico 1 (2 * d), K m * Nnet d Q m := by
  rw [pairing_kernel_corr, sum_zmod4d_fold]
  have hK0 : K 0 = 0 := by
    have := hK 0
    rw [neg_zero] at this
    linarith
  have hK2 : K ((2 * d : ℕ) : ZMod (4 * d)) = 0 := by
    have := hK ((2 * d : ℕ) : ZMod (4 * d))
    rw [neg_two_d] at this
    linarith
  rw [hK0, hK2, zero_mul, zero_mul, zero_add, zero_add]
  refine sum_congr rfl fun m _ => ?_
  rw [hK, Nnet, sub_neg_eq_add, ← Ccorr_neg Q ((d : ZMod (4 * d)) - m)]
  rw [show -((d : ZMod (4 * d)) - m) = (m : ZMod (4 * d)) - d by ring,
    show (d : ZMod (4 * d)) + m = (m : ZMod (4 * d)) + d by ring]
  ring

/-- The odd-kernel pairing of a 27B configuration, folded with `N(2d - m) = N(m)` and `N(d) = d`. -/
theorem pairing_odd_kernel_fold [Nonempty κ] {Q : ZMod (4 * d) → Matrix κ κ ℂ} (hQ : IsConfig27B d Q)
    (K : ZMod (4 * d) → ℝ) (hK : ∀ n, K (-n) = -K n) :
    ∑ x, ∑ y, K (x - y) * (ntr (Q x * Q (y + d))).re
      = d * K d + ∑ m ∈ Ico 1 d, (K m + K ((2 * d - m : ℕ) : ZMod (4 * d))) * Nnet d Q m := by
  rw [pairing_odd_kernel Q K hK, sum_Ico_two_d_fold (fun m => K m * Nnet d Q m), Nnet_d hQ]
  congr 1
  · ring
  · refine sum_congr rfl fun m hm => ?_
    have hm' := mem_Ico.1 hm
    rw [Nnet_reflect Q (by omega : m ≤ 2 * d)]
    ring

/-! ### The cotangent kernel and eq. (projform) -/

/-- The discrete Hilbert kernel `κ(u) = cot(π u/N)` on `ℤ_N`, `N = 4d`, with `κ(0) = 0`. -/
def kap (d : ℕ) (u : ZMod (4 * d)) : ℝ :=
  if u = 0 then 0 else Real.cot (Real.pi * u.val / (4 * d))

lemma cot_pi_sub (x : ℝ) : Real.cot (Real.pi - x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

lemma kap_neg (u : ZMod (4 * d)) : kap d (-u) = -kap d u := by
  unfold kap
  by_cases hu : u = 0
  · subst hu
    simp
  · rw [if_neg (neg_ne_zero.2 hu), if_neg hu, ZMod.neg_val, if_neg hu]
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    have hv : u.val ≤ 4 * d := (ZMod.val_lt u).le
    rw [Nat.cast_sub hv, ← cot_pi_sub]
    congr 1
    push_cast
    field_simp

lemma kap_d : kap d (d : ZMod (4 * d)) = 1 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hval : ((d : ℕ) : ZMod (4 * d)).val = d := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hne : ((d : ℕ) : ZMod (4 * d)) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [hval, ZMod.val_zero] at this
    omega
  rw [kap, if_neg hne, hval]
  have : Real.pi * (d : ℝ) / (4 * d) = Real.pi / 4 := by
    have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    field_simp
  rw [this, Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four,
    div_self (by positivity)]

omit [NeZero d] in
/-- `κ(m) + κ(2d - m) = 2 csc(π m/(2d))` for `1 ≤ m ≤ d - 1`. -/
lemma kap_add_reflect {m : ℕ} (hm0 : 1 ≤ m) (hm : m < d) :
    kap d (m : ZMod (4 * d)) + kap d ((2 * d - m : ℕ) : ZMod (4 * d)) = 2 * cscd d m := by
  have hd : 0 < d := by omega
  have hv1 : ((m : ℕ) : ZMod (4 * d)).val = m := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hv2 : ((2 * d - m : ℕ) : ZMod (4 * d)).val = 2 * d - m := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hn1 : ((m : ℕ) : ZMod (4 * d)) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [hv1, ZMod.val_zero] at this
    omega
  have hn2 : ((2 * d - m : ℕ) : ZMod (4 * d)) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [hv2, ZMod.val_zero] at this
    omega
  rw [kap, kap, if_neg hn1, if_neg hn2, hv1, hv2, cscd, psi]
  set θ : ℝ := Real.pi * m / (4 * d) with hθ
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have e2 : Real.pi * ((2 * d - m : ℕ) : ℝ) / (4 * d) = Real.pi / 2 - θ := by
    rw [hθ, Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have e3 : Real.pi * m / (2 * d) = 2 * θ := by
    rw [hθ]
    field_simp
    ring
  rw [e2, e3, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, Real.sin_two_mul]
  have hpos : 0 < θ := by rw [hθ]; positivity
  have hlt : θ < Real.pi / 2 := by
    rw [hθ, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (m : ℝ) < d := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)).ne'
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩).ne'
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **R1.4(b)**: `⟨A, B⟩_τ = d + ∑_{m=1}^{d-1} 2 csc(π m/(2d)) N(m)` for every 27B configuration. -/
theorem pairing_cot [Nonempty κ] {Q : ZMod (4 * d) → Matrix κ κ ℂ} (hQ : IsConfig27B d Q) :
    ∑ x, ∑ y, kap d (x - y) * (ntr (Q x * Q (y + d))).re
      = d + ∑ m ∈ Ico 1 d, 2 * cscd d m * Nnet d Q m := by
  rw [pairing_odd_kernel_fold hQ (kap d) kap_neg, kap_d, mul_one]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_Ico.1 hm
  rw [kap_add_reflect hm'.1 hm'.2]

/-- **Paper eq. (projform)**: for order-4 unitaries `V_0, …, V_{d-1}` with 27B configuration `Q`
(`A_x = Q_x`, `B_x = Q_{x+d}`), `F(V) = (1/2) ∑_{x,y ∈ ℤ_{4d}} κ(x - y) τ(A_x B_y) - d/2`. -/
theorem projform [Nonempty κ] {V : ℕ → Matrix κ κ ℂ} (hV : ∀ k, IsUnitaryM (V k))
    (hV4 : ∀ k, V k ^ 4 = 1) :
    clockF d V = (1 / 2) * ∑ x, ∑ y, kap d (x - y) * (ntr (Qcfg d V x * Qcfg d V (y + d))).re
      - d / 2 := by
  rw [pairing_cot (Qcfg_isConfig hV hV4), clockF_eq_csc hV hV4, mul_add, mul_sum]
  have : ∀ m ∈ Ico 1 d, (1 / 2 : ℝ) * (2 * cscd d m * Nnet d (Qcfg d V) m)
      = cscd d m * Nnet d (Qcfg d V) m := fun m _ => by ring
  rw [sum_congr rfl this]
  ring

end

end OQP27.Red
