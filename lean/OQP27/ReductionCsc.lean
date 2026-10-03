import OQP27.ReductionQ

/-!
# OQP 27B, module L2 (reduction), part 5: the linear (csc) form of `F` (QD-L7)

Sources: `iqoqi/programs/oqp27B_all/SHARED_LEMMAS.md` [QD] (QD-L7);
`iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, items 1.3 and 1.4;
`publish/CGLMP/paper-classical-all-d/main.tex`, Lemma 3.1 (the computation `Re[h_m i^s] = sec(ψ_m - sπ/2)`).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.Qcfg_isConfig`: the spectral projections of `E_k = V_k^*` form a 27B configuration.
* `OQP27.Red.clockF_eq_csc` (**QD-L7**): `F(V) = ∑_{m=1}^{d-1} csc(π m/(2d)) N(m)`.
* `OQP27.Red.Nnet_d`, `OQP27.Red.Nnet_reflect` (RIGIDITY_ALLD.md 1.4(a)): `N(d) = d`, `N(2d - m) = N(m)`.
* `OQP27.Red.Nnet_add_reflect_le` (RIGIDITY_ALLD.md (1.2)): `N(s) + N(d - s) ≤ d`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### The configuration of a clock family -/

/-- `Q_{k - d a}` as a function of the site `k` and the label `a`: the spectral projection of
`E_k = V_k^*` for the eigenvalue `i^a`. -/
def Qs (V : ℕ → Matrix κ κ ℂ) (k : ℕ) (a : ZMod 4) : Matrix κ κ ℂ := specProj (V k)ᴴ a

/-- **The 27B configuration of a clock family** `V` (paper Section 6.3, RIGIDITY_ALLD.md 1.3): `Q_x` is the
spectral projection of `E_k = V_k^*` for the eigenvalue `i^a`, where `x = k - d a`. -/
def Qcfg (d : ℕ) (V : ℕ → Matrix κ κ ℂ) (x : ZMod (4 * d)) : Matrix κ κ ℂ :=
  Qs V (site d x) (label d x)

lemma Qcfg_qd (V : ℕ → Matrix κ κ ℂ) {k : ℕ} (hk : k < d) (a : ZMod 4) :
    Qcfg d V (qd d k a) = Qs V k a := by
  rw [Qcfg, site_qd hk, label_qd hk]

variable {V : ℕ → Matrix κ κ ℂ}

lemma E_pow_four (hV4 : ∀ k, V k ^ 4 = 1) (k : ℕ) : (V k)ᴴ ^ 4 = 1 := by
  rw [← conjTranspose_pow, hV4, conjTranspose_one]

lemma Qs_isProj (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) (k : ℕ) (a : ZMod 4) :
    IsProj (Qs V k a) :=
  ⟨specProj_isHermitian (E_pow_four hV4 k) (hV k).conjTranspose a, specProj_sq (E_pow_four hV4 k) a⟩

lemma sum_Qs (V : ℕ → Matrix κ κ ℂ) (k : ℕ) : ∑ a : ZMod 4, Qs V k a = 1 := sum_specProj _

/-- The spectral projections of a clock family form a 27B configuration. -/
theorem Qcfg_isConfig (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) :
    IsConfig27B d (Qcfg d V) := by
  refine ⟨fun x => Qs_isProj hV hV4 _ _, fun k hk => ?_⟩
  simp_rw [Qcfg_qd V hk]
  exact sum_Qs V k

/-- `E_k = ∑_a i^a Q_{k,a}`. -/
lemma Vh_eq_sum (V : ℕ → Matrix κ κ ℂ) (k : ℕ) : (V k)ᴴ = ∑ b : ZMod 4, iz b • Qs V k b :=
  (sum_iz_smul_specProj _).symm

/-- `V_k = ∑_a i^{-a} Q_{k,a}`. -/
lemma V_eq_sum (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) (k : ℕ) :
    V k = ∑ a : ZMod 4, iz (-a) • Qs V k a := by
  have h := congrArg conjTranspose (Vh_eq_sum V k)
  rw [conjTranspose_conjTranspose] at h
  rw [h, conjTranspose_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [conjTranspose_smul, (Qs_isProj hV hV4 k a).1.eq, Complex.star_def, conj_iz]

omit [DecidableEq κ] in
lemma ntr_add (X Y : Matrix κ κ ℂ) : ntr (X + Y) = ntr X + ntr Y := by
  rw [ntr, ntr, ntr, trace_add, add_div]

omit [DecidableEq κ] in
lemma ntr_smul (c : ℂ) (X : Matrix κ κ ℂ) : ntr (c • X) = c * ntr X := by
  rw [ntr, ntr, trace_smul, smul_eq_mul, mul_div_assoc]

omit [DecidableEq κ] in
lemma ntr_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix κ κ ℂ) :
    ntr (∑ i ∈ s, f i) = ∑ i ∈ s, ntr (f i) := by
  rw [ntr, trace_sum, sum_div]
  rfl

omit [DecidableEq κ] in
/-- `τ(P Q)` is real for Hermitian `P, Q`. -/
lemma ntr_mul_ofReal_re {P Q : Matrix κ κ ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ((ntr (P * Q)).re : ℂ) = ntr (P * Q) := by
  apply Complex.conj_eq_iff_re.1
  rw [conj_ntr, conjTranspose_mul, hP.eq, hQ.eq, ntr_mul_comm]

/-- `tr(V_j V_k^*) = ∑_{a,b} i^{b-a} τ(Q_{j,a} Q_{k,b})`. -/
lemma ntr_V_mul_V (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) (j k : ℕ) :
    ntr (V j * (V k)ᴴ) = ∑ a : ZMod 4, ∑ b : ZMod 4, iz (b - a) * ntr (Qs V j a * Qs V k b) := by
  rw [V_eq_sum hV hV4 j, Vh_eq_sum V k, Finset.sum_mul_sum, ntr_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [ntr_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [smul_mul_smul_comm, ntr_smul, ← iz_add, neg_add_eq_sub]

/-- The pair couplings of a clock family, `π_{jk}(t) = ∑_a τ(Q_{j,a} Q_{k,a+t})`. -/
def piS (V : ℕ → Matrix κ κ ℂ) (j k : ℕ) (t : ZMod 4) : ℝ :=
  ∑ a : ZMod 4, (ntr (Qs V j a * Qs V k (a + t))).re

lemma piQ_Qcfg (V : ℕ → Matrix κ κ ℂ) {j k : ℕ} (hj : j < d) (hk : k < d) (t : ZMod 4) :
    piQ d (Qcfg d V) j k t = piS V j k t := by
  unfold piQ piS
  refine sum_congr rfl fun a _ => ?_
  rw [Qcfg_qd V hj, Qcfg_qd V hk]

lemma hd_iz_re (n : ℕ) :
    (hd d n * iz 0).re = secd d n ∧ (hd d n * iz 1).re = cscd d n ∧
      (hd d n * iz 2).re = -secd d n ∧ (hd d n * iz 3).re = -cscd d n := by
  obtain ⟨h0, h1, h2, h3⟩ := iz_values
  rw [h0, h1, h2, h3]
  simp [hd]

/-- **The `F` summand of a pair** (paper Lemma 3.1, operator form):
`Re[h_n tr(V_j V_k^*)] = sec ψ_n (π_{jk}(0) - π_{jk}(2)) + csc ψ_n (π_{jk}(1) - π_{jk}(3))`. -/
lemma re_hd_ntr (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) (n j k : ℕ) :
    (hd d n * ntr (V j * (V k)ᴴ)).re
      = secd d n * (piS V j k 0 - piS V j k 2) + cscd d n * (piS V j k 1 - piS V j k 3) := by
  rw [ntr_V_mul_V hV hV4, mul_sum, re_sum]
  have hreal : ∀ a b, ntr (Qs V j a * Qs V k b) = ((ntr (Qs V j a * Qs V k b)).re : ℂ) :=
    fun a b => (ntr_mul_ofReal_re (Qs_isProj hV hV4 j a).1 (Qs_isProj hV hV4 k b).1).symm
  have step : ∀ a : ZMod 4, (hd d n * ∑ b : ZMod 4, iz (b - a) * ntr (Qs V j a * Qs V k b)).re
      = ∑ t : ZMod 4, (hd d n * iz t).re * (ntr (Qs V j a * Qs V k (a + t))).re := by
    intro a
    rw [mul_sum, re_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (-a)) _ _ (fun b => ?_)
    simp only [Equiv.coe_addLeft]
    rw [hreal a b, ← mul_assoc, re_mul_ofReal, neg_add_eq_sub, add_sub_cancel]
  simp_rw [step]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_zmod4]
  obtain ⟨h0, h1, h2, h3⟩ := hd_iz_re (d := d) n
  rw [h0, h1, h2, h3]
  unfold piS
  ring

/-! ### Reindexing pairs -/

/-- Pairs `(j, k = j + m)` with `1 ≤ m`, `k < d`. -/
lemma sum_Ico_range_sub {M : Type*} [AddCommMonoid M] (Φ : ℕ → ℕ → M) (d : ℕ) :
    ∑ m ∈ Ico 1 d, ∑ j ∈ range (d - m), Φ m j = ∑ k ∈ range d, ∑ j ∈ range k, Φ (k - j) j := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun p => ⟨p.2 + p.1, p.2⟩) (fun p => ⟨p.1 - p.2, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, j⟩ h
    simp only [mem_sigma, mem_Ico, mem_range] at h ⊢
    omega
  · rintro ⟨k, j⟩ h
    simp only [mem_sigma, mem_Ico, mem_range] at h ⊢
    omega
  · rintro ⟨m, j⟩ h
    simp only [mem_sigma, mem_Ico, mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨k, j⟩ h
    simp only [mem_sigma, mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨m, j⟩ _
    rw [Nat.add_sub_cancel_left]

/-! ### QD-L7 -/

/-- **QD-L7 (the linear form).** For order-4 unitaries `V_0, …, V_{d-1}` and their 27B configuration `Q`,
`F(V) = ∑_{m=1}^{d-1} csc(π m/(2d)) N(m)`, where `N(m) = C(m - d) - C(m + d)` is the net `B → A` pair
count. -/
theorem clockF_eq_csc [NeZero d] (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) :
    clockF d V = ∑ m ∈ Ico 1 d, cscd d m * Nnet d (Qcfg d V) m := by
  have hd0 : d ≠ 0 := NeZero.ne d
  set π := piQ d (Qcfg d V) with hπ
  -- the left side as a sum over pairs
  have hL : clockF d V = ∑ k ∈ range d, ∑ j ∈ range k,
      (cscd d (k - j) * (π j (j + (k - j)) 1 - π j (j + (k - j)) 3)
        + secd d (k - j) * (π j (j + (k - j)) 0 - π j (j + (k - j)) 2)) := by
    unfold clockF
    refine sum_congr rfl fun k hk => sum_congr rfl fun j hj => ?_
    have hk' := mem_range.1 hk
    have hj' := mem_range.1 hj
    rw [re_hd_ntr hV hV4, show j + (k - j) = k by omega, hπ, piQ_Qcfg V (by omega) hk',
      piQ_Qcfg V (by omega) hk', piQ_Qcfg V (by omega) hk', piQ_Qcfg V (by omega) hk']
    ring
  -- the right side
  have hR : ∑ m ∈ Ico 1 d, cscd d m * Nnet d (Qcfg d V) m = ∑ m ∈ Ico 1 d, ∑ j ∈ range (d - m),
      (cscd d m * (π j (j + m) 1 - π j (j + m) 3) + secd d m * (π j (j + m) 0 - π j (j + m) 2)) := by
    have h1 : ∀ m ∈ Ico 1 d, cscd d m * Nnet d (Qcfg d V) m
        = ∑ j ∈ range (d - m), cscd d m * (π j (j + m) 1 - π j (j + m) 3)
          + ∑ j ∈ range m, cscd d m * (π j (j + (d - m)) 0 - π j (j + (d - m)) 2) := by
      intro m hm
      rw [Nnet_pair _ (le_of_lt (mem_Ico.1 hm).2), mul_add, mul_sum, mul_sum]
    rw [sum_congr rfl h1, sum_add_distrib]
    -- reflect the second sum, `m ↦ d - m`
    have h2 : ∑ m ∈ Ico 1 d, ∑ j ∈ range m, cscd d m * (π j (j + (d - m)) 0 - π j (j + (d - m)) 2)
        = ∑ m ∈ Ico 1 d, ∑ j ∈ range (d - m), secd d m * (π j (j + m) 0 - π j (j + m) 2) := by
      rw [← sum_Ico_reflect' (fun m => ∑ j ∈ range m,
        cscd d m * (π j (j + (d - m)) 0 - π j (j + (d - m)) 2)) d]
      refine sum_congr rfl fun m hm => ?_
      have hm' := mem_Ico.1 hm
      rw [Nat.sub_sub_self (le_of_lt hm'.2), cscd_reflect hd0 (le_of_lt hm'.2)]
    rw [h2, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
  rw [hL, hR, sum_Ico_range_sub (fun m j =>
    cscd d m * (π j (j + m) 1 - π j (j + m) 3) + secd d m * (π j (j + m) 0 - π j (j + m) 2)) d]

/-! ### Properties of `N(m)` for every 27B configuration (RIGIDITY_ALLD.md 1.4) -/

section NetCounts

open scoped ComplexOrder

variable {Q : ZMod (4 * d) → Matrix κ κ ℂ}

lemma ntr_one_eq [Nonempty κ] : ntr (1 : Matrix κ κ ℂ) = 1 := by
  rw [ntr, trace_one, div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

omit [DecidableEq κ] in
/-- `τ(P R) ≥ 0` (real part) for projections `P, R`. -/
lemma ntr_mul_re_nonneg {P R : Matrix κ κ ℂ} (hP : IsProj P) (hR : IsProj R) :
    0 ≤ (ntr (P * R)).re := by
  have h : trace (P * R) = trace ((R * P)ᴴ * (R * P)) := by
    rw [conjTranspose_mul, hP.1.eq, hR.1.eq]
    rw [show P * R * (R * P) = P * R * P by
      rw [← Matrix.mul_assoc (P * R) R P, Matrix.mul_assoc P R R, hR.2]]
    rw [trace_mul_comm (P * R) P, ← Matrix.mul_assoc, hP.2]
  have hnn : 0 ≤ trace ((R * P)ᴴ * (R * P)) :=
    (posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hre : 0 ≤ (trace (P * R)).re := by
    rw [h]
    exact (Complex.nonneg_iff.1 hnn).1
  rw [ntr, Complex.div_natCast_re]
  exact div_nonneg hre (Nat.cast_nonneg _)

omit [DecidableEq κ] in
lemma Ccorr_neg [NeZero d] (Q : ZMod (4 * d) → Matrix κ κ ℂ) (n : ZMod (4 * d)) :
    Ccorr d Q (-n) = Ccorr d Q n := by
  unfold Ccorr
  refine Fintype.sum_equiv (Equiv.subRight n) _ _ (fun u => ?_)
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [ntr_mul_comm, sub_eq_add_neg]

omit [DecidableEq κ] in
/-- `N(2d - m) = N(m)` (RIGIDITY_ALLD.md 1.4(a)). -/
theorem Nnet_reflect [NeZero d] (Q : ZMod (4 * d) → Matrix κ κ ℂ) {m : ℕ} (hm : m ≤ 2 * d) :
    Nnet d Q (2 * d - m) = Nnet d Q m := by
  unfold Nnet
  rw [Nat.cast_sub hm]
  push_cast
  have e1 : (2 * (d : ZMod (4 * d)) - m - d) = -((m : ZMod (4 * d)) - d) := by ring
  have h4 : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self _
  push_cast at h4
  have e2 : (2 * (d : ZMod (4 * d)) - m + d) = -((m : ZMod (4 * d)) + d) := by
    linear_combination h4
  rw [e1, e2, Ccorr_neg, Ccorr_neg]

/-- The four projections at one site form a projective measurement (indexed by `ℤ/4`). -/
lemma site_isPVM (hQ : IsConfig27B d Q) {k : ℕ} (hk : k < d) : IsPVM (fun a : ZMod 4 => Q (qd d k a)) :=
  ⟨fun _ => hQ.1 _, hQ.2 k hk⟩

/-- `N(d) = d` (RIGIDITY_ALLD.md 1.4(a)). -/
theorem Nnet_d [NeZero d] [Nonempty κ] (hQ : IsConfig27B d Q) : Nnet d Q d = d := by
  unfold Nnet Ccorr
  rw [sub_self, sum_zmod4d, sum_zmod4d]
  have h0 : ∀ k ∈ range d, ∑ a : ZMod 4, (ntr (Q (qd d k a) * Q (qd d k a + 0))).re = 1 := by
    intro k hk
    simp_rw [add_zero, (hQ.1 _).2]
    rw [← re_sum, ← ntr_sum, hQ.2 k (mem_range.1 hk), ntr_one_eq, Complex.one_re]
  have h2 : ∀ k ∈ range d, ∑ a : ZMod 4, (ntr (Q (qd d k a) * Q (qd d k a + ((d : ZMod (4 * d)) + d)))).re
      = 0 := by
    intro k hk
    refine sum_eq_zero fun a _ => ?_
    have e : qd d k a + ((d : ZMod (4 * d)) + d) = qd d k (a + 2) := by
      rw [← add_assoc, qd_add_d, qd_add_d, sub_sub, show (1 : ZMod 4) + 1 = -2 by decide, sub_neg_eq_add]
    rw [e, (site_isPVM hQ (mem_range.1 hk)).mul_eq_zero (show a ≠ a + 2 by
      intro h
      have : (2 : ZMod 4) = 0 := by linear_combination -h
      exact absurd this (by decide)), ntr, trace_zero, zero_div, Complex.zero_re]
  rw [sum_congr rfl h0, sum_congr rfl h2, sum_const, card_range, sum_const_zero]
  simp

lemma piQ_nonneg (hQ : IsConfig27B d Q) (j k : ℕ) (t : ZMod 4) : 0 ≤ piQ d Q j k t :=
  sum_nonneg fun _ _ => ntr_mul_re_nonneg (hQ.1 _) (hQ.1 _)

lemma sum_piQ [Nonempty κ] (hQ : IsConfig27B d Q) {j k : ℕ} (hj : j < d) (hk : k < d) :
    ∑ t : ZMod 4, piQ d Q j k t = 1 := by
  unfold piQ
  rw [sum_comm]
  have e : ∀ b : ZMod 4, ∑ t : ZMod 4, (ntr (Q (qd d j b) * Q (qd d k (b + t)))).re
      = (ntr (Q (qd d j b))).re := by
    intro b
    rw [← re_sum, ← ntr_sum, ← Matrix.mul_sum]
    have : ∑ t : ZMod 4, Q (qd d k (b + t)) = 1 := by
      rw [← hQ.2 k hk]
      exact Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun t => rfl)
    rw [this, Matrix.mul_one]
  rw [sum_congr rfl fun b _ => e b, ← re_sum, ← ntr_sum, hQ.2 j hj, ntr_one_eq, Complex.one_re]

lemma rho_le_one [Nonempty κ] (hQ : IsConfig27B d Q) {j k : ℕ} (hj : j < d) (hk : k < d) :
    piQ d Q j k 0 + piQ d Q j k 1 - piQ d Q j k 2 - piQ d Q j k 3 ≤ 1 := by
  have hs := sum_piQ hQ hj hk
  rw [sum_zmod4] at hs
  have h2 := piQ_nonneg hQ j k 2
  have h3 := piQ_nonneg hQ j k 3
  linarith

/-- **`N(s) + N(d - s) ≤ d`** (RIGIDITY_ALLD.md eq. (1.2), QD2-R2) for every 27B configuration. -/
theorem Nnet_add_reflect_le [NeZero d] [Nonempty κ] (hQ : IsConfig27B d Q) {s : ℕ} (hs : s ≤ d) :
    Nnet d Q s + Nnet d Q (d - s) ≤ d := by
  rw [Nnet_pair Q hs, Nnet_pair Q (Nat.sub_le d s), Nat.sub_sub_self hs]
  have e : ∑ j ∈ range (d - s), (piQ d Q j (j + s) 1 - piQ d Q j (j + s) 3)
      + ∑ j ∈ range s, (piQ d Q j (j + (d - s)) 0 - piQ d Q j (j + (d - s)) 2)
      + (∑ j ∈ range s, (piQ d Q j (j + (d - s)) 1 - piQ d Q j (j + (d - s)) 3)
        + ∑ j ∈ range (d - s), (piQ d Q j (j + s) 0 - piQ d Q j (j + s) 2))
      = ∑ j ∈ range (d - s), (piQ d Q j (j + s) 0 + piQ d Q j (j + s) 1 - piQ d Q j (j + s) 2
          - piQ d Q j (j + s) 3)
        + ∑ j ∈ range s, (piQ d Q j (j + (d - s)) 0 + piQ d Q j (j + (d - s)) 1
          - piQ d Q j (j + (d - s)) 2 - piQ d Q j (j + (d - s)) 3) := by
    rw [show ∀ a b c e : ℝ, a + b + (c + e) = (a + e) + (b + c) by intros; ring,
      ← sum_add_distrib, ← sum_add_distrib]
    congr 1
    · refine sum_congr rfl fun j _ => ?_
      ring
    · refine sum_congr rfl fun j _ => ?_
      ring
  rw [e]
  have b1 : ∑ j ∈ range (d - s), (piQ d Q j (j + s) 0 + piQ d Q j (j + s) 1 - piQ d Q j (j + s) 2
      - piQ d Q j (j + s) 3) ≤ ∑ j ∈ range (d - s), (1 : ℝ) :=
    sum_le_sum fun j hj => rho_le_one hQ (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega)
  have b2 : ∑ j ∈ range s, (piQ d Q j (j + (d - s)) 0 + piQ d Q j (j + (d - s)) 1
      - piQ d Q j (j + (d - s)) 2 - piQ d Q j (j + (d - s)) 3) ≤ ∑ j ∈ range s, (1 : ℝ) :=
    sum_le_sum fun j hj => rho_le_one hQ (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega)
  have hc : ∑ j ∈ range (d - s), (1 : ℝ) + ∑ j ∈ range s, (1 : ℝ) = d := by
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [← Nat.cast_add, Nat.sub_add_cancel hs]
  linarith

end NetCounts

/-! ### Every 27B configuration is the configuration of a clock family -/

section FamilyOfConfig

variable {Q : ZMod (4 * d) → Matrix κ κ ℂ}

lemma IsPVM.sum_smul_pow {P : ZMod 4 → Matrix κ κ ℂ} (hP : IsPVM P) (c : ZMod 4 → ℂ) (m : ℕ) :
    (∑ a, c a • P a) ^ m = ∑ a, c a ^ m • P a := by
  induction m with
  | zero => simp [hP.2]
  | succ m ih => rw [pow_succ, ih, hP.sum_mul_sum]; simp only [← pow_succ]

lemma iz_pow_val (b t : ZMod 4) : iz b ^ t.val = iz (b * t) := by
  rw [iz, iz, ← pow_mul, ZMod.val_mul, I_pow_mod]

/-- The clock family of a 27B configuration: `V_k = ∑_a i^{-a} Q_{k - d a}` for `k < d`
(and `V_k = 1` for `k ≥ d`). -/
def famOf (d : ℕ) (Q : ZMod (4 * d) → Matrix κ κ ℂ) (k : ℕ) : Matrix κ κ ℂ :=
  if k < d then ∑ a : ZMod 4, iz (-a) • Q (qd d k a) else 1

lemma famOf_conjTranspose (hQ : IsConfig27B d Q) {k : ℕ} (hk : k < d) :
    (famOf d Q k)ᴴ = ∑ a : ZMod 4, iz a • Q (qd d k a) := by
  rw [famOf, if_pos hk, (site_isPVM hQ hk).sum_smul_conjTranspose]
  refine sum_congr rfl fun a _ => ?_
  rw [conj_iz, neg_neg]

lemma famOf_unitary (hQ : IsConfig27B d Q) (k : ℕ) : IsUnitaryM (famOf d Q k) := by
  by_cases hk : k < d
  · unfold IsUnitaryM
    rw [famOf_conjTranspose hQ hk, famOf, if_pos hk, (site_isPVM hQ hk).sum_mul_sum, ← hQ.2 k hk]
    refine sum_congr rfl fun a _ => ?_
    rw [← iz_add, add_neg_cancel, iz_zero, one_smul]
  · unfold IsUnitaryM
    rw [famOf, if_neg hk, conjTranspose_one, Matrix.one_mul]

lemma famOf_pow_four (hQ : IsConfig27B d Q) (k : ℕ) : famOf d Q k ^ 4 = 1 := by
  by_cases hk : k < d
  · rw [famOf, if_pos hk, (site_isPVM hQ hk).sum_smul_pow, ← hQ.2 k hk]
    refine sum_congr rfl fun a _ => ?_
    rw [iz, ← pow_mul, mul_comm, pow_mul, Complex.I_pow_four, one_pow, one_smul]
  · rw [famOf, if_neg hk, one_pow]

/-- The spectral projections of `E_k = V_k^*` for the family of a configuration are the `Q_{k - d a}`. -/
lemma Qs_famOf (hQ : IsConfig27B d Q) {k : ℕ} (hk : k < d) (a : ZMod 4) :
    Qs (famOf d Q) k a = Q (qd d k a) := by
  have hP := site_isPVM hQ hk
  rw [Qs, famOf_conjTranspose hQ hk, specProj]
  have e1 : ∀ t : ZMod 4, iz (-(a * t)) • (∑ b : ZMod 4, iz b • Q (qd d k b)) ^ t.val
      = ∑ b : ZMod 4, (iz (-(a * t)) * iz (b * t)) • Q (qd d k b) := by
    intro t
    rw [hP.sum_smul_pow, smul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [iz_pow_val, smul_smul]
  simp_rw [e1]
  rw [sum_comm, smul_sum]
  have e2 : ∀ b : ZMod 4, (1 / 4 : ℂ) • ∑ t : ZMod 4, (iz (-(a * t)) * iz (b * t)) • Q (qd d k b)
      = (if b = a then (1 : ℂ) else 0) • Q (qd d k b) := by
    intro b
    rw [← sum_smul, smul_smul]
    congr 1
    have h3 : ∑ t : ZMod 4, iz (-(a * t)) * iz (b * t) = ∑ t : ZMod 4, iz ((b - a) * t) := by
      refine sum_congr rfl fun t _ => ?_
      rw [← iz_add]
      congr 1
      ring
    rw [h3, sum_iz_mul]
    split_ifs with h1 h2 h2
    · norm_num
    · exact absurd (sub_eq_zero.1 h1) h2
    · exact absurd (sub_eq_zero.2 h2) h1
    · norm_num
  simp_rw [e2, ite_smul, one_smul, zero_smul]
  rw [sum_ite_eq']
  simp

/-- **Every 27B configuration is the configuration of a clock family** (the converse of
`Qcfg_isConfig`): `Q = Qcfg (famOf Q)`. -/
theorem Qcfg_famOf [NeZero d] (hQ : IsConfig27B d Q) : Qcfg d (famOf d Q) = Q := by
  funext x
  rw [Qcfg, Qs_famOf hQ (site_lt (Nat.pos_of_ne_zero (NeZero.ne d)) x), qd_site_label]

end FamilyOfConfig

end

end OQP27.Red
