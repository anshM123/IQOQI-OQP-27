import OQP27.ReductionClock

/-!
# OQP 27B, module L2 (reduction), part 4: the Q-configuration and the linear (csc) form

Sources: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 6.3 (eq. (projform));
`iqoqi/programs/oqp27B_all/SHARED_LEMMAS.md` [QD] (QD-L7) and [E2] (E2-R2);
`iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, items 1.3 and 1.4.

For order-4 unitaries `V_0, …, V_{d-1}` put `E_k = V_k^*` and, for `x ∈ ℤ_{4d}` written uniquely as
`x = k - d a` (`0 ≤ k ≤ d-1`, `a ∈ ℤ/4`), let `Q_x` be the spectral projection of `E_k` for the eigenvalue
`i^a`. Then `A_x = Q_x`, `B_x = Q_{x+d}`, `C(n) = ∑_{u ∈ ℤ_{4d}} τ(Q_u Q_{u+n})` and the net `B → A` pair
count `N(m) = C(m - d) - C(m + d)` (RIGIDITY_ALLD.md 1.4).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.specProj_*`: the spectral projections of an order-4 unitary, by explicit functional
  calculus `Q_a = (1/4) ∑_t i^{-a t} E^t`.
* `OQP27.Red.Qcfg_isConfig`: `Q` is a 27B configuration (projections; each residue class mod `d` is a
  4-outcome PVM).
* `OQP27.Red.Nnet_pair`: the pair form of `N(m)` (RIGIDITY_ALLD.md 1.4(c)).
* `OQP27.Red.clockF_eq_csc` (**QD-L7**): `F(V) = ∑_{m=1}^{d-1} csc(π m/(2d)) N(m)`.
* `OQP27.Red.Nnet_d`, `OQP27.Red.Nnet_reflect` (1.4(a)): `N(d) = d`, `N(2d - m) = N(m)`.
* `OQP27.Red.Nnet_add_reflect_le` (1.4(c), eq. (1.2)): `N(s) + N(d - s) ≤ d`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

/-! ### Characters of `ℤ/4` -/

/-- `i^a` for `a ∈ ℤ/4`. -/
def iz (a : ZMod 4) : ℂ := I ^ a.val

lemma I_pow_mod (n : ℕ) : I ^ (n % 4) = I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

lemma iz_add (a b : ZMod 4) : iz (a + b) = iz a * iz b := by
  rw [iz, iz, iz, ZMod.val_add, I_pow_mod, pow_add]

lemma iz_zero : iz 0 = 1 := by simp [iz]

lemma iz_ne_zero (a : ZMod 4) : iz a ≠ 0 := pow_ne_zero _ Complex.I_ne_zero

lemma iz_neg (a : ZMod 4) : iz (-a) = (iz a)⁻¹ := by
  have h := iz_add a (-a)
  rw [add_neg_cancel, iz_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

lemma conj_iz (a : ZMod 4) : conj (iz a) = iz (-a) := by
  rw [iz_neg, iz, map_pow, Complex.conj_I, ← inv_pow, Complex.inv_I]

lemma iz_ne_one {a : ZMod 4} (ha : a ≠ 0) : iz a ≠ 1 := by
  unfold iz
  apply Complex.isPrimitiveRoot_I.pow_ne_one_of_pos_of_lt
  · rwa [Ne, ZMod.val_eq_zero]
  · exact ZMod.val_lt a

/-- Orthogonality: `∑_t i^{c t} = 4 [c = 0]`. -/
lemma sum_iz_mul (c : ZMod 4) : ∑ t : ZMod 4, iz (c * t) = if c = 0 then 4 else 0 := by
  split_ifs with hc
  · subst hc
    simp [iz_zero]
  · have key : iz c * ∑ t : ZMod 4, iz (c * t) = ∑ t : ZMod 4, iz (c * t) := by
      rw [mul_sum]
      have e : ∀ t : ZMod 4, iz c * iz (c * t) = iz (c * (t + 1)) := by
        intro t
        rw [← iz_add]
        ring_nf
      simp_rw [e]
      exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => rfl)
    have h1 : (iz c - 1) * ∑ t : ZMod 4, iz (c * t) = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) (iz_ne_one hc)
    · exact h

lemma iz_values : iz 0 = 1 ∧ iz 1 = I ∧ iz 2 = -1 ∧ iz 3 = -I := by
  refine ⟨iz_zero, ?_, ?_, ?_⟩
  · rw [iz, show (1 : ZMod 4).val = 1 from rfl, pow_one]
  · rw [iz, show (2 : ZMod 4).val = 2 from rfl, Complex.I_sq]
  · rw [iz, show (3 : ZMod 4).val = 3 from rfl, pow_succ, Complex.I_sq]
    ring

/-! ### Spectral projections of an order-4 unitary -/

section Spectral

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The spectral projection of an order-4 unitary `E` for the eigenvalue `i^a`:
`Q_a = (1/4) ∑_{t ∈ ℤ/4} i^{-a t} E^t`. -/
def specProj (E : Matrix κ κ ℂ) (a : ZMod 4) : Matrix κ κ ℂ :=
  (1 / 4 : ℂ) • ∑ t : ZMod 4, iz (-(a * t)) • E ^ t.val

variable {E : Matrix κ κ ℂ}

lemma pow_mod_four (hE : E ^ 4 = 1) (n : ℕ) : E ^ (n % 4) = E ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hE, one_pow, mul_one]

lemma pow_val_add (hE : E ^ 4 = 1) (s t : ZMod 4) : E ^ (s + t).val = E ^ s.val * E ^ t.val := by
  rw [ZMod.val_add, pow_mod_four hE, pow_add]

lemma specProj_mul (hE : E ^ 4 = 1) (a b : ZMod 4) :
    specProj E a * specProj E b = if a = b then specProj E a else 0 := by
  unfold specProj
  rw [smul_mul_smul_comm, Finset.sum_mul_sum]
  simp_rw [smul_mul_smul_comm, ← pow_val_add hE]
  -- reindex the inner sum by `u = s + t`
  have e1 : ∀ s : ZMod 4, ∑ t : ZMod 4, (iz (-(a * s)) * iz (-(b * t))) • E ^ (s + t).val
      = ∑ u : ZMod 4, (iz (-(b * u)) * iz ((b - a) * s)) • E ^ u.val := by
    intro s
    refine Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => ?_)
    simp only [Equiv.coe_addLeft]
    congr 1
    rw [← iz_add, ← iz_add]
    congr 1
    ring
  simp_rw [e1]
  rw [sum_comm]
  simp_rw [← sum_smul, ← mul_sum, sum_iz_mul, sub_eq_zero]
  split_ifs with h1 h2 h2
  · subst h1
    rw [smul_sum, smul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

lemma specProj_sq (hE : E ^ 4 = 1) (a : ZMod 4) : specProj E a * specProj E a = specProj E a := by
  rw [specProj_mul hE, if_pos rfl]

lemma specProj_orth (hE : E ^ 4 = 1) {a b : ZMod 4} (hab : a ≠ b) : specProj E a * specProj E b = 0 := by
  rw [specProj_mul hE, if_neg hab]

lemma sum_specProj (E : Matrix κ κ ℂ) : ∑ a : ZMod 4, specProj E a = 1 := by
  unfold specProj
  rw [← smul_sum, sum_comm]
  simp_rw [← sum_smul]
  have e : ∀ t : ZMod 4, ∑ a : ZMod 4, iz (-(a * t)) = if t = 0 then 4 else 0 := by
    intro t
    calc ∑ a : ZMod 4, iz (-(a * t)) = ∑ a : ZMod 4, iz (-t * a) :=
          sum_congr rfl fun a _ => by congr 1; ring
      _ = if -t = 0 then 4 else 0 := sum_iz_mul (-t)
      _ = if t = 0 then 4 else 0 := by simp only [neg_eq_zero]
  simp_rw [e]
  rw [sum_eq_single (0 : ZMod 4)]
  · simp only [if_true, ZMod.val_zero, pow_zero, smul_smul]
    norm_num
  · intro t _ ht
    rw [if_neg ht, zero_smul]
  · intro h
    exact absurd (mem_univ _) h

lemma sum_iz_smul_specProj (E : Matrix κ κ ℂ) : ∑ a : ZMod 4, iz a • specProj E a = E := by
  unfold specProj
  have h1 : ∀ a : ZMod 4, iz a • ((1 / 4 : ℂ) • ∑ t : ZMod 4, iz (-(a * t)) • E ^ t.val)
      = ∑ t : ZMod 4, (1 / 4 * iz ((1 - t) * a)) • E ^ t.val := by
    intro a
    rw [smul_sum, smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_comm (iz a), mul_assoc, ← iz_add]
    congr 2
    ring
  rw [sum_congr rfl fun a _ => h1 a, sum_comm]
  simp_rw [← sum_smul, ← mul_sum, sum_iz_mul, sub_eq_zero]
  rw [sum_eq_single (1 : ZMod 4)]
  · rw [if_pos rfl, show (1 : ZMod 4).val = 1 from rfl, pow_one]
    norm_num
  · intro t _ ht
    rw [if_neg (Ne.symm ht), mul_zero, zero_smul]
  · intro h
    exact absurd (mem_univ _) h

lemma specProj_isHermitian (hE : E ^ 4 = 1) (hU : IsUnitaryM E) (a : ZMod 4) :
    (specProj E a).IsHermitian := by
  have hEh : Eᴴ = E ^ 3 := by
    have h := hU
    unfold IsUnitaryM at h
    calc Eᴴ = Eᴴ * E ^ 4 := by rw [hE, mul_one]
      _ = Eᴴ * E * E ^ 3 := by rw [mul_assoc, ← pow_succ']
      _ = E ^ 3 := by rw [h, one_mul]
  unfold Matrix.IsHermitian specProj
  rw [conjTranspose_smul, conjTranspose_sum]
  simp_rw [conjTranspose_smul, conjTranspose_pow, hEh, ← pow_mul]
  have e : ∀ t : ZMod 4, star (iz (-(a * t))) • E ^ (3 * t.val) = iz (-(a * (-t))) • E ^ (-t).val := by
    intro t
    rw [Complex.star_def, conj_iz]
    congr 1
    · congr 1
      ring
    · rw [← pow_mod_four hE (3 * t.val), ← pow_mod_four hE (-t).val]
      congr 1
      rw [ZMod.neg_val]
      split_ifs with ht
      · subst ht
        simp
      · have h1 := ZMod.val_lt t
        have h2 : t.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
        omega
  simp_rw [e]
  have hs : star (1 / 4 : ℂ) = 1 / 4 := by simp
  rw [hs]
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ZMod 4)) _ _ (fun t => rfl)

end Spectral

/-! ### Points of `ℤ_{4d}`: `x = k - d a` -/

section Points

variable {d : ℕ}

/-- The point `x = k - d a` of `ℤ_{4d}`, written in the normal form `k + d · (-a)`. -/
def qd (d k : ℕ) (a : ZMod 4) : ZMod (4 * d) := ((k + d * (-a).val : ℕ) : ZMod (4 * d))

/-- The site `k` of `x ∈ ℤ_{4d}` (`x = k - d a`, `0 ≤ k < d`). -/
def site (d : ℕ) (x : ZMod (4 * d)) : ℕ := x.val % d

/-- The label `a ∈ ℤ/4` of `x ∈ ℤ_{4d}` (`x = k - d a`). -/
def label (d : ℕ) (x : ZMod (4 * d)) : ZMod 4 := -((x.val / d : ℕ) : ZMod 4)

/-- `d · a` as an element of `ℤ_{4d}` (well defined for `a ∈ ℤ/4`). -/
def mu (d : ℕ) (a : ZMod 4) : ZMod (4 * d) := (d : ZMod (4 * d)) * (a.val : ZMod (4 * d))

lemma natCast_mod_four (n : ℕ) :
    (d : ZMod (4 * d)) * ((n % 4 : ℕ) : ZMod (4 * d)) = (d : ZMod (4 * d)) * (n : ZMod (4 * d)) := by
  have h := Nat.mod_add_div n 4
  have e : (d : ZMod (4 * d)) * (n : ZMod (4 * d))
      = (d : ZMod (4 * d)) * ((n % 4 : ℕ) : ZMod (4 * d))
        + ((4 * d : ℕ) : ZMod (4 * d)) * ((n / 4 : ℕ) : ZMod (4 * d)) := by
    conv_lhs => rw [← h]
    push_cast
    ring
  rw [e, ZMod.natCast_self, zero_mul, add_zero]

lemma mu_add (a b : ZMod 4) : mu d (a + b) = mu d a + mu d b := by
  unfold mu
  rw [ZMod.val_add, natCast_mod_four]
  push_cast
  ring

lemma mu_one : mu d 1 = d := by
  unfold mu
  rw [show (1 : ZMod 4).val = 1 from rfl]
  push_cast
  ring

lemma mu_zero : mu d 0 = 0 := by simp [mu]

lemma mu_neg (a : ZMod 4) : mu d (-a) = -mu d a := by
  have h := mu_add (d := d) a (-a)
  rw [add_neg_cancel, mu_zero] at h
  linear_combination -h

/-- The paper's form of the point: `x = k - d a`. -/
lemma qd_eq (k : ℕ) (a : ZMod 4) : qd d k a = (k : ZMod (4 * d)) - mu d a := by
  have h : ((k + d * (-a).val : ℕ) : ZMod (4 * d)) = (k : ZMod (4 * d)) + mu d (-a) := by
    unfold mu
    push_cast
    ring
  rw [qd, h, mu_neg]
  ring

lemma qd_add_nat (k n : ℕ) (a : ZMod 4) :
    qd d k a + (n : ZMod (4 * d)) = qd d (k + n) a := by
  rw [qd_eq, qd_eq]
  push_cast
  ring

lemma qd_sub_d (k : ℕ) (a : ZMod 4) : qd d k a - (d : ZMod (4 * d)) = qd d k (a + 1) := by
  rw [qd_eq, qd_eq, mu_add, mu_one]
  ring

lemma qd_add_d (k : ℕ) (a : ZMod 4) : qd d k a + (d : ZMod (4 * d)) = qd d k (a - 1) := by
  rw [qd_eq, qd_eq, sub_eq_add_neg a, mu_add, mu_neg, mu_one]
  ring

lemma qd_add_dd (k : ℕ) (a : ZMod 4) : qd d (k + d) a = qd d k (a - 1) := by
  rw [← qd_add_nat, qd_add_d]

lemma qd_val {k : ℕ} (hk : k < d) (a : ZMod 4) : (qd d k a).val = k + d * (-a).val := by
  rw [qd, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have := ZMod.val_lt (-a)
  have h3 : (-a).val ≤ 3 := by omega
  have : d * (-a).val ≤ d * 3 := Nat.mul_le_mul_left d h3
  omega

lemma site_qd {k : ℕ} (hk : k < d) (a : ZMod 4) : site d (qd d k a) = k := by
  rw [site, qd_val hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

lemma label_qd {k : ℕ} (hk : k < d) (a : ZMod 4) : label d (qd d k a) = a := by
  have hd : 0 < d := by omega
  rw [label, qd_val hk, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hk, zero_add,
    ZMod.natCast_zmod_val, neg_neg]

lemma site_lt (hd : 0 < d) (x : ZMod (4 * d)) : site d x < d := Nat.mod_lt _ hd

lemma qd_site_label [NeZero d] (x : ZMod (4 * d)) : qd d (site d x) (label d x) = x := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hx := ZMod.val_lt x
  have hq : x.val / d < 4 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    linarith
  have hl : (-label d x).val = x.val / d := by
    rw [label, neg_neg, ZMod.val_natCast, Nat.mod_eq_of_lt hq]
  rw [qd, hl, site, Nat.mod_add_div, ZMod.natCast_zmod_val]

/-- Sums over `ℤ_{4d}` as sums over sites `k < d` and labels `a ∈ ℤ/4`. -/
lemma sum_zmod4d [NeZero d] {M : Type*} [AddCommMonoid M] (f : ZMod (4 * d) → M) :
    ∑ x, f x = ∑ k ∈ range d, ∑ a : ZMod 4, f (qd d k a) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (site d x, label d x)) (fun p => qd d p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp only [mem_product, mem_range, mem_univ, and_true]
    exact site_lt hd x
  · intro p _
    exact mem_univ _
  · intro x _
    exact qd_site_label x
  · intro p hp
    simp only [mem_product, mem_range] at hp
    simp only [site_qd hp.1, label_qd hp.1]
  · intro x _
    simp only [qd_site_label x]

end Points

/-! ### 27B configurations and the net pair counts -/

section Config

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A **27B configuration**: projections `Q_x`, `x ∈ ℤ_{4d}`, such that for every site `k < d` the four
projections `Q_{k - d a}` (`a ∈ ℤ/4`) form a projective measurement. -/
def IsConfig27B (d : ℕ) (Q : ZMod (4 * d) → Matrix κ κ ℂ) : Prop :=
  (∀ x, IsProj (Q x)) ∧ ∀ k < d, ∑ a : ZMod 4, Q (qd d k a) = 1

/-- `C(n) = ∑_{u ∈ ℤ_{4d}} τ(Q_u Q_{u+n})` (the real part; the trace is real for projections). -/
def Ccorr (d : ℕ) [NeZero d] (Q : ZMod (4 * d) → Matrix κ κ ℂ) (n : ZMod (4 * d)) : ℝ :=
  ∑ u, (ntr (Q u * Q (u + n))).re

/-- **The net `B → A` pair count** `N(m) = C(m - d) - C(m + d)` (RIGIDITY_ALLD.md 1.4; with
`A_x = Q_x`, `B_x = Q_{x+d}` this is `∑_y τ(A_{y+m} B_y) - ∑_y τ(A_{y-m} B_y)`). -/
def Nnet (d : ℕ) [NeZero d] (Q : ZMod (4 * d) → Matrix κ κ ℂ) (m : ℕ) : ℝ :=
  Ccorr d Q ((m : ZMod (4 * d)) - d) - Ccorr d Q ((m : ZMod (4 * d)) + d)

/-- The pair couplings `π_{jk}(t) = ∑_b τ(Q_{j-db} Q_{k-d(b+t)})` (RIGIDITY_ALLD.md 1.4(c)). -/
def piQ (d : ℕ) (Q : ZMod (4 * d) → Matrix κ κ ℂ) (j k : ℕ) (t : ZMod 4) : ℝ :=
  ∑ b : ZMod 4, (ntr (Q (qd d j b) * Q (qd d k (b + t)))).re

omit [DecidableEq κ] in
lemma ntr_mul_comm (X Y : Matrix κ κ ℂ) : ntr (X * Y) = ntr (Y * X) := by
  rw [ntr, ntr, trace_mul_comm]

lemma neg_one_zmod4 : (-1 : ZMod 4) = 3 := by decide

omit [DecidableEq κ] in
/-- **Pair form of `N(m)`** (RIGIDITY_ALLD.md 1.4(c)): for `m ≤ d`,
`N(m) = ∑_{k-j=m} [π_{jk}(1) - π_{jk}(3)] + ∑_{k-j=d-m} [π_{jk}(0) - π_{jk}(2)]`. -/
theorem Nnet_pair [NeZero d] (Q : ZMod (4 * d) → Matrix κ κ ℂ) {m : ℕ} (hm : m ≤ d) :
    Nnet d Q m = ∑ j ∈ range (d - m), (piQ d Q j (j + m) 1 - piQ d Q j (j + m) 3)
      + ∑ j ∈ range m, (piQ d Q j (j + (d - m)) 0 - piQ d Q j (j + (d - m)) 2) := by
  unfold Nnet Ccorr
  rw [sum_zmod4d, sum_zmod4d, ← sum_sub_distrib]
  have hd' : range d = range ((d - m) + m) := by rw [Nat.sub_add_cancel hm]
  rw [hd', sum_range_add]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    unfold piQ
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    have e1 : qd d k a + ((m : ZMod (4 * d)) - d) = qd d (k + m) (a + 1) := by
      rw [← add_sub_assoc, qd_add_nat, qd_sub_d]
    have e2 : qd d k a + ((m : ZMod (4 * d)) + d) = qd d (k + m) (a + 3) := by
      rw [← add_assoc, qd_add_nat, qd_add_d, sub_eq_add_neg, neg_one_zmod4]
    rw [e1, e2]
  · refine sum_congr rfl fun j _ => ?_
    unfold piQ
    have e1 : ∀ a : ZMod 4, qd d (d - m + j) a + ((m : ZMod (4 * d)) - d) = qd d j a := by
      intro a
      rw [← add_sub_assoc, qd_add_nat, show d - m + j + m = j + d by omega, qd_add_dd, qd_sub_d,
        sub_add_cancel]
    have e2 : ∀ a : ZMod 4, qd d (d - m + j) a + ((m : ZMod (4 * d)) + d) = qd d j (a + 2) := by
      intro a
      rw [← add_assoc, qd_add_nat, show d - m + j + m = j + d by omega, qd_add_dd, qd_add_d]
      congr 1
      rw [sub_sub, show (1 : ZMod 4) + 1 = -2 by decide, sub_neg_eq_add]
    simp_rw [e1, e2]
    congr 1
    · refine sum_congr rfl fun a _ => ?_
      rw [ntr_mul_comm, add_zero, add_comm (d - m) j]
    · refine Fintype.sum_equiv (Equiv.addRight 2) _ _ (fun a => ?_)
      simp only [Equiv.coe_addRight]
      rw [ntr_mul_comm, add_comm (d - m) j, add_assoc a 2 2, show (2 : ZMod 4) + 2 = 0 by decide,
        add_zero]

end Config

end

end OQP27.Red
