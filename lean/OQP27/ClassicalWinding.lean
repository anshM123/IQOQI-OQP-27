import OQP27.ClassicalDefs

/-!
# The classical Theorem B for every `d` (module L7): cyclically ordered colourings

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Corollary `cor:monotone` (structure of cyclically
ordered colourings; the winding number `w = 1` gives adjacent intervals) and Lemma `lem:junctionineq` (the
junction inequality).

Let `A`, `B` be disjoint subsets of `ℤ_N` such that the colouring `(A, B, C = ℤ_N ∖ (A ∪ B))` is cyclically
ordered (`CycOrd A B`), and let `w = wind A B = #{x ∈ A : x - 1 ∈ B}` be its winding number. This file proves:

* `one_le_wind`: `w ≥ 1` if `A` is nonempty and `A ≠ ℤ_N` (Corollary `cor:monotone`, `w ≥ 1`);
* `eq_ico_of_wind_eq_one`: if `w = 1`, then `A = r + [0, |A|)` and `B = r + [-|B|, 0)` for some `r`
  (Corollary `cor:monotone`: the colourings with `w = 1` are the rotations of `([0, a), [-b, 0))`);
* `wind_count_le`: `#{x ∈ A : x + m ∈ B} ≤ (m - 1) w`, the counting step of the proof of Lemma
  `lem:junctionineq` (walking forward from `x ∈ A` to `x + m ∈ B` one leaves `A` at one of its `w` exits,
  at distance at most `m - 2` from `x`);
* `pairK_le_wind`: for even `N` and an odd kernel `e` with `e(v) ≤ 0` for `1 ≤ v ≤ N/2`,
  `⟨A, B⟩_e ≤ w e(1) + w sc`; this is the bound `E(A, B) ≤ -w |e(1)| + w sc` in the proof of Lemma
  `lem:junctionineq`;
* `pairK_ico_ge`: for `N = 4d` and `e(v) ≤ 0` for `1 ≤ v ≤ 2d`, `⟨[0, d), [-d, 0)⟩_e ≥ e(1) - fw`; this is
  the bound `E(A₀, B₀) ≥ -|e(1)| - fw` in the proof of Lemma `lem:junctionineq` (case `a = b = d`).

Here `⟨X, Y⟩_e = pairK e X Y`, `sc = scSum N e` and `fw = fwSum N e` (see `OQP27/ClassicalDefs.lean`).
All statements are proved; no hypotheses remain.
-/

namespace OQP27.ClassB

open Finset

variable {N : ℕ} [NeZero N]

/-! ### Elementary tools -/

/-- Discrete intermediate value theorem: a property false at `0` and true at `n` switches on at some
step `i → i + 1` with `i < n`. -/
lemma wind_ivt (P : ℕ → Prop) (n : ℕ) (h0 : ¬ P 0) (hn : P n) :
    ∃ i < n, ¬ P i ∧ P (i + 1) := by
  induction n with
  | zero => exact absurd hn h0
  | succ n ih =>
    by_cases hPn : P n
    · obtain ⟨i, hi, h⟩ := ih hPn
      exact ⟨i, by omega, h⟩
    · exact ⟨n, by omega, hPn, hn⟩

/-- Discrete intermediate value theorem, dual form. -/
lemma wind_ivt' (P : ℕ → Prop) (n : ℕ) (h0 : P 0) (hn : ¬ P n) :
    ∃ i < n, P i ∧ ¬ P (i + 1) := by
  obtain ⟨i, hi, h1, h2⟩ := wind_ivt (fun i => ¬ P i) n (not_not.2 h0) hn
  exact ⟨i, hi, not_not.1 h1, h2⟩

omit [NeZero N] in
/-- The cast `ℕ → ℤ_N` is injective on `[0, N)`. -/
lemma wind_natCast_inj {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : (i : ZMod N) = (j : ZMod N)) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact h

/-- Let `f : [0, N) → ℤ_N` be a bijection (a walk through `ℤ_N`). If `X` is closed under stepping back
along the walk (`f i ∈ X → f (i - 1) ∈ X` for `1 ≤ i < N`), then `X` is an initial segment of the walk:
`X = {f 0, …, f (|X| - 1)}`. -/
lemma wind_walk (f : ℕ → ZMod N) (hf : ∀ i < N, ∀ j < N, f i = f j → i = j)
    (X : Finset (ZMod N)) (hX : ∀ i, 1 ≤ i → i < N → f i ∈ X → f (i - 1) ∈ X) :
    X = (range X.card).image f := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (range N).filter (fun i => f i ∈ X) := ⟨_, rfl⟩
  have hinj : Set.InjOn f ((range N : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    exact hf i (mem_range.1 hi) j (mem_range.1 hj) hij
  have huniv : (range N).image f = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_range, ZMod.card]
  have hXS : X = S.image f := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (range N).image f := huniv ▸ mem_univ x
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx'
      exact mem_image.2 ⟨i, hS ▸ mem_filter.2 ⟨hi, hx⟩, rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      rw [hS] at hi
      exact (mem_filter.1 hi).2
  have hSN : S ⊆ range N := by
    rw [hS]
    exact filter_subset _ _
  have hcard : X.card = S.card := by
    rw [hXS, card_image_of_injOn (hinj.mono (coe_subset.2 hSN))]
  -- `S = {i < N : f i ∈ X}` is closed downwards
  have hdown : ∀ k i, i ∈ S → k ≤ i → i - k ∈ S := by
    intro k
    induction k with
    | zero => intro i hi _; simpa using hi
    | succ k ih =>
      intro i hi hki
      have h1 := ih i hi (by omega)
      rw [hS, mem_filter, mem_range] at h1 ⊢
      have h2 := hX (i - k) (by omega) h1.1 h1.2
      refine ⟨by omega, ?_⟩
      rw [show i - (k + 1) = i - k - 1 by omega]
      exact h2
  -- hence `S` is an initial segment of `ℕ`
  have hSr : S = range S.card := by
    apply eq_of_subset_of_card_le
    · intro i hi
      rw [mem_range]
      have hsub : range (i + 1) ⊆ S := by
        intro j hj
        rw [mem_range] at hj
        have := hdown (i - j) i hi (by omega)
        rwa [show i - (i - j) = j by omega] at this
      have := card_le_card hsub
      rw [card_range] at this
      omega
    · rw [card_range]
  calc X = S.image f := hXS
    _ = (range S.card).image f := by rw [← hSr]
    _ = (range X.card).image f := by rw [hcard]

omit [NeZero N] in
/-- `{s - 1 - i : i < k} = s - k + [0, k)`. -/
lemma wind_image_rev (s : ZMod N) (k : ℕ) :
    (range k).image (fun i : ℕ => s - 1 - (i : ZMod N)) = ico (s - (k : ZMod N)) k := by
  unfold ico
  ext z
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t + (i + 1) = k := ⟨k - (i + 1), by omega⟩
    refine ⟨t, by omega, ?_⟩
    have h : ((t + (i + 1) : ℕ) : ZMod N) = k := by rw [ht]
    simp only [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t + (i + 1) = k := ⟨k - (i + 1), by omega⟩
    refine ⟨t, by omega, ?_⟩
    have h : ((t + (i + 1) : ℕ) : ZMod N) = k := by rw [ht]
    simp only [Nat.cast_add, Nat.cast_one] at h
    linear_combination -h

/-! ### The winding number (Corollary `cor:monotone`) -/

set_option linter.unusedVariables false in
/-- **The winding number is at least one** (Corollary `cor:monotone`). If `∅ ≠ A ≠ ℤ_N`, walking from a
point outside `A` to a point of `A` one enters `A` at some `x`; then `x - 1 ∉ A`, so `x - 1 ∈ B` because no
pair `(x - 1, x)` is coloured `(C, A)`. (The hypothesis `hAB` is not needed.) -/
theorem one_le_wind {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B)
    (hA : A.Nonempty) (hAN : A.card < N) : 1 ≤ wind A B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, -, hb⟩ : ∃ b, b ∈ (univ : Finset (ZMod N)) ∧ b ∉ A :=
    exists_mem_notMem_of_card_lt_card (by rwa [card_univ, ZMod.card])
  obtain ⟨i, -, hi1, hi2⟩ := wind_ivt (fun i : ℕ => b + (i : ZMod N) ∈ A) (a - b).val
    (by simpa using hb) (by simpa [ZMod.natCast_zmod_val] using ha)
  have hi1' : b + (i : ZMod N) ∉ A := hi1
  have hi2' : b + (i : ZMod N) + 1 ∈ A := by
    have : b + (i : ZMod N) + 1 = b + ((i + 1 : ℕ) : ZMod N) := by push_cast; ring
    rw [this]; exact hi2
  have hB : b + (i : ZMod N) ∈ B := by
    by_contra hB
    exact (hcyc (b + (i : ZMod N))).2.2 ⟨hi1', hB, hi2'⟩
  unfold wind
  apply card_pos.2
  exact ⟨b + (i : ZMod N) + 1, mem_filter.2 ⟨hi2', by rwa [add_sub_cancel_right]⟩⟩

set_option linter.unusedVariables false in
/-- **Winding number one gives adjacent intervals** (Corollary `cor:monotone`, case `w = 1`). If
`w = 1`, let `x₀` be the unique point of `A` with `x₀ - 1 ∈ B`. Then `x₀` is the only entry of `A` (an
entry `x` has `x - 1 ∈ B`, since no pair is coloured `(C, A)`), so `A = x₀ + [0, |A|)`; and `x₀ - 1` is the
only exit of `B` (an exit `y` has `y + 1 ∈ A`, since no pair is coloured `(B, C)`), so
`B = x₀ + [-|B|, 0)`. (The hypotheses `hAB` and `hAN` are not needed.) -/
theorem eq_ico_of_wind_eq_one {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B)
    (hAN : A.card + B.card < N) (hw : wind A B = 1) :
    ∃ r : ZMod N, A = ico r A.card ∧ B = ico (r - (B.card : ZMod N)) B.card := by
  unfold wind at hw
  obtain ⟨x₀, hx₀⟩ := card_eq_one.1 hw
  have huniq : ∀ x, x ∈ A → x - 1 ∈ B → x = x₀ := by
    intro x hx hxB
    have : x ∈ A.filter (fun x => x - 1 ∈ B) := mem_filter.2 ⟨hx, hxB⟩
    rw [hx₀] at this
    exact mem_singleton.1 this
  refine ⟨x₀, ?_, ?_⟩
  · -- walk forward from the entry `x₀`
    refine wind_walk (fun i : ℕ => x₀ + (i : ZMod N)) ?_ A ?_
    · intro i hi j hj hij
      exact wind_natCast_inj hi hj (add_left_cancel hij)
    · intro i hi1 hiN (hiA : x₀ + (i : ZMod N) ∈ A)
      by_contra hnot
      have hx1 : x₀ + (i : ZMod N) - 1 = x₀ + ((i - 1 : ℕ) : ZMod N) := by
        rw [Nat.cast_sub hi1, Nat.cast_one]; ring
      have hB : x₀ + (i : ZMod N) - 1 ∈ B := by
        by_contra hB
        exact (hcyc (x₀ + (i : ZMod N) - 1)).2.2 ⟨by rwa [hx1], hB, by rwa [sub_add_cancel]⟩
      have h := huniq _ hiA hB
      have h0 : (i : ZMod N) = ((0 : ℕ) : ZMod N) := by
        rw [Nat.cast_zero]; linear_combination h
      have := wind_natCast_inj hiN (NeZero.pos N) h0
      omega
  · -- walk backward from the exit `x₀ - 1`
    refine (wind_walk (fun i : ℕ => x₀ - 1 - (i : ZMod N)) ?_ B ?_).trans
      (wind_image_rev x₀ B.card)
    · intro i hi j hj hij
      exact wind_natCast_inj hi hj (sub_right_inj.1 hij)
    · intro i hi1 hiN (hiB : x₀ - 1 - (i : ZMod N) ∈ B)
      by_contra hnot
      have hy1 : x₀ - 1 - (i : ZMod N) + 1 = x₀ - 1 - ((i - 1 : ℕ) : ZMod N) := by
        rw [Nat.cast_sub hi1, Nat.cast_one]; ring
      have hA : x₀ - 1 - (i : ZMod N) + 1 ∈ A := by
        by_contra hA
        exact (hcyc (x₀ - 1 - (i : ZMod N))).2.1 ⟨hiB, hA, by rwa [hy1]⟩
      have h := huniq _ hA (by rwa [add_sub_cancel_right])
      have h0 : (i : ZMod N) = ((0 : ℕ) : ZMod N) := by
        rw [Nat.cast_zero]; linear_combination -h
      have := wind_natCast_inj hiN (NeZero.pos N) h0
      omega

/-! ### Exits, entries and the counting bound -/

omit [NeZero N] in
/-- A subset of `ℤ_N` has as many exits (`x ∈ X`, `x + 1 ∉ X`) as entries (`x ∈ X`, `x - 1 ∉ X`). -/
lemma wind_exits_eq_entries (X : Finset (ZMod N)) :
    (X.filter fun x => x + 1 ∉ X).card = (X.filter fun x => x - 1 ∉ X).card := by
  have h1 : (X.filter fun x => x + 1 ∈ X).card + (X.filter fun x => x + 1 ∉ X).card = X.card :=
    card_filter_add_card_filter_not _
  have h2 : (X.filter fun x => x - 1 ∈ X).card + (X.filter fun x => x - 1 ∉ X).card = X.card :=
    card_filter_add_card_filter_not _
  have h3 : (X.filter fun x => x + 1 ∈ X).card = (X.filter fun x => x - 1 ∈ X).card := by
    apply card_nbij' (fun x => x + 1) (fun x => x - 1)
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨hx.2, by simpa using hx.1⟩
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨hx.2, by simpa using hx.1⟩
    · intro x _
      simp
    · intro x _
      simp
  omega

omit [NeZero N] in
/-- In a cyclically ordered colouring the entries of `A` are exactly the junctions `B | A`. -/
lemma wind_eq_card_entries {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B) :
    wind A B = (A.filter fun x => x - 1 ∉ A).card := by
  unfold wind
  congr 1
  apply filter_congr
  intro x hx
  constructor
  · intro hB hA'
    exact disjoint_left.1 hAB hA' hB
  · intro hA'
    by_contra hB
    exact (hcyc (x - 1)).2.2 ⟨hA', hB, by rwa [sub_add_cancel]⟩

omit [NeZero N] in
/-- **The counting step of Lemma `lem:junctionineq`**: `#{x ∈ A : x + m ∈ B} ≤ (m - 1) w`. Walking forward
from `x ∈ A` to `x + m ∈ B` one leaves `A` at an exit `x + j` with `j ≤ m - 2` (`j = m - 1` would give a
pair coloured `(A, B)`), and `A` has `w` exits. -/
lemma wind_count_le {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B) (m : ℕ) :
    (A.filter fun x => x + (m : ZMod N) ∈ B).card ≤ (m - 1) * wind A B := by
  have hexit : (A.filter fun x => x + 1 ∉ A).card = wind A B := by
    rw [wind_exits_eq_entries, wind_eq_card_entries hAB hcyc]
  have hsub : (A.filter fun x => x + (m : ZMod N) ∈ B) ⊆ (range (m - 1)).biUnion
      (fun j => (A.filter fun x => x + 1 ∉ A).image (fun z => z - (j : ZMod N))) := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxA, hxB⟩ := hx
    have hm : ¬ (x + (m : ZMod N) ∈ A) := fun h => disjoint_left.1 hAB h hxB
    obtain ⟨j, hjm, hj1, hj2⟩ :=
      wind_ivt' (fun i : ℕ => x + (i : ZMod N) ∈ A) m (by simpa using hxA) hm
    have hj1' : x + (j : ZMod N) ∈ A := hj1
    have hj2' : x + (j : ZMod N) + 1 ∉ A := by
      have : x + (j : ZMod N) + 1 = x + ((j + 1 : ℕ) : ZMod N) := by push_cast; ring
      rw [this]; exact hj2
    have hj : j < m - 1 := by
      by_contra hj
      have hjeq : j + 1 = m := by omega
      apply (hcyc (x + (j : ZMod N))).1
      refine ⟨hj1', ?_⟩
      have : x + (j : ZMod N) + 1 = x + (m : ZMod N) := by rw [← hjeq]; push_cast; ring
      rw [this]; exact hxB
    rw [mem_biUnion]
    exact ⟨j, mem_range.2 hj, mem_image.2 ⟨x + (j : ZMod N), mem_filter.2 ⟨hj1', hj2'⟩, by ring⟩⟩
  calc (A.filter fun x => x + (m : ZMod N) ∈ B).card
      ≤ ((range (m - 1)).biUnion
          (fun j => (A.filter fun x => x + 1 ∉ A).image (fun z => z - (j : ZMod N)))).card :=
        card_le_card hsub
    _ ≤ ∑ j ∈ range (m - 1),
          ((A.filter fun x => x + 1 ∉ A).image (fun z => z - (j : ZMod N))).card :=
        card_biUnion_le
    _ ≤ ∑ _j ∈ range (m - 1), (A.filter fun x => x + 1 ∉ A).card :=
        sum_le_sum fun j _ => card_image_le
    _ = (m - 1) * wind A B := by rw [sum_const, card_range, smul_eq_mul, hexit]

/-! ### The junction inequality (Lemma `lem:junctionineq`) -/

/-- Pointwise bound for a pair `x ∈ A`, `y ∈ B`: `e(x - y)` is at most `e(1)` if `y = x - 1`, plus
`-e(m)` if `y = x + m` with `2 ≤ m < N/2`. Here `x - y ≠ 0` (disjointness), `x - y ≠ -1` (no pair
`(A, B)`), `e(x - y) ≤ 0` if `2 ≤ (x - y).val ≤ N/2`, and `e(x - y) = -e(y - x)` otherwise. -/
lemma wind_pt_bound (e : ZMod N → ℝ) (he_odd : ∀ u, e (-u) = -e u)
    (he_nonpos : ∀ v : ℕ, 1 ≤ v → 2 * v ≤ N → e (v : ZMod N) ≤ 0) (hN : Even N)
    {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B)
    {x y : ZMod N} (hx : x ∈ A) (hy : y ∈ B) :
    e (x - y) ≤ (if x - 1 = y then e 1 else 0) +
      ∑ m ∈ Ico 2 (N / 2), (if x + (m : ZMod N) = y then -e (m : ZMod N) else 0) := by
  have hterm : ∀ m ∈ Ico 2 (N / 2),
      0 ≤ (if x + (m : ZMod N) = y then -e (m : ZMod N) else 0) := by
    intro m hm
    rw [mem_Ico] at hm
    split_ifs
    · have := he_nonpos m (by omega) (by omega)
      linarith
    · exact le_refl 0
  have hS := sum_nonneg hterm
  by_cases h1 : x - 1 = y
  · rw [if_pos h1]
    have : x - y = 1 := by rw [← h1]; ring
    rw [this]
    linarith
  · rw [if_neg h1, zero_add]
    obtain ⟨v, hv⟩ : ∃ v : ℕ, v = (x - y).val := ⟨_, rfl⟩
    have hxy : x - y = (v : ZMod N) := by rw [hv, ZMod.natCast_zmod_val]
    have hvN : v < N := hv ▸ ZMod.val_lt (x - y)
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, sub_eq_zero] at hxy
      exact disjoint_left.1 hAB hx (hxy ▸ hy)
    have hvN1 : v ≠ N - 1 := by
      intro h
      have hc : ((N - 1 : ℕ) : ZMod N) = -1 := by
        rw [Nat.cast_sub NeZero.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
      rw [h, hc] at hxy
      apply (hcyc x).1
      refine ⟨hx, ?_⟩
      have : x + 1 = y := by linear_combination hxy
      rw [this]; exact hy
    by_cases hv2 : 2 * v ≤ N
    · have := he_nonpos v (by omega) hv2
      rw [hxy]
      linarith
    · obtain ⟨k, hk⟩ := hN
      have hm0 : N - v ∈ Ico 2 (N / 2) := by
        rw [mem_Ico]; omega
      have hym : x + ((N - v : ℕ) : ZMod N) = y := by
        rw [Nat.cast_sub hvN.le, ZMod.natCast_self, ← hxy]; ring
      have hneg : x - y = -((N - v : ℕ) : ZMod N) := by
        rw [← hym]; ring
      calc e (x - y) = -e ((N - v : ℕ) : ZMod N) := by rw [hneg, he_odd]
        _ = (if x + ((N - v : ℕ) : ZMod N) = y then -e ((N - v : ℕ) : ZMod N) else 0) := by
          rw [if_pos hym]
        _ ≤ _ := single_le_sum hterm hm0

/-- **The junction inequality, cyclically ordered side** (proof of Lemma `lem:junctionineq`): for even
`N`, an odd kernel `e` with `e(v) ≤ 0` for `1 ≤ v ≤ N/2`, and a cyclically ordered colouring with winding
number `w`, `⟨A, B⟩_e ≤ w e(1) + w sc`. -/
theorem pairK_le_wind (e : ZMod N → ℝ) (he_odd : ∀ u, e (-u) = -e u)
    (he_nonpos : ∀ v : ℕ, 1 ≤ v → 2 * v ≤ N → e (v : ZMod N) ≤ 0) (hN : Even N)
    {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hcyc : CycOrd A B) :
    pairK e A B ≤ (wind A B : ℝ) * e 1 + (wind A B : ℝ) * scSum N e := by
  have step1 : pairK e A B ≤ ∑ x ∈ A, ∑ y ∈ B, ((if x - 1 = y then e 1 else 0) +
      ∑ m ∈ Ico 2 (N / 2), (if x + (m : ZMod N) = y then -e (m : ZMod N) else 0)) :=
    sum_le_sum fun x hx => sum_le_sum fun y hy =>
      wind_pt_bound e he_odd he_nonpos hN hAB hcyc hx hy
  have step2 : ∀ x ∈ A, ∑ y ∈ B, ((if x - 1 = y then e 1 else 0) +
      ∑ m ∈ Ico 2 (N / 2), (if x + (m : ZMod N) = y then -e (m : ZMod N) else 0)) =
      (if x - 1 ∈ B then e 1 else 0) +
        ∑ m ∈ Ico 2 (N / 2), (if x + (m : ZMod N) ∈ B then -e (m : ZMod N) else 0) := by
    intro x _
    rw [sum_add_distrib, sum_comm (s := B) (t := Ico 2 (N / 2))]
    simp only [sum_ite_eq]
  calc pairK e A B ≤ _ := step1
    _ = ∑ x ∈ A, ((if x - 1 ∈ B then e 1 else 0) +
          ∑ m ∈ Ico 2 (N / 2), (if x + (m : ZMod N) ∈ B then -e (m : ZMod N) else 0)) :=
        sum_congr rfl step2
    _ = (wind A B : ℝ) * e 1 + ∑ m ∈ Ico 2 (N / 2),
          ((A.filter fun x => x + (m : ZMod N) ∈ B).card : ℝ) * (-e (m : ZMod N)) := by
        rw [sum_add_distrib, sum_comm (s := A) (t := Ico 2 (N / 2)), ← sum_filter]
        congr 1
        · rw [sum_const, nsmul_eq_mul]
          rfl
        · refine sum_congr rfl fun m _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (wind A B : ℝ) * e 1 + ∑ m ∈ Ico 2 (N / 2),
          (((m : ℝ) - 1) * wind A B) * (-e (m : ZMod N)) := by
        refine add_le_add le_rfl (sum_le_sum fun m hm => ?_)
        rw [mem_Ico] at hm
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · have h : ((A.filter fun x => x + (m : ZMod N) ∈ B).card : ℝ) ≤
              (((m - 1) * wind A B : ℕ) : ℝ) := by
            exact_mod_cast wind_count_le hAB hcyc m
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
          exact h
        · have := he_nonpos m (by omega) (by omega)
          linarith
    _ = (wind A B : ℝ) * e 1 + (wind A B : ℝ) * scSum N e := by
        unfold scSum
        rw [mul_sum]
        congr 1
        refine sum_congr rfl fun m _ => ?_
        ring

/-- **The junction inequality, interval side** (proof of Lemma `lem:junctionineq`, `a = b = d`,
`N = 4d`): if `e(v) ≤ 0` for `1 ≤ v ≤ 2d`, then `⟨[0, d), [-d, 0)⟩_e ≥ e(1) - fw`. The differences
`m = x - y` lie in `[1, 2d)`; the value `m` occurs at most `m` times (`0 ≤ x ≤ m - 1` determines `y`). -/
theorem pairK_ico_ge (d : ℕ) [NeZero d] (e : ZMod (4 * d) → ℝ)
    (he_nonpos : ∀ v : ℕ, 1 ≤ v → 2 * v ≤ 4 * d → e (v : ZMod (4 * d)) ≤ 0) :
    e 1 - fwSum (4 * d) e ≤ pairK e (ico 0 d) (ico (-(d : ZMod (4 * d))) d) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hinj : ∀ r : ZMod (4 * d),
      Set.InjOn (fun i : ℕ => r + (i : ZMod (4 * d))) ((range d : Finset ℕ) : Set ℕ) := by
    intro r i hi j hj hij
    rw [mem_coe, mem_range] at hi hj
    have h : (i : ZMod (4 * d)) = (j : ZMod (4 * d)) := add_left_cancel hij
    exact wind_natCast_inj (by omega) (by omega) h
  -- the pairing as a sum over `[0, d) × [0, d)`
  have h1 : pairK e (ico 0 d) (ico (-(d : ZMod (4 * d))) d) =
      ∑ p ∈ range d ×ˢ range d, e ((p.1 + d - p.2 : ℕ) : ZMod (4 * d)) := by
    unfold pairK ico
    rw [sum_image (hinj 0), sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_image (hinj _)]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    congr 1
    dsimp only
    rw [Nat.cast_sub (by omega : j ≤ i + d)]
    push_cast
    ring
  -- group the pairs by the difference `m = i + d - j ∈ [1, 2d)`
  have hmaps : ∀ p ∈ range d ×ˢ range d, (fun p : ℕ × ℕ => p.1 + d - p.2) p ∈ Ico 1 (2 * d) := by
    intro p hp
    rw [mem_product, mem_range, mem_range] at hp
    simp only [mem_Ico]
    omega
  have h2 : ∑ p ∈ range d ×ˢ range d, e ((p.1 + d - p.2 : ℕ) : ZMod (4 * d)) =
      ∑ m ∈ Ico 1 (2 * d), (((range d ×ˢ range d).filter
        fun p : ℕ × ℕ => p.1 + d - p.2 = m).card : ℝ) * e (m : ZMod (4 * d)) := by
    rw [← sum_fiberwise_of_maps_to' hmaps (fun m : ℕ => e (m : ZMod (4 * d)))]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_const, nsmul_eq_mul]
  -- the difference `m` occurs at most `m` times
  have h3 : ∀ m ∈ Ico 1 (2 * d),
      ((range d ×ˢ range d).filter fun p : ℕ × ℕ => p.1 + d - p.2 = m).card ≤ m := by
    intro m _
    calc _ ≤ (range m).card := by
          apply card_le_card_of_injOn Prod.fst
          · intro p hp
            rw [mem_coe, mem_filter, mem_product, mem_range, mem_range] at hp
            rw [mem_coe, mem_range]
            omega
          · intro p hp q hq hpq
            rw [mem_coe, mem_filter, mem_product, mem_range, mem_range] at hp hq
            have hpq' : p.1 = q.1 := hpq
            ext
            · exact hpq'
            · omega
      _ = m := card_range m
  have h4 : 4 * d / 2 = 2 * d := by omega
  have h5 : ∑ m ∈ Ico 1 (2 * d), (m : ℝ) * e (m : ZMod (4 * d)) =
      e 1 + ∑ m ∈ Ico 2 (2 * d), (m : ℝ) * e (m : ZMod (4 * d)) := by
    rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < 2 * d)]
    simp
  rw [h1, h2]
  unfold fwSum
  rw [h4]
  calc e 1 - ∑ m ∈ Ico 2 (2 * d), (m : ℝ) * -e (m : ZMod (4 * d))
      = ∑ m ∈ Ico 1 (2 * d), (m : ℝ) * e (m : ZMod (4 * d)) := by
        rw [h5]
        simp only [mul_neg, sum_neg_distrib]
        ring
    _ ≤ _ := by
        apply sum_le_sum
        intro m hm
        have hm' := mem_Ico.1 hm
        apply mul_le_mul_of_nonpos_right
        · exact_mod_cast h3 m hm
        · exact he_nonpos m (by omega) (by omega)

end OQP27.ClassB
