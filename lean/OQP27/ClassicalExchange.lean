import OQP27.ClassicalDefs

/-!
# The classical Theorem B for every `d` (module L7): cyclic symmetry and the exchange argument

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 4 (proof of Theorem A): Lemma `lem:cyclic`
(cyclic symmetry), Lemma `lem:swap` (exchange identity) and the first assertion of Corollary `cor:monotone`
(every maximiser of `⟨A, B⟩` is cyclically ordered).

Everything stated here is proved in full: no hypotheses (`Hyp_...`) remain.

For a kernel `f : ℤ_N → ℝ` with `f(-u) = -f(u)` and the pairing `⟨X, Y⟩ = pairK f X Y = ∑_{x∈X} ∑_{y∈Y} f(x - y)`:

* `pairK_swap`, `pairK_self`, `pairK_univ`: `⟨Y, X⟩ = -⟨X, Y⟩`, `⟨X, X⟩ = 0` and `⟨X, ℤ_N⟩ = 0`
  (the last one because `∑_{u ∈ ℤ_N} f(u) = 0`);
* `pairK_cyc` (Lemma `lem:cyclic`): for disjoint `A, B` and `C = ℤ_N ∖ (A ∪ B)`,
  `⟨B, C⟩ = ⟨A, B⟩` and `⟨C, A⟩ = ⟨A, B⟩`;
* `pairK_image_add`, `image_add_ico`: the pairing is invariant under a common translation, and a translate
  of the interval `ico r L = r + [0, L)` is again such an interval;
* `cycOrd_of_isMax` (Lemma `lem:swap` and Corollary `cor:monotone`, first assertion): let `κ` be odd with
  `κ(v + 1) < κ(v)` for `1 ≤ v ≤ N - 2` (for instance `κ(u) = cot(π u/N)`). If disjoint `A, B` maximise
  `⟨A, B⟩_κ` among disjoint pairs of the same sizes, and `A`, `B`, `C` are nonempty, then the colouring
  `(A, B, C)` is cyclically ordered (`CycOrd A B`). Exchanging an adjacent pair `(x, x + 1)` coloured
  `(A, B)`, `(B, C)` or `(C, A)` keeps the sizes and increases the pairing by
  `∑_{t ∈ T} (κ(x - t) - κ(x + 1 - t)) > 0`, where `T = C`, `A` or `B` respectively.
-/

namespace OQP27.ClassB

open Finset

-- The statements below keep the section variable `[NeZero N]` uniformly, also where the proof does
-- not need it.
set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ## Odd kernels -/

/-- An odd kernel sums to zero over `ℤ_N`. -/
lemma exch_sum_univ_odd (f : ZMod N → ℝ) (hf : ∀ u, f (-u) = -f u) : ∑ u : ZMod N, f u = 0 := by
  have h : ∑ u : ZMod N, f (-u) = ∑ u : ZMod N, f u := Equiv.sum_comp (Equiv.neg (ZMod N)) f
  simp only [hf, Finset.sum_neg_distrib] at h
  linarith

/-- Antisymmetry of the pairing of an odd kernel: `⟨Y, X⟩ = -⟨X, Y⟩`. -/
theorem pairK_swap (f : ZMod N → ℝ) (hf : ∀ u, f (-u) = -f u) (X Y : Finset (ZMod N)) :
    pairK f Y X = -pairK f X Y := by
  unfold pairK
  have hc : ∑ y ∈ Y, ∑ x ∈ X, f (y - x) = ∑ x ∈ X, ∑ y ∈ Y, f (y - x) := Finset.sum_comm
  rw [hc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← hf, neg_sub]

/-- `⟨X, X⟩ = 0` for an odd kernel. -/
theorem pairK_self (f : ZMod N → ℝ) (hf : ∀ u, f (-u) = -f u) (X : Finset (ZMod N)) :
    pairK f X X = 0 := by
  have h := pairK_swap f hf X X
  linarith

/-- `⟨X, ℤ_N⟩ = 0` for an odd kernel. -/
theorem pairK_univ (f : ZMod N → ℝ) (hf : ∀ u, f (-u) = -f u) (X : Finset (ZMod N)) :
    pairK f X univ = 0 := by
  unfold pairK
  refine Finset.sum_eq_zero fun x _ => ?_
  have h : ∑ y : ZMod N, f (x - y) = ∑ u : ZMod N, f u := Equiv.sum_comp (Equiv.subLeft x) f
  rw [h]
  exact exch_sum_univ_odd f hf

/-- Additivity of the pairing in the second set. -/
lemma exch_pairK_union_right (f : ZMod N → ℝ) (X : Finset (ZMod N)) {Y Z : Finset (ZMod N)}
    (h : Disjoint Y Z) : pairK f X (Y ∪ Z) = pairK f X Y + pairK f X Z := by
  unfold pairK
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_union h

/-- Cyclic symmetry (Lemma `lem:cyclic`): with `C = ℤ_N ∖ (A ∪ B)`, `⟨B, C⟩ = ⟨A, B⟩ = ⟨C, A⟩`. -/
theorem pairK_cyc (f : ZMod N → ℝ) (hf : ∀ u, f (-u) = -f u) {A B : Finset (ZMod N)}
    (hAB : Disjoint A B) :
    pairK f B (univ \ (A ∪ B)) = pairK f A B ∧ pairK f (univ \ (A ∪ B)) A = pairK f A B := by
  have hU : (A ∪ B) ∪ (univ \ (A ∪ B)) = univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hD : Disjoint (A ∪ B) (univ \ (A ∪ B)) := Finset.disjoint_sdiff
  have h1 := pairK_univ f hf A
  have h2 := pairK_univ f hf B
  rw [← hU, exch_pairK_union_right f A hD, exch_pairK_union_right f A hAB] at h1
  rw [← hU, exch_pairK_union_right f B hD, exch_pairK_union_right f B hAB] at h2
  have h3 := pairK_self f hf A
  have h4 := pairK_self f hf B
  have h5 := pairK_swap f hf A B
  have h6 := pairK_swap f hf A (univ \ (A ∪ B))
  constructor <;> linarith

/-! ## Translations -/

/-- The pairing is invariant under translating both sets by the same `r`. -/
theorem pairK_image_add (f : ZMod N → ℝ) (X Y : Finset (ZMod N)) (r : ZMod N) :
    pairK f (X.image (r + ·)) (Y.image (r + ·)) = pairK f X Y := by
  unfold pairK
  have hinj : ∀ S : Finset (ZMod N), Set.InjOn (r + · : ZMod N → ZMod N) S :=
    fun S => (add_right_injective r).injOn
  rw [Finset.sum_image (hinj X)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (hinj Y)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [add_sub_add_left_eq_sub]

/-- `s + (r + [0, L)) = (s + r) + [0, L)`. -/
theorem image_add_ico (s r : ZMod N) (L : ℕ) : (ico r L).image (s + ·) = ico (s + r) L := by
  unfold ico
  rw [Finset.image_image]
  congr 1
  funext i
  simp [add_assoc]

/-! ## The exchange argument -/

/-- `δ(u) = κ(u) - κ(u + 1) > 0` for `u ∉ {0, -1}`, i.e. for `1 ≤ u ≤ N - 2`. -/
lemma exch_delta_pos (κ : ZMod N → ℝ)
    (hκ_dec : ∀ v : ℕ, 1 ≤ v → v + 2 ≤ N → κ ((v + 1 : ℕ) : ZMod N) < κ (v : ZMod N))
    (u : ZMod N) (h0 : u ≠ 0) (h1 : u + 1 ≠ 0) : κ (u + 1) < κ u := by
  have hv0 : u.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have hvlt : u.val < N := ZMod.val_lt u
  have hv1 : u.val + 1 ≠ N := by
    intro h
    apply h1
    have h' : ((u.val + 1 : ℕ) : ZMod N) = 0 := by rw [h, ZMod.natCast_self]
    rwa [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h'
  have h := hκ_dec u.val (by omega) (by omega)
  rwa [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h

/-- `κ(x + 1 - t) < κ(x - t)` whenever `t ∉ {x, x + 1}`. -/
lemma exch_delta_sub (κ : ZMod N → ℝ)
    (hκ_dec : ∀ v : ℕ, 1 ≤ v → v + 2 ≤ N → κ ((v + 1 : ℕ) : ZMod N) < κ (v : ZMod N))
    (x t : ZMod N) (h0 : t ≠ x) (h1 : t ≠ x + 1) : κ (x + 1 - t) < κ (x - t) := by
  have h := exch_delta_pos κ hκ_dec (x - t) (sub_ne_zero.mpr (Ne.symm h0)) (by
    rw [sub_add_eq_add_sub]
    exact sub_ne_zero.mpr (Ne.symm h1))
  rwa [sub_add_eq_add_sub] at h

/-- The gain of an exchange: `∑_{t ∈ T} κ(x + 1 - t) < ∑_{t ∈ T} κ(x - t)` for nonempty `T` avoiding
`x` and `x + 1`. -/
lemma exch_gap_pos (κ : ZMod N → ℝ)
    (hκ_dec : ∀ v : ℕ, 1 ≤ v → v + 2 ≤ N → κ ((v + 1 : ℕ) : ZMod N) < κ (v : ZMod N))
    {T : Finset (ZMod N)} (hT : T.Nonempty) (x : ZMod N) (hx : x ∉ T) (hx1 : x + 1 ∉ T) :
    ∑ t ∈ T, κ (x + 1 - t) < ∑ t ∈ T, κ (x - t) := by
  refine Finset.sum_lt_sum_of_nonempty hT fun t ht => ?_
  exact exch_delta_sub κ hκ_dec x t (fun h => hx (h ▸ ht)) (fun h => hx1 (h ▸ ht))

/-- Replacing `b ∈ S` by `a ∉ S` in a sum. -/
lemma exch_sum_insert_erase (g : ZMod N → ℝ) {S : Finset (ZMod N)} {a b : ZMod N}
    (hb : b ∈ S) (ha : a ∉ S) :
    ∑ y ∈ insert a (S.erase b), g y = ∑ y ∈ S, g y + g a - g b := by
  rw [Finset.sum_insert (fun h => ha (Finset.mem_of_mem_erase h)), ← Finset.add_sum_erase S g hb]
  ring

/-- Replacing `b ∈ S` by `a ∉ S` in the first argument of the pairing. -/
lemma exch_pairK_insert_erase (f : ZMod N → ℝ) {S : Finset (ZMod N)} (T : Finset (ZMod N))
    {a b : ZMod N} (hb : b ∈ S) (ha : a ∉ S) :
    pairK f (insert a (S.erase b)) T = pairK f S T + ∑ t ∈ T, f (a - t) - ∑ t ∈ T, f (b - t) := by
  unfold pairK
  exact exch_sum_insert_erase (fun y => ∑ t ∈ T, f (y - t)) hb ha

/-- Replacing `b ∈ S` by `a ∉ S` keeps the size. -/
lemma exch_card_insert_erase {S : Finset (ZMod N)} {a b : ZMod N} (hb : b ∈ S) (ha : a ∉ S) :
    (insert a (S.erase b)).card = S.card := by
  rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
    Finset.card_erase_add_one hb]

/-- Exchanging `a ∈ A` and `b ∈ B` keeps the two sets disjoint. -/
lemma exch_disjoint_swap {A B : Finset (ZMod N)} {a b : ZMod N} (hAB : Disjoint A B)
    (hab : a ≠ b) : Disjoint (insert b (A.erase a)) (insert a (B.erase b)) := by
  rw [Finset.disjoint_left]
  intro y hyA hyB
  rw [Finset.mem_insert, Finset.mem_erase] at hyA hyB
  rcases hyA with h1 | ⟨h1, h2⟩ <;> rcases hyB with h3 | ⟨h3, h4⟩
  · exact hab (h3.symm.trans h1)
  · exact h3 h1
  · exact h1 h3
  · exact Finset.disjoint_left.mp hAB h2 h4

/-- Exchanging `a ∈ A` and `b ∈ B` does not change `A ∪ B` (hence not `C`). -/
lemma exch_union_swap {A B : Finset (ZMod N)} {a b : ZMod N} (ha : a ∈ A) (hb : b ∈ B) :
    insert b (A.erase a) ∪ insert a (B.erase b) = A ∪ B := by
  ext y
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ((h | ⟨_, h⟩) | (h | ⟨_, h⟩))
    · exact Or.inr (h ▸ hb)
    · exact Or.inl h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hya : y = a
      · exact Or.inr (Or.inl hya)
      · exact Or.inl (Or.inr ⟨hya, h⟩)
    · by_cases hyb : y = b
      · exact Or.inl (Or.inl hyb)
      · exact Or.inr (Or.inr ⟨hyb, h⟩)

/-- Lemma `lem:swap` and Corollary `cor:monotone` (first assertion): for an odd kernel `κ` with
`κ(v + 1) < κ(v)` for `1 ≤ v ≤ N - 2`, every maximiser `(A, B)` of `⟨A, B⟩_κ` over disjoint pairs of the
same sizes, with `A`, `B` and `C = ℤ_N ∖ (A ∪ B)` nonempty, is cyclically ordered. -/
theorem cycOrd_of_isMax (κ : ZMod N → ℝ) (hκ_odd : ∀ u, κ (-u) = -κ u)
    (hκ_dec : ∀ v : ℕ, 1 ≤ v → v + 2 ≤ N → κ ((v + 1 : ℕ) : ZMod N) < κ (v : ZMod N))
    {A B : Finset (ZMod N)} (hAB : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hC : (univ \ (A ∪ B)).Nonempty)
    (hmax : ∀ A' B' : Finset (ZMod N), Disjoint A' B' → A'.card = A.card → B'.card = B.card →
      pairK κ A' B' ≤ pairK κ A B) :
    CycOrd A B := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · -- A pair coloured `(A, B)`: exchange `x` and `x + 1`; `C` is unchanged, and by cyclic symmetry
    -- `⟨A', B'⟩ - ⟨A, B⟩ = ⟨B', C⟩ - ⟨B, C⟩ = ∑_{t ∈ C} (κ(x - t) - κ(x + 1 - t)) > 0`.
    rintro ⟨hxA, hx1B⟩
    have hxB : x ∉ B := Finset.disjoint_left.mp hAB hxA
    have hx1A : x + 1 ∉ A := fun h => Finset.disjoint_left.mp hAB h hx1B
    have hne : x ≠ x + 1 := fun h => hxB (h ▸ hx1B)
    have hxC : x ∉ univ \ (A ∪ B) := by
      rw [Finset.mem_sdiff]
      exact fun h => h.2 (Finset.mem_union_left _ hxA)
    have hx1C : x + 1 ∉ univ \ (A ∪ B) := by
      rw [Finset.mem_sdiff]
      exact fun h => h.2 (Finset.mem_union_right _ hx1B)
    have hdisj := exch_disjoint_swap hAB hne
    have h1 := hmax _ _ hdisj (exch_card_insert_erase hxA hx1A) (exch_card_insert_erase hx1B hxB)
    have h2 := (pairK_cyc κ hκ_odd hdisj).1
    rw [exch_union_swap hxA hx1B] at h2
    have h3 := (pairK_cyc κ hκ_odd hAB).1
    have h4 := exch_pairK_insert_erase κ (univ \ (A ∪ B)) hx1B hxB
    have h5 := exch_gap_pos κ hκ_dec hC x hxC hx1C
    linarith
  · -- A pair coloured `(B, C)`: move `x` from `B` to `x + 1`; `A` is unchanged and
    -- `⟨A, B'⟩ - ⟨A, B⟩ = ∑_{s ∈ A} (κ(x - s) - κ(x + 1 - s)) > 0`.
    rintro ⟨hxB, hx1A, hx1B⟩
    have hxA : x ∉ A := fun h => Finset.disjoint_left.mp hAB h hxB
    have hdisj : Disjoint A (insert (x + 1) (B.erase x)) := by
      rw [Finset.disjoint_insert_right]
      exact ⟨hx1A, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hAB⟩
    have h1 := hmax _ _ hdisj rfl (exch_card_insert_erase hxB hx1B)
    have h2 := pairK_swap κ hκ_odd A (insert (x + 1) (B.erase x))
    have h3 := pairK_swap κ hκ_odd A B
    have h4 := exch_pairK_insert_erase κ A hxB hx1B
    have h5 := exch_gap_pos κ hκ_dec hA x hxA hx1A
    linarith
  · -- A pair coloured `(C, A)`: move `x + 1` from `A` to `x`; `B` is unchanged and
    -- `⟨A', B⟩ - ⟨A, B⟩ = ∑_{y ∈ B} (κ(x - y) - κ(x + 1 - y)) > 0`.
    rintro ⟨hxA, hxB, hx1A⟩
    have hx1B : x + 1 ∉ B := Finset.disjoint_left.mp hAB hx1A
    have hdisj : Disjoint (insert x (A.erase (x + 1))) B := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hxB, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hAB⟩
    have h1 := hmax _ _ hdisj (exch_card_insert_erase hx1A hxA) rfl
    have h4 := exch_pairK_insert_erase κ B hx1A hxA
    have h5 := exch_gap_pos κ hκ_dec hB x hxB hx1B
    linarith

end OQP27.ClassB
