import OQP27.ClassicalExchange
import OQP27.ClassicalWinding

/-!
# Theorem A (discrete Hilbert-transform rearrangement), case `N = 4d`, `|A| = |B| = d` (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 4, "Conclusion of the proof" of Theorem A.

`OQP27.ClassB.thmA_abstract` is the conclusion of the proof of Theorem A for an abstract kernel
`κ = q + e` on `ℤ_N`, `N = 4d`, with the properties used in the paper:
* `κ` odd and strictly decreasing on `{1, …, N-1}` (exchange identity, Lemma `lem:swap`);
* `e` odd and `≤ 0` on `{1, …, N/2}`, with the junction margin `2 sc + fw < -e(1)` (Lemma `lem:junction`);
* the continuous inequality for `q` (Proposition `prop:cont` for unit cells).
Then for disjoint `A, B ⊆ ℤ_N` with `|A| = |B| = d`, `⟨A, B⟩_κ ≤ ⟨[0,d), [-d,0)⟩_κ`, with equality only if
`(A, B) = (r + [0,d), r + [-d,0))` for some `r`.

Proof (as in the paper): a maximiser exists (finitely many pairs); by the exchange identity it is
cyclically ordered (`cycOrd_of_isMax`); its winding number `w = #{B | A junctions}` is `≥ 1`
(`one_le_wind`); if `w ≥ 2` then `⟨A,B⟩_κ = ⟨A,B⟩_q + ⟨A,B⟩_e ≤ ⟨A₀,B₀⟩_q + w e(1) + w sc`
(`pairK_le_wind`) `< ⟨A₀,B₀⟩_q + e(1) - fw ≤ ⟨A₀,B₀⟩_κ` (`pairK_ico_ge`), contradicting maximality;
so `w = 1` and the maximiser is a rotation of `(A₀, B₀)` (`eq_ico_of_wind_eq_one`), whose value is
`⟨A₀,B₀⟩_κ` by translation invariance (`pairK_image_add`).  Every pair attaining the maximum is a
maximiser, hence a rotation of `(A₀, B₀)`.

No hypotheses beyond the stated (abstract) ones; they are verified for `κ = cot(π·/N)` in
`OQP27/ClassicalTheoremB.lean`.
-/

set_option autoImplicit false

namespace OQP27.ClassB

open Finset

section Intervals

variable {N : ℕ}

lemma ico_inj_on {L : ℕ} (hL : L ≤ N) (r : ZMod N) :
    Set.InjOn (fun i : ℕ => r + (i : ZMod N)) (range L : Set ℕ) := by
  intro i hi j hj hij
  simp only at hij
  have h := add_left_cancel hij
  have hi' : i < N := lt_of_lt_of_le (Finset.mem_range.1 hi) hL
  have hj' : j < N := lt_of_lt_of_le (Finset.mem_range.1 hj) hL
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this

lemma card_ico {L : ℕ} (hL : L ≤ N) (r : ZMod N) : (ico r L).card = L := by
  unfold ico
  rw [Finset.card_image_of_injOn (ico_inj_on hL r), Finset.card_range]

end Intervals

lemma disjoint_ico_ico (d : ℕ) [NeZero d] :
    Disjoint (ico (0 : ZMod (4 * d)) d) (ico (-(d : ZMod (4 * d))) d) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold ico at hx hx'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨j, hj, hij⟩ := Finset.mem_image.1 hx'
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  -- `-d + j = i` gives `i + d - j ≡ 0 (mod 4d)` with `1 ≤ i + d - j ≤ 2d - 1`
  have hi2 : ((i : ℕ) : ZMod (4 * d)) = -(d : ZMod (4 * d)) + (j : ZMod (4 * d)) := by
    rw [hij, zero_add]
  have h : (((i + d - j : ℕ)) : ZMod (4 * d)) = 0 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [hi2]
    ring
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
  omega

/-- **Theorem A** (`N = 4d`, `|A| = |B| = d`) for an abstract kernel `κ = q + e` with the properties used
in the paper's proof. -/
theorem thmA_abstract {d : ℕ} [NeZero d] (κ q e : ZMod (4 * d) → ℝ)
    (hsplit : ∀ u, κ u = q u + e u)
    (hκ_odd : ∀ u, κ (-u) = -κ u)
    (hκ_dec : ∀ v : ℕ, 1 ≤ v → v + 2 ≤ 4 * d →
      κ ((v + 1 : ℕ) : ZMod (4 * d)) < κ (v : ZMod (4 * d)))
    (he_odd : ∀ u, e (-u) = -e u)
    (he_nonpos : ∀ v : ℕ, 1 ≤ v → 2 * v ≤ 4 * d → e (v : ZMod (4 * d)) ≤ 0)
    (hmargin : 2 * scSum (4 * d) e + fwSum (4 * d) e < -e 1)
    (hq : ∀ A B : Finset (ZMod (4 * d)), Disjoint A B → A.card = d → B.card = d →
      pairK q A B ≤ pairK q (ico 0 d) (ico (-(d : ZMod (4 * d))) d))
    (A B : Finset (ZMod (4 * d))) (hAB : Disjoint A B) (hA : A.card = d) (hB : B.card = d) :
    pairK κ A B ≤ pairK κ (ico 0 d) (ico (-(d : ZMod (4 * d))) d) ∧
      (pairK κ A B = pairK κ (ico 0 d) (ico (-(d : ZMod (4 * d))) d) →
        ∃ r : ZMod (4 * d), A = ico r d ∧ B = ico (r - (d : ZMod (4 * d))) d) := by
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdN : d ≤ 4 * d := by omega
  set A₀ : Finset (ZMod (4 * d)) := ico 0 d with hA₀
  set B₀ : Finset (ZMod (4 * d)) := ico (-(d : ZMod (4 * d))) d with hB₀
  have hA₀c : A₀.card = d := card_ico hdN 0
  have hB₀c : B₀.card = d := card_ico hdN _
  have hA₀B₀ : Disjoint A₀ B₀ := disjoint_ico_ico d
  -- signs of `sc` and `fw`
  have hsc : 0 ≤ scSum (4 * d) e := by
    unfold scSum
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h1 : 1 ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      linarith
    have h2 : e (m : ZMod (4 * d)) ≤ 0 := he_nonpos m (by omega) (by omega)
    nlinarith
  have hfw : 0 ≤ fwSum (4 * d) e := by
    unfold fwSum
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h2 : e (m : ZMod (4 * d)) ≤ 0 := he_nonpos m (by omega) (by omega)
    have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hsplitK : ∀ X Y : Finset (ZMod (4 * d)), pairK κ X Y = pairK q X Y + pairK e X Y := by
    intro X Y
    rw [pairK_congr hsplit X Y, pairK_add]
  have hN : Even (4 * d) := ⟨2 * d, by ring⟩
  -- the junction step: winding `≥ 2` is strictly worse than `(A₀, B₀)`
  have hjunction : ∀ A B : Finset (ZMod (4 * d)), Disjoint A B → A.card = d → B.card = d →
      CycOrd A B → 2 ≤ wind A B → pairK κ A B < pairK κ A₀ B₀ := by
    intro A B hAB hA hB hcyc hw
    have h1 := hq A B hAB hA hB
    have h2 := pairK_le_wind e he_odd he_nonpos hN hAB hcyc
    have h3 := pairK_ico_ge d e he_nonpos
    rw [hsplitK, hsplitK A₀ B₀]
    have hwr : (2 : ℝ) ≤ (wind A B : ℝ) := by exact_mod_cast hw
    set w : ℝ := (wind A B : ℝ)
    have key : w * e 1 + w * scSum (4 * d) e < e 1 - fwSum (4 * d) e := by
      nlinarith
    linarith
  -- admissible pairs
  set Adm : Finset (Finset (ZMod (4 * d)) × Finset (ZMod (4 * d))) :=
    (univ ×ˢ univ).filter fun p => Disjoint p.1 p.2 ∧ p.1.card = d ∧ p.2.card = d with hAdm
  have hmem : ∀ X Y : Finset (ZMod (4 * d)), (X, Y) ∈ Adm ↔ Disjoint X Y ∧ X.card = d ∧ Y.card = d := by
    intro X Y
    simp [hAdm]
  -- a maximiser is a rotation of `(A₀, B₀)`
  have hrot : ∀ X Y : Finset (ZMod (4 * d)), Disjoint X Y → X.card = d → Y.card = d →
      (∀ p ∈ Adm, pairK κ p.1 p.2 ≤ pairK κ X Y) →
        ∃ r : ZMod (4 * d), X = ico r d ∧ Y = ico (r - (d : ZMod (4 * d))) d := by
    intro X Y hXY hX hY hmax
    have hXne : X.Nonempty := by rw [← Finset.card_pos, hX]; exact hd1
    have hYne : Y.Nonempty := by rw [← Finset.card_pos, hY]; exact hd1
    have hCne : (univ \ (X ∪ Y)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_union_of_disjoint hXY, hX, hY, Finset.card_univ, ZMod.card]
      omega
    have hcyc : CycOrd X Y := by
      apply cycOrd_of_isMax κ hκ_odd hκ_dec hXY hXne hYne hCne
      intro A' B' hA'B' hA' hB'
      exact hmax (A', B') ((hmem A' B').2 ⟨hA'B', hA'.trans hX, hB'.trans hY⟩)
    have hw1 := one_le_wind hXY hcyc hXne (by rw [hX]; omega)
    have hw : wind X Y = 1 := by
      by_contra hne
      have hw2 : 2 ≤ wind X Y := by omega
      have hlt := hjunction X Y hXY hX hY hcyc hw2
      have hle := hmax (A₀, B₀) ((hmem A₀ B₀).2 ⟨hA₀B₀, hA₀c, hB₀c⟩)
      linarith
    obtain ⟨r, hXr, hYr⟩ := eq_ico_of_wind_eq_one hXY hcyc (by rw [hX, hY]; omega) hw
    exact ⟨r, by rw [hXr, hX], by rw [hYr, hY]⟩
  -- the value of a rotation of `(A₀, B₀)`
  have hval : ∀ r : ZMod (4 * d), pairK κ (ico r d) (ico (r - (d : ZMod (4 * d))) d) =
      pairK κ A₀ B₀ := by
    intro r
    have e1 : ico r d = A₀.image (r + ·) := by rw [hA₀, image_add_ico, add_zero]
    have e2 : ico (r - (d : ZMod (4 * d))) d = B₀.image (r + ·) := by
      rw [hB₀, image_add_ico, sub_eq_add_neg]
    rw [e1, e2, pairK_image_add]
  -- existence of a maximiser
  have hne : Adm.Nonempty := ⟨(A₀, B₀), (hmem A₀ B₀).2 ⟨hA₀B₀, hA₀c, hB₀c⟩⟩
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image Adm (fun p => pairK κ p.1 p.2) hne
  obtain ⟨hp1, hp2, hp3⟩ := (hmem p.1 p.2).1 hp
  obtain ⟨r, hr1, hr2⟩ := hrot p.1 p.2 hp1 hp2 hp3 hpmax
  have hmaxval : pairK κ p.1 p.2 = pairK κ A₀ B₀ := by rw [hr1, hr2, hval]
  have hall : ∀ q' ∈ Adm, pairK κ q'.1 q'.2 ≤ pairK κ A₀ B₀ := by
    intro q' hq'
    rw [← hmaxval]
    exact hpmax q' hq'
  refine ⟨?_, ?_⟩
  · exact hall (A, B) ((hmem A B).2 ⟨hAB, hA, hB⟩)
  · intro heq
    apply hrot A B hAB hA hB
    intro q' hq'
    rw [heq]
    exact hall q' hq'

end OQP27.ClassB
