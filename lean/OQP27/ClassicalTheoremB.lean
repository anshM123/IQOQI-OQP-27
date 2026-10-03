import OQP27.ClassicalTheoremA
import OQP27.ClassicalJunction
import OQP27.ClassicalContinuum
import OQP27.ClassicalCot

/-!
# The classical Theorem B for every `d` (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Theorem A (Section 4), Lemma `lem:cot` and the proof
of Theorem B (Section 3).

Main results (no hypotheses):
* `OQP27.ClassB.classical_thmA`: **Theorem A** for `N = 4d`, `|A| = |B| = d`, `d ≥ 2`: for disjoint
  `A, B ⊆ ℤ_{4d}` of size `d`, `∑_{x ∈ A, y ∈ B} cot(π(x - y)/(4d)) ≤ ∑_{x ∈ [0,d), y ∈ [-d,0)} cot(…)`,
  with equality only for `(A, B) = (r + [0,d), r + [-d,0))`.
* `OQP27.ClassB.classicalTheoremB`: **module L6's `OQP27.Rig.Hyp_ClassicalTheoremB d` for every `d ≥ 1`**:
  `F(a) ≤ F_DKZ` for every `a ∈ ℤ_4^d`, with equality only for one-step `a`
  (`classicalTheoremB_all`: the same in the form `∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d`).
Consequences for module L6's rigidity chain are in `OQP27/ClassicalRigidity.lean`.

The ingredients: the cotangent representation `F(a) = ⟨S_a, S_a - d⟩/2 - d/2` (`OQP27/ClassicalCot.lean`);
the exchange identity and cyclic order (`OQP27/ClassicalExchange.lean`); winding numbers and the junction
counting (`OQP27/ClassicalWinding.lean`); the junction estimates `e(m) ≤ 0`, `|e(m)| ≤ (N/π)/(6m(m²-1))`,
`|e(1)| > (7/24)(N/π)` (`OQP27/ClassicalJunction.lean`); the continuous inequality for unit cells from
module L5's Q-T1 in the scalar case (`OQP27/ClassicalContinuum.lean`); the assembly
(`OQP27/ClassicalTheoremA.lean`).
-/

set_option autoImplicit false

namespace OQP27.ClassB

open Finset

/-- **Theorem A** (`N = 4d`, `|A| = |B| = d`, `d ≥ 2`) for the cotangent kernel `κ(u) = cot(πu/N)`. -/
theorem classical_thmA {d : ℕ} [NeZero d] (hd : 2 ≤ d) (A B : Finset (ZMod (4 * d)))
    (hAB : Disjoint A B) (hA : A.card = d) (hB : B.card = d) :
    pairK (kap (4 * d)) A B ≤ pairK (kap (4 * d)) (ico 0 d) (ico (-(d : ZMod (4 * d))) d) ∧
      (pairK (kap (4 * d)) A B = pairK (kap (4 * d)) (ico 0 d) (ico (-(d : ZMod (4 * d))) d) →
        ∃ r : ZMod (4 * d), A = ico r d ∧ B = ico (r - (d : ZMod (4 * d))) d) :=
  thmA_abstract (kap (4 * d)) (kbar (4 * d)) (ejun (4 * d)) (kap_eq_add (4 * d)) kap_neg
    (fun v hv hvN => kap_strictAnti v hv hvN) ejun_neg (fun v hv hvN => ejun_nonpos v hv hvN)
    (junction_margin (by omega)) (fun A B hAB hA hB => kbar_continuum A B hAB hA hB) A B hAB hA hB

/-- **The classical Theorem B for every `d ≥ 1`** (module L6's `Hyp_ClassicalTheoremB d`):
`F(a) ≤ F_DKZ` for all `a ∈ ℤ_4^d`, with equality only for one-step `a`. -/
theorem classicalTheoremB (d : ℕ) (hd : 1 ≤ d) : Rig.Hyp_ClassicalTheoremB d := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    intro a
    have hF : Rig.clockFa a = 0 := by
      unfold Rig.clockFa
      simp
    have hD : Rig.FDKZ 1 = 0 := by
      unfold Rig.FDKZ
      simp
    refine ⟨by rw [hF, hD], fun _ => ⟨a 0 - 1, 0, by norm_num, fun k => ?_⟩⟩
    fin_cases k
    simp
  · have : NeZero d := ⟨by omega⟩
    intro a
    have hS := classical_thmA h (Sa a) ((Sa a).image (· - (d : ZMod (4 * d)))) (disjoint_Sa a)
      (card_Sa a) (card_Sa_sub a)
    rw [clockFa_eq_pairK, FDKZ_eq_pairK]
    refine ⟨by linarith [hS.1], fun heq => ?_⟩
    obtain ⟨r, hr, -⟩ := hS.2 (by linarith)
    exact isOneStep_of_Sa_eq a r hr

/-- `Hyp_ClassicalTheoremB` for every `d`, in the form taken by the rigidity theorems and by `Main.lean`. -/
theorem classicalTheoremB_all : ∀ d [NeZero d], 2 ≤ d → Rig.Hyp_ClassicalTheoremB d :=
  fun d _ hd => classicalTheoremB d (by omega)

end OQP27.ClassB
