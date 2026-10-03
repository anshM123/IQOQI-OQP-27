import OQP27.CertCheck
import OQP27.CertClausen

/-!
# The complete certificate checker for CONE_d (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`OQP27.ConeCertificate.fullCheck c` computes, in exact rational interval arithmetic,
1. the table of enclosures of `Cl₂(2π c'/Q)`, `Q = 4dq`, `c' = 0, …, 2dq` (file `CertClausen`);
2. the table of enclosures of `Ĝ(J/q)`, `J = 0, …, dq`;
3. for every cell `ℓ = n/q` of the certificate: the window sums `J_r(m) = n_r + ⋯ + n_{r+m-1}` (integers),
   enclosures of `P(m) = (1/d) ∑_r Ĝ(J_r(m)/q)` for `m = 0, …, d` and of `u^ℓ_m = P(m+1) - 2P(m) + P(m-1)`;
4. enclosures of `v_m = 2/sin(π m/(2d))` (after checking that the enclosure of the sine is positive);
5. the residual-correction check `OQP27.ConeCertificate.check` (file `CertCheck`).

`OQP27.ConeCertificate.fullCheck_sound`: `c.fullCheck = true → ConeCert c.d`; `fullCheck_sound_strong` gives in
addition that every weight is positive (used for the strengthened statement `ConeCertPos` of the skeleton).
Since `fullCheck` is an ordinary computable function on rationals, `c.fullCheck = true` can be established for a
concrete certificate by kernel evaluation (`decide +kernel`); no other trusted computation is involved.

No hypotheses.
-/

namespace OQP27

open Finset Real

/-! ### Window sums of integer cells -/

/-- The integer window sum `J_r(m) = n_r + ⋯ + n_{r+m-1}` (indices mod `d`). -/
def winN (d : ℕ) (n : List ℕ) (r m : ℕ) : ℕ := ∑ i ∈ range m, n.getD ((r + i) % d) 0

theorem coneWindowSum_cellVec (d q : ℕ) (n : List ℕ) (r m : ℕ) :
    coneWindowSum d (cellVec q n) r m = (winN d n r m : ℝ) / q := by
  unfold coneWindowSum cellVec winN
  push_cast
  rw [Finset.sum_div]

theorem winN_le {d : ℕ} (hd : 0 < d) (n : List ℕ) (r : ℕ) {m : ℕ} (hm : m ≤ d) :
    winN d n r m ≤ ∑ s ∈ range d, n.getD s 0 := by
  unfold winN
  have hinj : Set.InjOn (fun i => (r + i) % d) (range m : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    have h1 : (r + i) % d = (r + j) % d := hij
    have h2 : i % d = j % d := Nat.ModEq.add_left_cancel' r h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  calc ∑ i ∈ range m, n.getD ((r + i) % d) 0
      = ∑ s ∈ (range m).image (fun i => (r + i) % d), n.getD s 0 :=
        (Finset.sum_image (f := fun s => n.getD s 0) hinj).symm
    _ ≤ ∑ s ∈ range d, n.getD s 0 := by
        apply Finset.sum_le_sum_of_subset
        intro s hs
        simp only [mem_image, mem_range] at hs ⊢
        obtain ⟨i, _, rfl⟩ := hs
        exact Nat.mod_lt _ hd

/-! ### Enclosures of `P`, `u` and `v` -/

/-- Table of enclosures of `Ĝ(J/q)`, `J = 0, …, dq`. -/
def gTab (d q : ℕ) : List QI :=
  let clT := clTab (4 * d * q) (2 * d * q)
  (List.range (d * q + 1)).map fun J => gEnc d q clT J

theorem mem_gTab {d q J : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hJ : J ≤ d * q) :
    ((gTab d q).getD J default).Mem (coneGhat d ((J : ℝ) / q)) := by
  unfold gTab
  simp only
  rw [QI.getD_map_range _ _ _ (by omega)]
  exact mem_gEnc hd hq (by nlinarith)

/-- Enclosure of `P(m) = (1/d) ∑_{r<d} Ĝ(S_r(m))` for the cell `n/q`. -/
def pEnc (d : ℕ) (gT : List QI) (n : List ℕ) (m : ℕ) : QI :=
  QI.smul (1 / (d : ℚ)) (QI.sumRange d fun r => gT.getD (winN d n r m) default)

theorem mem_pEnc {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) {n : List ℕ}
    (hn : ∑ s ∈ range d, n.getD s 0 = d * q) {m : ℕ} (hm : m ≤ d) :
    (pEnc d (gTab d q) n m).Mem (coneP d (cellVec q n) m) := by
  unfold pEnc coneP
  have h : (QI.sumRange d fun r => (gTab d q).getD (winN d n r m) default).Mem
      (∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m)) := by
    apply QI.mem_sumRange
    intro r _
    rw [coneWindowSum_cellVec]
    have hJ : winN d n r m ≤ d * q := (winN_le (by omega) n r hm).trans hn.le
    exact mem_gTab hd hq hJ
  have e : (∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m)) / (d : ℝ) =
      ((1 / (d : ℚ) : ℚ) : ℝ) * ∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m) := by
    push_cast; ring
  rw [e]
  exact h.smul _

/-- The list of enclosures of `P(0), …, P(d)`. -/
def pList (d : ℕ) (gT : List QI) (n : List ℕ) : List QI :=
  (List.range (d + 1)).map fun m => pEnc d gT n m

/-- `u_m = P(m+1) - 2 P(m) + P(m-1)` from the list of `P` enclosures. -/
def uFromP (pL : List QI) (m : ℕ) : QI :=
  QI.add (QI.sub (pL.getD (m + 1) default) (QI.smul 2 (pL.getD m default))) (pL.getD (m - 1) default)

/-- Enclosures of `u^ℓ_1, …, u^ℓ_{d-1}` for the cell `ℓ = n/q`. -/
def uList (d : ℕ) (gT : List QI) (n : List ℕ) : List QI :=
  let pL := pList d gT n
  (List.range (d - 1)).map fun i => uFromP pL (i + 1)

theorem mem_uList {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) {n : List ℕ}
    (hn : ∑ s ∈ range d, n.getD s 0 = d * q) {i : ℕ} (hi : i < d - 1) :
    ((uList d (gTab d q) n).getD i default).Mem (coneU d (cellVec q n) (i + 1)) := by
  unfold uList
  simp only
  rw [QI.getD_map_range _ _ _ hi]
  unfold uFromP coneU pList
  rw [QI.getD_map_range _ _ _ (by omega), QI.getD_map_range _ _ _ (by omega),
    QI.getD_map_range _ _ _ (by omega)]
  have h1 := mem_pEnc hd hq hn (m := i + 1 + 1) (by omega)
  have h2 := mem_pEnc hd hq hn (m := i + 1) (by omega)
  have h3 := mem_pEnc hd hq hn (m := i + 1 - 1) (by omega)
  have h := (h1.sub (h2.smul 2)).add h3
  have e : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [e] at h
  exact h

/-- Enclosure of `v_m = 2/sin(π m/(2d))`; sound when the enclosure of the sine is positive. -/
def sinV (d m : ℕ) : QI := sinPi ((m : ℚ) / (2 * d))

def vEnc (d m : ℕ) : QI := QI.round prec (QI.smul 2 (QI.inv (sinV d m)))

theorem mem_vEnc {d m : ℕ} (h : 0 < (sinV d m).lo) : (vEnc d m).Mem (coneV d m) := by
  unfold vEnc coneV
  apply QI.Mem.round
  have hs := mem_sinPi ((m : ℚ) / (2 * d))
  have e : π * (((m : ℚ) / (2 * d) : ℚ) : ℝ) = π * m / (2 * d) := by push_cast; ring
  rw [e] at hs
  have h2 := (hs.inv h).smul 2
  have e2 : ((2 : ℚ) : ℝ) * (1 / Real.sin (π * m / (2 * d))) = 2 / Real.sin (π * m / (2 * d)) := by
    push_cast; ring
  rw [e2] at h2
  exact h2

/-! ### The complete check -/

namespace ConeCertificate

/-- Enclosures of the matrix entries `U_{i,k} = u^{ℓ^(k)}_{i+1}`, one list per cell. -/
def uTable (c : ConeCertificate) : List (List QI) :=
  let gT := gTab c.d c.q
  c.cells.map fun n => uList c.d gT n

/-- Enclosures of `v_{i+1}`, `i < d-1`. -/
def vTable (c : ConeCertificate) : List QI :=
  (List.range (c.d - 1)).map fun i => vEnc c.d (i + 1)

/-- The complete check of a CONE_d certificate. -/
def fullCheck (c : ConeCertificate) : Bool :=
  let UT := c.uTable
  let vT := c.vTable
  decide (1 ≤ c.d) &&
    (List.range (c.d - 1)).all (fun i => decide (0 < (sinV c.d (i + 1)).lo)) &&
    c.check (fun i k => (UT.getD k []).getD i default) (fun i => vT.getD i default)

theorem getD_map_of_lt {α β : Type*} (f : α → β) (l : List α) (a : α) (b : β) {k : ℕ}
    (hk : k < l.length) : (l.map f).getD k b = f (l.getD k a) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  rfl

/-- **Soundness of the complete check, strong form**: all cells are cell vectors and every weight is positive. -/
theorem fullCheck_sound_strong (c : ConeCertificate) (h : c.fullCheck = true) :
    (∀ k < c.cells.length, IsConeCell c.d (cellVec c.q (c.cells.getD k []))) ∧
      ∃ x : ℕ → ℝ, (∀ k < c.cells.length, 0 < x k) ∧
        ∀ m : ℕ, 1 ≤ m → m ≤ c.d - 1 →
          ∑ k : Fin c.cells.length, x k * coneU c.d (cellVec c.q (c.cells.getD k [])) m = coneV c.d m := by
  unfold fullCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hd, hsin⟩, hcheck⟩ := h
  -- validity of the cells, read off from the check
  have hcells := hcheck
  unfold check at hcells
  rw [Bool.and_eq_true] at hcells
  have hok := hcells.1
  unfold cellsOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨hq, hsums⟩ := hok
  refine c.sound_strong _ _ ?_ ?_ hcheck
  · intro i hi k hk
    unfold uTable
    simp only
    rw [getD_map_of_lt _ _ [] _ hk]
    have hn : ∑ s ∈ range c.d, (c.cells.getD k []).getD s 0 = c.d * c.q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hsums _ (List.getElem_mem _)
    exact mem_uList hd hq hn hi
  · intro i hi
    unfold vTable
    rw [QI.getD_map_range _ _ _ hi]
    exact mem_vEnc (hsin i hi)

/-- **Soundness of the complete check.** -/
theorem fullCheck_sound (c : ConeCertificate) (h : c.fullCheck = true) : ConeCert c.d := by
  obtain ⟨hcell, x, hxpos, hxeq⟩ := c.fullCheck_sound_strong h
  exact ⟨c.cells.length, fun k => cellVec c.q (c.cells.getD k []), fun k => x k,
    fun k => hcell k k.2, fun k => (hxpos k k.2).le, hxeq⟩

end ConeCertificate

end OQP27
