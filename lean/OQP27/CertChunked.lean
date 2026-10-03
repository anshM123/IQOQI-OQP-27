import OQP27.CertStaged
import Mathlib.Data.List.GetD

/-!
# Chunked computation of the Clausen table (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For certificates with a large denominator `q` (such as the LP certificates of `QD2/certs`, `q = 16`) the Clausen
table `Cl₂(2π c/Q)`, `Q = 4dq`, is too large for a single kernel evaluation.  This file allows it to be
assembled from pieces checked in separate declarations:
* `OQP27.ClChunkOK Q lo L`: `L` lists enclosures of `Cl₂(2π(lo+i)/Q)`, `i < L.length`;
  `OQP27.clChunkOK_clChunk` (a computed chunk is sound) and `OQP27.clChunkOK_append` (chunks concatenate);
* `OQP27.GTabOK d q gT`: `gT` lists enclosures of `Ĝ(J/q)`, `J ≤ dq`; `OQP27.gTabOK_gTabOf` builds it from a
  sound Clausen table;
* `OQP27.ConeCertificate.fullCheckWith_sound`: the complete check, run with any sound `Ĝ` table, proves
  `ConeCert d`.

No hypotheses.
-/

namespace OQP27

open Finset Real

/-! ### Chunks of the Clausen table -/

/-- `L` lists enclosures of `Cl₂(2π(lo+i)/Q)`, `i < L.length`. -/
def ClChunkOK (Q lo : ℕ) (L : List QI) : Prop :=
  ∀ i < L.length, (L.getD i default).Mem (clausen2 (2 * π * ((lo + i : ℕ) : ℝ) / Q))

theorem clChunkOK_nil (Q lo : ℕ) : ClChunkOK Q lo [] := fun i hi => absurd hi (by simp)

theorem clChunkOK_append {Q lo : ℕ} {A B : List QI} (hA : ClChunkOK Q lo A)
    (hB : ClChunkOK Q (lo + A.length) B) : ClChunkOK Q lo (A ++ B) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < A.length
  · rw [List.getD_append _ _ _ _ h]
    exact hA i h
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have h2 := hB (i - A.length) (by omega)
    have e : lo + A.length + (i - A.length) = lo + i := by omega
    rw [e] at h2
    exact h2

/-- `OQP27.clChunkOK_append` with the offset of the second chunk given explicitly. -/
theorem clChunkOK_append' {Q lo a lo' : ℕ} {A B : List QI} (hA : ClChunkOK Q lo A) (hlen : A.length = a)
    (hlo : lo + a = lo') (hB : ClChunkOK Q lo' B) : ClChunkOK Q lo (A ++ B) := by
  subst hlen; subst hlo; exact clChunkOK_append hA hB

/-- Enclosures of `Cl₂(2π(lo+i)/Q)`, `i < len`, from given tables of sines and of `H(Q, ·)`. -/
def clChunk (Q : ℕ) (sT hT : List QI) (lo len : ℕ) : List QI :=
  (List.range len).map fun i => clEnc Q sT hT (lo + i)

theorem clChunkOK_clChunk {Q : ℕ} (hQ : 1 ≤ Q) (lo len : ℕ) :
    ClChunkOK Q lo (clChunk Q (sinTab Q) (hTab Q) lo len) := by
  intro i hi
  unfold clChunk at hi ⊢
  rw [List.length_map, List.length_range] at hi
  rw [QI.getD_map_range _ _ _ hi]
  exact mem_clEnc hQ (lo + i)

/-- A literal chunk that equals a computed chunk (with literal sine and `H` tables equal to the computed ones)
is sound. -/
theorem clChunkOK_of_eq {Q : ℕ} (hQ : 1 ≤ Q) {sT hT L : List QI} (hs : sinTab Q = sT) (hh : hTab Q = hT)
    {lo len : ℕ} (hL : clChunk Q sT hT lo len = L) : ClChunkOK Q lo L := by
  rw [← hL, ← hs, ← hh]
  exact clChunkOK_clChunk hQ lo len

/-! ### `Ĝ` tables -/

/-- `gT` lists enclosures of `Ĝ(J/q)`, `J = 0, …, dq`. -/
def GTabOK (d q : ℕ) (gT : List QI) : Prop :=
  ∀ J ≤ d * q, (gT.getD J default).Mem (coneGhat d ((J : ℝ) / q))

/-- The `Ĝ` table computed from a given Clausen table. -/
def gTabOf (d q : ℕ) (clT : List QI) : List QI :=
  (List.range (d * q + 1)).map fun J => gEnc d q clT J

theorem gTabOK_gTabOf {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) {clT : List QI}
    (hcl : ClChunkOK (4 * d * q) 0 clT) (hlen : 2 * d * q < clT.length) :
    GTabOK d q (gTabOf d q clT) := by
  intro J hJ
  unfold gTabOf
  rw [QI.getD_map_range _ _ _ (by omega)]
  have hJ2 : J ≤ 2 * d * q := by nlinarith
  unfold gEnc
  rw [coneGhat_rat hd hq hJ2]
  apply QI.Mem.round
  have h1 := hcl J (by omega)
  have h2 := hcl (2 * d * q - J) (by omega)
  simp only [Nat.zero_add] at h1 h2
  have h := ((mem_factorEnc d).mul (h1.add h2)).neg
  rw [neg_mul]
  exact h

theorem gTabOK_gTab {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) : GTabOK d q (gTab d q) :=
  fun _ hJ => mem_gTab hd hq hJ

/-! ### Cell directions from a sound `Ĝ` table -/

theorem mem_pEnc_of {d q : ℕ} (hd : 1 ≤ d) {gT : List QI} (hg : GTabOK d q gT) {n : List ℕ}
    (hn : ∑ s ∈ range d, n.getD s 0 = d * q) {m : ℕ} (hm : m ≤ d) :
    (pEnc d gT n m).Mem (coneP d (cellVec q n) m) := by
  unfold pEnc coneP
  have h : (QI.sumRange d fun r => gT.getD (winN d n r m) default).Mem
      (∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m)) := by
    apply QI.mem_sumRange
    intro r _
    rw [coneWindowSum_cellVec]
    exact hg _ ((winN_le (by omega) n r hm).trans hn.le)
  have e : (∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m)) / (d : ℝ) =
      ((1 / (d : ℚ) : ℚ) : ℝ) * ∑ r ∈ range d, coneGhat d (coneWindowSum d (cellVec q n) r m) := by
    push_cast; ring
  rw [e]
  exact h.smul _

theorem mem_uList_of {d q : ℕ} (hd : 1 ≤ d) {gT : List QI} (hg : GTabOK d q gT) {n : List ℕ}
    (hn : ∑ s ∈ range d, n.getD s 0 = d * q) {i : ℕ} (hi : i < d - 1) :
    ((uList d gT n).getD i default).Mem (coneU d (cellVec q n) (i + 1)) := by
  unfold uList
  simp only
  rw [QI.getD_map_range _ _ _ hi]
  unfold uFromP coneU pList
  rw [QI.getD_map_range _ _ _ (by omega), QI.getD_map_range _ _ _ (by omega),
    QI.getD_map_range _ _ _ (by omega)]
  have h1 := mem_pEnc_of hd hg hn (m := i + 1 + 1) (by omega)
  have h2 := mem_pEnc_of hd hg hn (m := i + 1) (by omega)
  have h3 := mem_pEnc_of hd hg hn (m := i + 1 - 1) (by omega)
  have h := (h1.sub (h2.smul 2)).add h3
  have e : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [e] at h
  exact h

namespace ConeCertificate

/-- The table of `u`-enclosures computed from a given `Ĝ` table. -/
def uTableWith (c : ConeCertificate) (gT : List QI) : List (List QI) :=
  c.cells.map fun n => uList c.d gT n

/-- **Soundness of the complete check with a supplied `Ĝ` table.** -/
theorem fullCheckWith_sound (c : ConeCertificate) (gT : List QI) (hg : GTabOK c.d c.q gT)
    (h : c.fullCheckU (c.uTableWith gT) = true) : ConeCert c.d := by
  unfold fullCheckU at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hd, hsin⟩, hcheck⟩ := h
  have hcells := hcheck
  unfold check at hcells
  rw [Bool.and_eq_true] at hcells
  have hok := hcells.1
  unfold cellsOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨hq, hsums⟩ := hok
  refine c.sound _ _ ?_ ?_ hcheck
  · intro i hi k hk
    unfold uTableWith
    rw [getD_map_of_lt _ _ [] _ hk]
    have hn : ∑ s ∈ range c.d, (c.cells.getD k []).getD s 0 = c.d * c.q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hsums _ (List.getElem_mem _)
    exact mem_uList_of hd hg hn hi
  · intro i hi
    unfold vTable
    rw [QI.getD_map_range _ _ _ hi]
    exact mem_vEnc (hsin i hi)

end ConeCertificate

end OQP27
