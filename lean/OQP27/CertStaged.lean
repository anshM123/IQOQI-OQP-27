import OQP27.CertPipeline

/-!
# Two-stage version of the complete check (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For larger `d` the single kernel evaluation of `OQP27.ConeCertificate.fullCheck` needs much memory.  Here the
check is split into two kernel evaluations, in two separate declarations:
1. the table of enclosures of the cell directions is computed and compared with a literal table `UT`
   (`OQP27.qiTableEqb c.uTable UT = true`, hence `c.uTable = UT` by `OQP27.qiTableEqb_eq`);
2. the rest of the check is run on the literal table (`OQP27.ConeCertificate.fullCheckU c UT = true`).

`OQP27.ConeCertificate.fullCheck_of_fullCheckU`: `c.uTable = UT → c.fullCheckU UT = true → c.fullCheck = true`, hence
(`OQP27.ConeCertificate.fullCheckU_sound`) `ConeCert c.d`.
The literal table is untrusted data: stage 1 proves that it equals the computed table.

No hypotheses.
-/

namespace OQP27

open Finset

/-- Boolean equality of rational intervals. -/
def qiEqb (a b : QI) : Bool := decide (a.lo = b.lo) && decide (a.hi = b.hi)

/-- Boolean equality of lists of rational intervals. -/
def qiListEqb : List QI → List QI → Bool
  | [], [] => true
  | a :: as, b :: bs => qiEqb a b && qiListEqb as bs
  | _, _ => false

/-- Boolean equality of tables of rational intervals. -/
def qiTableEqb : List (List QI) → List (List QI) → Bool
  | [], [] => true
  | a :: as, b :: bs => qiListEqb a b && qiTableEqb as bs
  | _, _ => false

theorem qiEqb_eq {a b : QI} (h : qiEqb a b = true) : a = b := by
  unfold qiEqb at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases a; cases b
  simp only [QI.mk.injEq]
  exact h

theorem qiListEqb_eq : ∀ {a b : List QI}, qiListEqb a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    unfold qiListEqb at h
    rw [Bool.and_eq_true] at h
    rw [qiEqb_eq h.1, qiListEqb_eq h.2]
  | [], _ :: _, h => by simp [qiListEqb] at h
  | _ :: _, [], h => by simp [qiListEqb] at h

theorem qiTableEqb_eq : ∀ {a b : List (List QI)}, qiTableEqb a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    unfold qiTableEqb at h
    rw [Bool.and_eq_true] at h
    rw [qiListEqb_eq h.1, qiTableEqb_eq h.2]
  | [], _ :: _, h => by simp [qiTableEqb] at h
  | _ :: _, [], h => by simp [qiTableEqb] at h

namespace ConeCertificate

/-- The complete check with the table of `u`-enclosures supplied as `UT`. -/
def fullCheckU (c : ConeCertificate) (UT : List (List QI)) : Bool :=
  let vT := c.vTable
  decide (1 ≤ c.d) &&
    (List.range (c.d - 1)).all (fun i => decide (0 < (sinV c.d (i + 1)).lo)) &&
    c.check (fun i k => (UT.getD k []).getD i default) (fun i => vT.getD i default)

theorem fullCheck_eq_fullCheckU (c : ConeCertificate) : c.fullCheck = c.fullCheckU c.uTable := rfl

/-- The two stages together give the complete check. -/
theorem fullCheck_of_fullCheckU (c : ConeCertificate) (UT : List (List QI)) (hUT : c.uTable = UT)
    (h : c.fullCheckU UT = true) : c.fullCheck = true := by
  rw [fullCheck_eq_fullCheckU, hUT]
  exact h

/-- **Soundness of the two-stage check.** -/
theorem fullCheckU_sound (c : ConeCertificate) (UT : List (List QI)) (hUT : c.uTable = UT)
    (h : c.fullCheckU UT = true) : ConeCert c.d :=
  c.fullCheck_sound (c.fullCheck_of_fullCheckU UT hUT h)

end ConeCertificate

end OQP27
