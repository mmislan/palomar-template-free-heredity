module

public import P161Formal.ResetChecker

/-! A single finite-parent test and generic coverage/soundness interface.
The complete literal-data theorem must discharge both list premises. -/

@[expose] public section
namespace P161Formal

def resetParentTest (a : ℕ) : Bool :=
  (checkGlobalResetRow a false && checkGlobalResetRow a true) &&
    if a < 512 then
      checkDeficientResetRow a false && checkDeficientResetRow a true
    else true

theorem parent_test_global (a : ℕ) (h : resetParentTest a = true) :
    checkGlobalResetRow a false = true ∧ checkGlobalResetRow a true = true := by
  simp only [resetParentTest, Bool.and_eq_true] at h
  exact h.1

theorem parent_test_deficient (a : ℕ) (ha : a < 512)
    (h : resetParentTest a = true) :
    checkDeficientResetRow a false = true ∧ checkDeficientResetRow a true = true := by
  simp only [resetParentTest, Bool.and_eq_true, ite_eq_left ha] at h
  exact h.2

theorem covered_parent_checked (parents : List ℕ) (lower count a : ℕ)
    (hcoverage : parents = (List.range count).map (fun i => lower + i))
    (hchecked : parents.all resetParentTest = true)
    (hlower : lower ≤ a) (hupper : a < lower + count) :
    resetParentTest a = true := by
  have hm : a ∈ parents := by
    rw [hcoverage]
    exact List.mem_map.mpr ⟨a - lower, List.mem_range.mpr (by omega), by omega⟩
  exact List.all_eq_true.mp hchecked a hm

end P161Formal
