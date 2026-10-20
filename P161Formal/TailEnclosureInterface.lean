module

public import P161Formal.RecoveryProfile

/-! Exact high-tail enclosure and cubic relative-gap predicate.
The geometric gap is handled uniformly, so it is not enumerated here. -/

@[expose] public section
namespace P161Formal

def checkTailEnclosureParent (a : ℕ) : Bool :=
  checkTailEnclosure a false && checkTailEnclosure a true &&
    (if a < 768 then decide (0 ≤ recoveryTailDeltaQ a ∧
      recoveryTailDeltaQ a ≤ recoveryTailAQ a / 10000) else true)

theorem checked_tail_enclosure_false (a : ℕ) (h : checkTailEnclosureParent a = true) :
    checkTailEnclosure a false = true := by
  simp only [checkTailEnclosureParent, Bool.and_eq_true] at h
  exact h.1.1

theorem checked_tail_enclosure_true (a : ℕ) (h : checkTailEnclosureParent a = true) :
    checkTailEnclosure a true = true := by
  simp only [checkTailEnclosureParent, Bool.and_eq_true] at h
  exact h.1.2

theorem checked_cubic_gap (a : ℕ) (ha : a < 768) (h : checkTailEnclosureParent a = true) :
    0 ≤ recoveryTailDeltaQ a ∧ recoveryTailDeltaQ a ≤ recoveryTailAQ a / 10000 := by
  simp only [checkTailEnclosureParent, Bool.and_eq_true, ite_eq_left ha,
    decide_eq_true_eq] at h
  exact h.2

end P161Formal
