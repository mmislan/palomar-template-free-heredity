module

public import P161Formal.StrongRecoveryProfile
public import P161Formal.CubicRecoveryTail
public import Mathlib.Tactic.Linarith

/-! Structural high-count shape of the selected recovery witness.
The low/cubic chemical rows and literal table enclosure are separate. -/

@[expose] public section
namespace P161Formal

theorem strong_geometric_shape (a : ℕ) (ha : 769 ≤ a) (hb : a ≤ 2048) :
    checkStrongRecoveryShape a = true := by
  have hA0 := recovery_geometric_tail_positive a (by omega)
  have hA1 := recovery_tail_at_most_one a (by omega)
  obtain ⟨hc0,hc1⟩ := recovery_tail_coefficient_bounds a (by omega) hb
  simp only [checkStrongRecoveryShape, decide_eq_true_eq,
    strongRecoveryWitnessQ, recoveryAQ, recoveryGapQ,
    ite_eq_right (show ¬a < 512 by omega), ite_true, Bool.false_eq_true,
    ite_false, sub_zero, recovery_tail_delta_factor]
  refine ⟨?_, ?_, ?_, trivial⟩
  · have hc : 0 < 1 - (15/8 : ℚ) * recoveryTailCoefficientQ a := by nlinarith
    have h := mul_pos hA0 hc
    nlinarith
  · have h := mul_nonneg (le_of_lt hA0) (le_of_lt hc0)
    nlinarith
  · nlinarith

end P161Formal
