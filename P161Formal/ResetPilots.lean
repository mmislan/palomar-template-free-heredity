module

public import P161Formal.ResetChecker

/-! Bounded representative pilots only. No all-row residual certificate is
asserted. These tests use the structurally proved integer recurrence. -/

public section
namespace P161Formal

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem reset_join_pilot :
    checkDeficientResetRow 511 false = true ∧ checkDeficientResetRow 511 true = true ∧
    checkGlobalResetRow 511 false = true ∧ checkGlobalResetRow 511 true = true ∧
    checkGlobalResetRow 512 false = true ∧ checkGlobalResetRow 512 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem reset_cap_pilot :
    checkGlobalResetRow 2048 false = true ∧ checkGlobalResetRow 2048 true = true := by
  decide

end P161Formal
