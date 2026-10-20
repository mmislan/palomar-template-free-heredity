module

public import P161Formal.StrongRecoveryProfile

/-! Separate exact lower-count recovery decisions, selected15/8,220 witness.
Both chemical rows and shape are checked by ordinary kernel reduction.
This source makes no stochastic or full-mission assertion. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem strong_row_496 :
    (checkStrongRecoveryChemical 496 false && checkStrongRecoveryChemical 496 true &&
      checkStrongRecoveryShape 496) = true := by decide +kernel

theorem strong_row_497 :
    (checkStrongRecoveryChemical 497 false && checkStrongRecoveryChemical 497 true &&
      checkStrongRecoveryShape 497) = true := by decide +kernel

theorem strong_row_498 :
    (checkStrongRecoveryChemical 498 false && checkStrongRecoveryChemical 498 true &&
      checkStrongRecoveryShape 498) = true := by decide +kernel

theorem strong_row_499 :
    (checkStrongRecoveryChemical 499 false && checkStrongRecoveryChemical 499 true &&
      checkStrongRecoveryShape 499) = true := by decide +kernel

theorem strong_row_500 :
    (checkStrongRecoveryChemical 500 false && checkStrongRecoveryChemical 500 true &&
      checkStrongRecoveryShape 500) = true := by decide +kernel

theorem strong_row_501 :
    (checkStrongRecoveryChemical 501 false && checkStrongRecoveryChemical 501 true &&
      checkStrongRecoveryShape 501) = true := by decide +kernel

theorem strong_row_502 :
    (checkStrongRecoveryChemical 502 false && checkStrongRecoveryChemical 502 true &&
      checkStrongRecoveryShape 502) = true := by decide +kernel

theorem strong_row_503 :
    (checkStrongRecoveryChemical 503 false && checkStrongRecoveryChemical 503 true &&
      checkStrongRecoveryShape 503) = true := by decide +kernel

theorem strong_row_504 :
    (checkStrongRecoveryChemical 504 false && checkStrongRecoveryChemical 504 true &&
      checkStrongRecoveryShape 504) = true := by decide +kernel

theorem strong_row_505 :
    (checkStrongRecoveryChemical 505 false && checkStrongRecoveryChemical 505 true &&
      checkStrongRecoveryShape 505) = true := by decide +kernel

theorem strong_row_506 :
    (checkStrongRecoveryChemical 506 false && checkStrongRecoveryChemical 506 true &&
      checkStrongRecoveryShape 506) = true := by decide +kernel

theorem strong_row_507 :
    (checkStrongRecoveryChemical 507 false && checkStrongRecoveryChemical 507 true &&
      checkStrongRecoveryShape 507) = true := by decide +kernel

theorem strong_row_508 :
    (checkStrongRecoveryChemical 508 false && checkStrongRecoveryChemical 508 true &&
      checkStrongRecoveryShape 508) = true := by decide +kernel

theorem strong_row_509 :
    (checkStrongRecoveryChemical 509 false && checkStrongRecoveryChemical 509 true &&
      checkStrongRecoveryShape 509) = true := by decide +kernel

theorem strong_row_510 :
    (checkStrongRecoveryChemical 510 false && checkStrongRecoveryChemical 510 true &&
      checkStrongRecoveryShape 510) = true := by decide +kernel

theorem strong_row_511 :
    (checkStrongRecoveryChemical 511 false && checkStrongRecoveryChemical 511 true &&
      checkStrongRecoveryShape 511) = true := by decide +kernel

theorem strong_recovery_rows_496_511 :
    (List.range' 496 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_496, strong_row_497, strong_row_498, strong_row_499, strong_row_500, strong_row_501, strong_row_502, strong_row_503, strong_row_504, strong_row_505, strong_row_506, strong_row_507, strong_row_508, strong_row_509, strong_row_510, strong_row_511, Bool.and_self]

end P161Formal
