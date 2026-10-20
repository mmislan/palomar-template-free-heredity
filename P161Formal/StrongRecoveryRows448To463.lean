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

theorem strong_row_448 :
    (checkStrongRecoveryChemical 448 false && checkStrongRecoveryChemical 448 true &&
      checkStrongRecoveryShape 448) = true := by decide +kernel

theorem strong_row_449 :
    (checkStrongRecoveryChemical 449 false && checkStrongRecoveryChemical 449 true &&
      checkStrongRecoveryShape 449) = true := by decide +kernel

theorem strong_row_450 :
    (checkStrongRecoveryChemical 450 false && checkStrongRecoveryChemical 450 true &&
      checkStrongRecoveryShape 450) = true := by decide +kernel

theorem strong_row_451 :
    (checkStrongRecoveryChemical 451 false && checkStrongRecoveryChemical 451 true &&
      checkStrongRecoveryShape 451) = true := by decide +kernel

theorem strong_row_452 :
    (checkStrongRecoveryChemical 452 false && checkStrongRecoveryChemical 452 true &&
      checkStrongRecoveryShape 452) = true := by decide +kernel

theorem strong_row_453 :
    (checkStrongRecoveryChemical 453 false && checkStrongRecoveryChemical 453 true &&
      checkStrongRecoveryShape 453) = true := by decide +kernel

theorem strong_row_454 :
    (checkStrongRecoveryChemical 454 false && checkStrongRecoveryChemical 454 true &&
      checkStrongRecoveryShape 454) = true := by decide +kernel

theorem strong_row_455 :
    (checkStrongRecoveryChemical 455 false && checkStrongRecoveryChemical 455 true &&
      checkStrongRecoveryShape 455) = true := by decide +kernel

theorem strong_row_456 :
    (checkStrongRecoveryChemical 456 false && checkStrongRecoveryChemical 456 true &&
      checkStrongRecoveryShape 456) = true := by decide +kernel

theorem strong_row_457 :
    (checkStrongRecoveryChemical 457 false && checkStrongRecoveryChemical 457 true &&
      checkStrongRecoveryShape 457) = true := by decide +kernel

theorem strong_row_458 :
    (checkStrongRecoveryChemical 458 false && checkStrongRecoveryChemical 458 true &&
      checkStrongRecoveryShape 458) = true := by decide +kernel

theorem strong_row_459 :
    (checkStrongRecoveryChemical 459 false && checkStrongRecoveryChemical 459 true &&
      checkStrongRecoveryShape 459) = true := by decide +kernel

theorem strong_row_460 :
    (checkStrongRecoveryChemical 460 false && checkStrongRecoveryChemical 460 true &&
      checkStrongRecoveryShape 460) = true := by decide +kernel

theorem strong_row_461 :
    (checkStrongRecoveryChemical 461 false && checkStrongRecoveryChemical 461 true &&
      checkStrongRecoveryShape 461) = true := by decide +kernel

theorem strong_row_462 :
    (checkStrongRecoveryChemical 462 false && checkStrongRecoveryChemical 462 true &&
      checkStrongRecoveryShape 462) = true := by decide +kernel

theorem strong_row_463 :
    (checkStrongRecoveryChemical 463 false && checkStrongRecoveryChemical 463 true &&
      checkStrongRecoveryShape 463) = true := by decide +kernel

theorem strong_recovery_rows_448_463 :
    (List.range' 448 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_448, strong_row_449, strong_row_450, strong_row_451, strong_row_452, strong_row_453, strong_row_454, strong_row_455, strong_row_456, strong_row_457, strong_row_458, strong_row_459, strong_row_460, strong_row_461, strong_row_462, strong_row_463, Bool.and_self]

end P161Formal
