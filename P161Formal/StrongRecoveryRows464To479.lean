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

theorem strong_row_464 :
    (checkStrongRecoveryChemical 464 false && checkStrongRecoveryChemical 464 true &&
      checkStrongRecoveryShape 464) = true := by decide +kernel

theorem strong_row_465 :
    (checkStrongRecoveryChemical 465 false && checkStrongRecoveryChemical 465 true &&
      checkStrongRecoveryShape 465) = true := by decide +kernel

theorem strong_row_466 :
    (checkStrongRecoveryChemical 466 false && checkStrongRecoveryChemical 466 true &&
      checkStrongRecoveryShape 466) = true := by decide +kernel

theorem strong_row_467 :
    (checkStrongRecoveryChemical 467 false && checkStrongRecoveryChemical 467 true &&
      checkStrongRecoveryShape 467) = true := by decide +kernel

theorem strong_row_468 :
    (checkStrongRecoveryChemical 468 false && checkStrongRecoveryChemical 468 true &&
      checkStrongRecoveryShape 468) = true := by decide +kernel

theorem strong_row_469 :
    (checkStrongRecoveryChemical 469 false && checkStrongRecoveryChemical 469 true &&
      checkStrongRecoveryShape 469) = true := by decide +kernel

theorem strong_row_470 :
    (checkStrongRecoveryChemical 470 false && checkStrongRecoveryChemical 470 true &&
      checkStrongRecoveryShape 470) = true := by decide +kernel

theorem strong_row_471 :
    (checkStrongRecoveryChemical 471 false && checkStrongRecoveryChemical 471 true &&
      checkStrongRecoveryShape 471) = true := by decide +kernel

theorem strong_row_472 :
    (checkStrongRecoveryChemical 472 false && checkStrongRecoveryChemical 472 true &&
      checkStrongRecoveryShape 472) = true := by decide +kernel

theorem strong_row_473 :
    (checkStrongRecoveryChemical 473 false && checkStrongRecoveryChemical 473 true &&
      checkStrongRecoveryShape 473) = true := by decide +kernel

theorem strong_row_474 :
    (checkStrongRecoveryChemical 474 false && checkStrongRecoveryChemical 474 true &&
      checkStrongRecoveryShape 474) = true := by decide +kernel

theorem strong_row_475 :
    (checkStrongRecoveryChemical 475 false && checkStrongRecoveryChemical 475 true &&
      checkStrongRecoveryShape 475) = true := by decide +kernel

theorem strong_row_476 :
    (checkStrongRecoveryChemical 476 false && checkStrongRecoveryChemical 476 true &&
      checkStrongRecoveryShape 476) = true := by decide +kernel

theorem strong_row_477 :
    (checkStrongRecoveryChemical 477 false && checkStrongRecoveryChemical 477 true &&
      checkStrongRecoveryShape 477) = true := by decide +kernel

theorem strong_row_478 :
    (checkStrongRecoveryChemical 478 false && checkStrongRecoveryChemical 478 true &&
      checkStrongRecoveryShape 478) = true := by decide +kernel

theorem strong_row_479 :
    (checkStrongRecoveryChemical 479 false && checkStrongRecoveryChemical 479 true &&
      checkStrongRecoveryShape 479) = true := by decide +kernel

theorem strong_recovery_rows_464_479 :
    (List.range' 464 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_464, strong_row_465, strong_row_466, strong_row_467, strong_row_468, strong_row_469, strong_row_470, strong_row_471, strong_row_472, strong_row_473, strong_row_474, strong_row_475, strong_row_476, strong_row_477, strong_row_478, strong_row_479, Bool.and_self]

end P161Formal
