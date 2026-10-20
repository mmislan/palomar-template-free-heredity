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

theorem strong_row_432 :
    (checkStrongRecoveryChemical 432 false && checkStrongRecoveryChemical 432 true &&
      checkStrongRecoveryShape 432) = true := by decide +kernel

theorem strong_row_433 :
    (checkStrongRecoveryChemical 433 false && checkStrongRecoveryChemical 433 true &&
      checkStrongRecoveryShape 433) = true := by decide +kernel

theorem strong_row_434 :
    (checkStrongRecoveryChemical 434 false && checkStrongRecoveryChemical 434 true &&
      checkStrongRecoveryShape 434) = true := by decide +kernel

theorem strong_row_435 :
    (checkStrongRecoveryChemical 435 false && checkStrongRecoveryChemical 435 true &&
      checkStrongRecoveryShape 435) = true := by decide +kernel

theorem strong_row_436 :
    (checkStrongRecoveryChemical 436 false && checkStrongRecoveryChemical 436 true &&
      checkStrongRecoveryShape 436) = true := by decide +kernel

theorem strong_row_437 :
    (checkStrongRecoveryChemical 437 false && checkStrongRecoveryChemical 437 true &&
      checkStrongRecoveryShape 437) = true := by decide +kernel

theorem strong_row_438 :
    (checkStrongRecoveryChemical 438 false && checkStrongRecoveryChemical 438 true &&
      checkStrongRecoveryShape 438) = true := by decide +kernel

theorem strong_row_439 :
    (checkStrongRecoveryChemical 439 false && checkStrongRecoveryChemical 439 true &&
      checkStrongRecoveryShape 439) = true := by decide +kernel

theorem strong_row_440 :
    (checkStrongRecoveryChemical 440 false && checkStrongRecoveryChemical 440 true &&
      checkStrongRecoveryShape 440) = true := by decide +kernel

theorem strong_row_441 :
    (checkStrongRecoveryChemical 441 false && checkStrongRecoveryChemical 441 true &&
      checkStrongRecoveryShape 441) = true := by decide +kernel

theorem strong_row_442 :
    (checkStrongRecoveryChemical 442 false && checkStrongRecoveryChemical 442 true &&
      checkStrongRecoveryShape 442) = true := by decide +kernel

theorem strong_row_443 :
    (checkStrongRecoveryChemical 443 false && checkStrongRecoveryChemical 443 true &&
      checkStrongRecoveryShape 443) = true := by decide +kernel

theorem strong_row_444 :
    (checkStrongRecoveryChemical 444 false && checkStrongRecoveryChemical 444 true &&
      checkStrongRecoveryShape 444) = true := by decide +kernel

theorem strong_row_445 :
    (checkStrongRecoveryChemical 445 false && checkStrongRecoveryChemical 445 true &&
      checkStrongRecoveryShape 445) = true := by decide +kernel

theorem strong_row_446 :
    (checkStrongRecoveryChemical 446 false && checkStrongRecoveryChemical 446 true &&
      checkStrongRecoveryShape 446) = true := by decide +kernel

theorem strong_row_447 :
    (checkStrongRecoveryChemical 447 false && checkStrongRecoveryChemical 447 true &&
      checkStrongRecoveryShape 447) = true := by decide +kernel

theorem strong_recovery_rows_432_447 :
    (List.range' 432 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_432, strong_row_433, strong_row_434, strong_row_435, strong_row_436, strong_row_437, strong_row_438, strong_row_439, strong_row_440, strong_row_441, strong_row_442, strong_row_443, strong_row_444, strong_row_445, strong_row_446, strong_row_447, Bool.and_self]

end P161Formal
