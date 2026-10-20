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

theorem strong_row_480 :
    (checkStrongRecoveryChemical 480 false && checkStrongRecoveryChemical 480 true &&
      checkStrongRecoveryShape 480) = true := by decide +kernel

theorem strong_row_481 :
    (checkStrongRecoveryChemical 481 false && checkStrongRecoveryChemical 481 true &&
      checkStrongRecoveryShape 481) = true := by decide +kernel

theorem strong_row_482 :
    (checkStrongRecoveryChemical 482 false && checkStrongRecoveryChemical 482 true &&
      checkStrongRecoveryShape 482) = true := by decide +kernel

theorem strong_row_483 :
    (checkStrongRecoveryChemical 483 false && checkStrongRecoveryChemical 483 true &&
      checkStrongRecoveryShape 483) = true := by decide +kernel

theorem strong_row_484 :
    (checkStrongRecoveryChemical 484 false && checkStrongRecoveryChemical 484 true &&
      checkStrongRecoveryShape 484) = true := by decide +kernel

theorem strong_row_485 :
    (checkStrongRecoveryChemical 485 false && checkStrongRecoveryChemical 485 true &&
      checkStrongRecoveryShape 485) = true := by decide +kernel

theorem strong_row_486 :
    (checkStrongRecoveryChemical 486 false && checkStrongRecoveryChemical 486 true &&
      checkStrongRecoveryShape 486) = true := by decide +kernel

theorem strong_row_487 :
    (checkStrongRecoveryChemical 487 false && checkStrongRecoveryChemical 487 true &&
      checkStrongRecoveryShape 487) = true := by decide +kernel

theorem strong_row_488 :
    (checkStrongRecoveryChemical 488 false && checkStrongRecoveryChemical 488 true &&
      checkStrongRecoveryShape 488) = true := by decide +kernel

theorem strong_row_489 :
    (checkStrongRecoveryChemical 489 false && checkStrongRecoveryChemical 489 true &&
      checkStrongRecoveryShape 489) = true := by decide +kernel

theorem strong_row_490 :
    (checkStrongRecoveryChemical 490 false && checkStrongRecoveryChemical 490 true &&
      checkStrongRecoveryShape 490) = true := by decide +kernel

theorem strong_row_491 :
    (checkStrongRecoveryChemical 491 false && checkStrongRecoveryChemical 491 true &&
      checkStrongRecoveryShape 491) = true := by decide +kernel

theorem strong_row_492 :
    (checkStrongRecoveryChemical 492 false && checkStrongRecoveryChemical 492 true &&
      checkStrongRecoveryShape 492) = true := by decide +kernel

theorem strong_row_493 :
    (checkStrongRecoveryChemical 493 false && checkStrongRecoveryChemical 493 true &&
      checkStrongRecoveryShape 493) = true := by decide +kernel

theorem strong_row_494 :
    (checkStrongRecoveryChemical 494 false && checkStrongRecoveryChemical 494 true &&
      checkStrongRecoveryShape 494) = true := by decide +kernel

theorem strong_row_495 :
    (checkStrongRecoveryChemical 495 false && checkStrongRecoveryChemical 495 true &&
      checkStrongRecoveryShape 495) = true := by decide +kernel

theorem strong_recovery_rows_480_495 :
    (List.range' 480 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_480, strong_row_481, strong_row_482, strong_row_483, strong_row_484, strong_row_485, strong_row_486, strong_row_487, strong_row_488, strong_row_489, strong_row_490, strong_row_491, strong_row_492, strong_row_493, strong_row_494, strong_row_495, Bool.and_self]

end P161Formal
