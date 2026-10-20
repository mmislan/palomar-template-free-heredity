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

theorem strong_row_512 :
    (checkStrongRecoveryChemical 512 false && checkStrongRecoveryChemical 512 true &&
      checkStrongRecoveryShape 512) = true := by decide +kernel

theorem strong_row_513 :
    (checkStrongRecoveryChemical 513 false && checkStrongRecoveryChemical 513 true &&
      checkStrongRecoveryShape 513) = true := by decide +kernel

theorem strong_row_514 :
    (checkStrongRecoveryChemical 514 false && checkStrongRecoveryChemical 514 true &&
      checkStrongRecoveryShape 514) = true := by decide +kernel

theorem strong_row_515 :
    (checkStrongRecoveryChemical 515 false && checkStrongRecoveryChemical 515 true &&
      checkStrongRecoveryShape 515) = true := by decide +kernel

theorem strong_row_516 :
    (checkStrongRecoveryChemical 516 false && checkStrongRecoveryChemical 516 true &&
      checkStrongRecoveryShape 516) = true := by decide +kernel

theorem strong_row_517 :
    (checkStrongRecoveryChemical 517 false && checkStrongRecoveryChemical 517 true &&
      checkStrongRecoveryShape 517) = true := by decide +kernel

theorem strong_row_518 :
    (checkStrongRecoveryChemical 518 false && checkStrongRecoveryChemical 518 true &&
      checkStrongRecoveryShape 518) = true := by decide +kernel

theorem strong_row_519 :
    (checkStrongRecoveryChemical 519 false && checkStrongRecoveryChemical 519 true &&
      checkStrongRecoveryShape 519) = true := by decide +kernel

theorem strong_row_520 :
    (checkStrongRecoveryChemical 520 false && checkStrongRecoveryChemical 520 true &&
      checkStrongRecoveryShape 520) = true := by decide +kernel

theorem strong_row_521 :
    (checkStrongRecoveryChemical 521 false && checkStrongRecoveryChemical 521 true &&
      checkStrongRecoveryShape 521) = true := by decide +kernel

theorem strong_row_522 :
    (checkStrongRecoveryChemical 522 false && checkStrongRecoveryChemical 522 true &&
      checkStrongRecoveryShape 522) = true := by decide +kernel

theorem strong_row_523 :
    (checkStrongRecoveryChemical 523 false && checkStrongRecoveryChemical 523 true &&
      checkStrongRecoveryShape 523) = true := by decide +kernel

theorem strong_row_524 :
    (checkStrongRecoveryChemical 524 false && checkStrongRecoveryChemical 524 true &&
      checkStrongRecoveryShape 524) = true := by decide +kernel

theorem strong_row_525 :
    (checkStrongRecoveryChemical 525 false && checkStrongRecoveryChemical 525 true &&
      checkStrongRecoveryShape 525) = true := by decide +kernel

theorem strong_row_526 :
    (checkStrongRecoveryChemical 526 false && checkStrongRecoveryChemical 526 true &&
      checkStrongRecoveryShape 526) = true := by decide +kernel

theorem strong_row_527 :
    (checkStrongRecoveryChemical 527 false && checkStrongRecoveryChemical 527 true &&
      checkStrongRecoveryShape 527) = true := by decide +kernel

theorem strong_recovery_rows_512_527 :
    (List.range' 512 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_512, strong_row_513, strong_row_514, strong_row_515, strong_row_516, strong_row_517, strong_row_518, strong_row_519, strong_row_520, strong_row_521, strong_row_522, strong_row_523, strong_row_524, strong_row_525, strong_row_526, strong_row_527, Bool.and_self]

end P161Formal
