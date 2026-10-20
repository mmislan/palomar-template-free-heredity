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

theorem strong_row_528 :
    (checkStrongRecoveryChemical 528 false && checkStrongRecoveryChemical 528 true &&
      checkStrongRecoveryShape 528) = true := by decide +kernel

theorem strong_row_529 :
    (checkStrongRecoveryChemical 529 false && checkStrongRecoveryChemical 529 true &&
      checkStrongRecoveryShape 529) = true := by decide +kernel

theorem strong_row_530 :
    (checkStrongRecoveryChemical 530 false && checkStrongRecoveryChemical 530 true &&
      checkStrongRecoveryShape 530) = true := by decide +kernel

theorem strong_row_531 :
    (checkStrongRecoveryChemical 531 false && checkStrongRecoveryChemical 531 true &&
      checkStrongRecoveryShape 531) = true := by decide +kernel

theorem strong_row_532 :
    (checkStrongRecoveryChemical 532 false && checkStrongRecoveryChemical 532 true &&
      checkStrongRecoveryShape 532) = true := by decide +kernel

theorem strong_row_533 :
    (checkStrongRecoveryChemical 533 false && checkStrongRecoveryChemical 533 true &&
      checkStrongRecoveryShape 533) = true := by decide +kernel

theorem strong_row_534 :
    (checkStrongRecoveryChemical 534 false && checkStrongRecoveryChemical 534 true &&
      checkStrongRecoveryShape 534) = true := by decide +kernel

theorem strong_row_535 :
    (checkStrongRecoveryChemical 535 false && checkStrongRecoveryChemical 535 true &&
      checkStrongRecoveryShape 535) = true := by decide +kernel

theorem strong_row_536 :
    (checkStrongRecoveryChemical 536 false && checkStrongRecoveryChemical 536 true &&
      checkStrongRecoveryShape 536) = true := by decide +kernel

theorem strong_row_537 :
    (checkStrongRecoveryChemical 537 false && checkStrongRecoveryChemical 537 true &&
      checkStrongRecoveryShape 537) = true := by decide +kernel

theorem strong_row_538 :
    (checkStrongRecoveryChemical 538 false && checkStrongRecoveryChemical 538 true &&
      checkStrongRecoveryShape 538) = true := by decide +kernel

theorem strong_row_539 :
    (checkStrongRecoveryChemical 539 false && checkStrongRecoveryChemical 539 true &&
      checkStrongRecoveryShape 539) = true := by decide +kernel

theorem strong_row_540 :
    (checkStrongRecoveryChemical 540 false && checkStrongRecoveryChemical 540 true &&
      checkStrongRecoveryShape 540) = true := by decide +kernel

theorem strong_row_541 :
    (checkStrongRecoveryChemical 541 false && checkStrongRecoveryChemical 541 true &&
      checkStrongRecoveryShape 541) = true := by decide +kernel

theorem strong_row_542 :
    (checkStrongRecoveryChemical 542 false && checkStrongRecoveryChemical 542 true &&
      checkStrongRecoveryShape 542) = true := by decide +kernel

theorem strong_row_543 :
    (checkStrongRecoveryChemical 543 false && checkStrongRecoveryChemical 543 true &&
      checkStrongRecoveryShape 543) = true := by decide +kernel

theorem strong_recovery_rows_528_543 :
    (List.range' 528 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_528, strong_row_529, strong_row_530, strong_row_531, strong_row_532, strong_row_533, strong_row_534, strong_row_535, strong_row_536, strong_row_537, strong_row_538, strong_row_539, strong_row_540, strong_row_541, strong_row_542, strong_row_543, Bool.and_self]

end P161Formal
