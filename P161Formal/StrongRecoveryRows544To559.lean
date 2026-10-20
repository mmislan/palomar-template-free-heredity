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

theorem strong_row_544 :
    (checkStrongRecoveryChemical 544 false && checkStrongRecoveryChemical 544 true &&
      checkStrongRecoveryShape 544) = true := by decide +kernel

theorem strong_row_545 :
    (checkStrongRecoveryChemical 545 false && checkStrongRecoveryChemical 545 true &&
      checkStrongRecoveryShape 545) = true := by decide +kernel

theorem strong_row_546 :
    (checkStrongRecoveryChemical 546 false && checkStrongRecoveryChemical 546 true &&
      checkStrongRecoveryShape 546) = true := by decide +kernel

theorem strong_row_547 :
    (checkStrongRecoveryChemical 547 false && checkStrongRecoveryChemical 547 true &&
      checkStrongRecoveryShape 547) = true := by decide +kernel

theorem strong_row_548 :
    (checkStrongRecoveryChemical 548 false && checkStrongRecoveryChemical 548 true &&
      checkStrongRecoveryShape 548) = true := by decide +kernel

theorem strong_row_549 :
    (checkStrongRecoveryChemical 549 false && checkStrongRecoveryChemical 549 true &&
      checkStrongRecoveryShape 549) = true := by decide +kernel

theorem strong_row_550 :
    (checkStrongRecoveryChemical 550 false && checkStrongRecoveryChemical 550 true &&
      checkStrongRecoveryShape 550) = true := by decide +kernel

theorem strong_row_551 :
    (checkStrongRecoveryChemical 551 false && checkStrongRecoveryChemical 551 true &&
      checkStrongRecoveryShape 551) = true := by decide +kernel

theorem strong_row_552 :
    (checkStrongRecoveryChemical 552 false && checkStrongRecoveryChemical 552 true &&
      checkStrongRecoveryShape 552) = true := by decide +kernel

theorem strong_row_553 :
    (checkStrongRecoveryChemical 553 false && checkStrongRecoveryChemical 553 true &&
      checkStrongRecoveryShape 553) = true := by decide +kernel

theorem strong_row_554 :
    (checkStrongRecoveryChemical 554 false && checkStrongRecoveryChemical 554 true &&
      checkStrongRecoveryShape 554) = true := by decide +kernel

theorem strong_row_555 :
    (checkStrongRecoveryChemical 555 false && checkStrongRecoveryChemical 555 true &&
      checkStrongRecoveryShape 555) = true := by decide +kernel

theorem strong_row_556 :
    (checkStrongRecoveryChemical 556 false && checkStrongRecoveryChemical 556 true &&
      checkStrongRecoveryShape 556) = true := by decide +kernel

theorem strong_row_557 :
    (checkStrongRecoveryChemical 557 false && checkStrongRecoveryChemical 557 true &&
      checkStrongRecoveryShape 557) = true := by decide +kernel

theorem strong_row_558 :
    (checkStrongRecoveryChemical 558 false && checkStrongRecoveryChemical 558 true &&
      checkStrongRecoveryShape 558) = true := by decide +kernel

theorem strong_row_559 :
    (checkStrongRecoveryChemical 559 false && checkStrongRecoveryChemical 559 true &&
      checkStrongRecoveryShape 559) = true := by decide +kernel

theorem strong_recovery_rows_544_559 :
    (List.range' 544 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_544, strong_row_545, strong_row_546, strong_row_547, strong_row_548, strong_row_549, strong_row_550, strong_row_551, strong_row_552, strong_row_553, strong_row_554, strong_row_555, strong_row_556, strong_row_557, strong_row_558, strong_row_559, Bool.and_self]

end P161Formal
