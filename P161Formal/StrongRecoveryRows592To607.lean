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

theorem strong_row_592 :
    (checkStrongRecoveryChemical 592 false && checkStrongRecoveryChemical 592 true &&
      checkStrongRecoveryShape 592) = true := by decide +kernel

theorem strong_row_593 :
    (checkStrongRecoveryChemical 593 false && checkStrongRecoveryChemical 593 true &&
      checkStrongRecoveryShape 593) = true := by decide +kernel

theorem strong_row_594 :
    (checkStrongRecoveryChemical 594 false && checkStrongRecoveryChemical 594 true &&
      checkStrongRecoveryShape 594) = true := by decide +kernel

theorem strong_row_595 :
    (checkStrongRecoveryChemical 595 false && checkStrongRecoveryChemical 595 true &&
      checkStrongRecoveryShape 595) = true := by decide +kernel

theorem strong_row_596 :
    (checkStrongRecoveryChemical 596 false && checkStrongRecoveryChemical 596 true &&
      checkStrongRecoveryShape 596) = true := by decide +kernel

theorem strong_row_597 :
    (checkStrongRecoveryChemical 597 false && checkStrongRecoveryChemical 597 true &&
      checkStrongRecoveryShape 597) = true := by decide +kernel

theorem strong_row_598 :
    (checkStrongRecoveryChemical 598 false && checkStrongRecoveryChemical 598 true &&
      checkStrongRecoveryShape 598) = true := by decide +kernel

theorem strong_row_599 :
    (checkStrongRecoveryChemical 599 false && checkStrongRecoveryChemical 599 true &&
      checkStrongRecoveryShape 599) = true := by decide +kernel

theorem strong_row_600 :
    (checkStrongRecoveryChemical 600 false && checkStrongRecoveryChemical 600 true &&
      checkStrongRecoveryShape 600) = true := by decide +kernel

theorem strong_row_601 :
    (checkStrongRecoveryChemical 601 false && checkStrongRecoveryChemical 601 true &&
      checkStrongRecoveryShape 601) = true := by decide +kernel

theorem strong_row_602 :
    (checkStrongRecoveryChemical 602 false && checkStrongRecoveryChemical 602 true &&
      checkStrongRecoveryShape 602) = true := by decide +kernel

theorem strong_row_603 :
    (checkStrongRecoveryChemical 603 false && checkStrongRecoveryChemical 603 true &&
      checkStrongRecoveryShape 603) = true := by decide +kernel

theorem strong_row_604 :
    (checkStrongRecoveryChemical 604 false && checkStrongRecoveryChemical 604 true &&
      checkStrongRecoveryShape 604) = true := by decide +kernel

theorem strong_row_605 :
    (checkStrongRecoveryChemical 605 false && checkStrongRecoveryChemical 605 true &&
      checkStrongRecoveryShape 605) = true := by decide +kernel

theorem strong_row_606 :
    (checkStrongRecoveryChemical 606 false && checkStrongRecoveryChemical 606 true &&
      checkStrongRecoveryShape 606) = true := by decide +kernel

theorem strong_row_607 :
    (checkStrongRecoveryChemical 607 false && checkStrongRecoveryChemical 607 true &&
      checkStrongRecoveryShape 607) = true := by decide +kernel

theorem strong_recovery_rows_592_607 :
    (List.range' 592 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_592, strong_row_593, strong_row_594, strong_row_595, strong_row_596, strong_row_597, strong_row_598, strong_row_599, strong_row_600, strong_row_601, strong_row_602, strong_row_603, strong_row_604, strong_row_605, strong_row_606, strong_row_607, Bool.and_self]

end P161Formal
