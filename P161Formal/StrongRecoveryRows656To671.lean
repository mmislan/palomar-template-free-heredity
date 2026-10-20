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

theorem strong_row_656 :
    (checkStrongRecoveryChemical 656 false && checkStrongRecoveryChemical 656 true &&
      checkStrongRecoveryShape 656) = true := by decide +kernel

theorem strong_row_657 :
    (checkStrongRecoveryChemical 657 false && checkStrongRecoveryChemical 657 true &&
      checkStrongRecoveryShape 657) = true := by decide +kernel

theorem strong_row_658 :
    (checkStrongRecoveryChemical 658 false && checkStrongRecoveryChemical 658 true &&
      checkStrongRecoveryShape 658) = true := by decide +kernel

theorem strong_row_659 :
    (checkStrongRecoveryChemical 659 false && checkStrongRecoveryChemical 659 true &&
      checkStrongRecoveryShape 659) = true := by decide +kernel

theorem strong_row_660 :
    (checkStrongRecoveryChemical 660 false && checkStrongRecoveryChemical 660 true &&
      checkStrongRecoveryShape 660) = true := by decide +kernel

theorem strong_row_661 :
    (checkStrongRecoveryChemical 661 false && checkStrongRecoveryChemical 661 true &&
      checkStrongRecoveryShape 661) = true := by decide +kernel

theorem strong_row_662 :
    (checkStrongRecoveryChemical 662 false && checkStrongRecoveryChemical 662 true &&
      checkStrongRecoveryShape 662) = true := by decide +kernel

theorem strong_row_663 :
    (checkStrongRecoveryChemical 663 false && checkStrongRecoveryChemical 663 true &&
      checkStrongRecoveryShape 663) = true := by decide +kernel

theorem strong_row_664 :
    (checkStrongRecoveryChemical 664 false && checkStrongRecoveryChemical 664 true &&
      checkStrongRecoveryShape 664) = true := by decide +kernel

theorem strong_row_665 :
    (checkStrongRecoveryChemical 665 false && checkStrongRecoveryChemical 665 true &&
      checkStrongRecoveryShape 665) = true := by decide +kernel

theorem strong_row_666 :
    (checkStrongRecoveryChemical 666 false && checkStrongRecoveryChemical 666 true &&
      checkStrongRecoveryShape 666) = true := by decide +kernel

theorem strong_row_667 :
    (checkStrongRecoveryChemical 667 false && checkStrongRecoveryChemical 667 true &&
      checkStrongRecoveryShape 667) = true := by decide +kernel

theorem strong_row_668 :
    (checkStrongRecoveryChemical 668 false && checkStrongRecoveryChemical 668 true &&
      checkStrongRecoveryShape 668) = true := by decide +kernel

theorem strong_row_669 :
    (checkStrongRecoveryChemical 669 false && checkStrongRecoveryChemical 669 true &&
      checkStrongRecoveryShape 669) = true := by decide +kernel

theorem strong_row_670 :
    (checkStrongRecoveryChemical 670 false && checkStrongRecoveryChemical 670 true &&
      checkStrongRecoveryShape 670) = true := by decide +kernel

theorem strong_row_671 :
    (checkStrongRecoveryChemical 671 false && checkStrongRecoveryChemical 671 true &&
      checkStrongRecoveryShape 671) = true := by decide +kernel

theorem strong_recovery_rows_656_671 :
    (List.range' 656 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_656, strong_row_657, strong_row_658, strong_row_659, strong_row_660, strong_row_661, strong_row_662, strong_row_663, strong_row_664, strong_row_665, strong_row_666, strong_row_667, strong_row_668, strong_row_669, strong_row_670, strong_row_671, Bool.and_self]

end P161Formal
