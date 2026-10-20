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

theorem strong_row_688 :
    (checkStrongRecoveryChemical 688 false && checkStrongRecoveryChemical 688 true &&
      checkStrongRecoveryShape 688) = true := by decide +kernel

theorem strong_row_689 :
    (checkStrongRecoveryChemical 689 false && checkStrongRecoveryChemical 689 true &&
      checkStrongRecoveryShape 689) = true := by decide +kernel

theorem strong_row_690 :
    (checkStrongRecoveryChemical 690 false && checkStrongRecoveryChemical 690 true &&
      checkStrongRecoveryShape 690) = true := by decide +kernel

theorem strong_row_691 :
    (checkStrongRecoveryChemical 691 false && checkStrongRecoveryChemical 691 true &&
      checkStrongRecoveryShape 691) = true := by decide +kernel

theorem strong_row_692 :
    (checkStrongRecoveryChemical 692 false && checkStrongRecoveryChemical 692 true &&
      checkStrongRecoveryShape 692) = true := by decide +kernel

theorem strong_row_693 :
    (checkStrongRecoveryChemical 693 false && checkStrongRecoveryChemical 693 true &&
      checkStrongRecoveryShape 693) = true := by decide +kernel

theorem strong_row_694 :
    (checkStrongRecoveryChemical 694 false && checkStrongRecoveryChemical 694 true &&
      checkStrongRecoveryShape 694) = true := by decide +kernel

theorem strong_row_695 :
    (checkStrongRecoveryChemical 695 false && checkStrongRecoveryChemical 695 true &&
      checkStrongRecoveryShape 695) = true := by decide +kernel

theorem strong_row_696 :
    (checkStrongRecoveryChemical 696 false && checkStrongRecoveryChemical 696 true &&
      checkStrongRecoveryShape 696) = true := by decide +kernel

theorem strong_row_697 :
    (checkStrongRecoveryChemical 697 false && checkStrongRecoveryChemical 697 true &&
      checkStrongRecoveryShape 697) = true := by decide +kernel

theorem strong_row_698 :
    (checkStrongRecoveryChemical 698 false && checkStrongRecoveryChemical 698 true &&
      checkStrongRecoveryShape 698) = true := by decide +kernel

theorem strong_row_699 :
    (checkStrongRecoveryChemical 699 false && checkStrongRecoveryChemical 699 true &&
      checkStrongRecoveryShape 699) = true := by decide +kernel

theorem strong_row_700 :
    (checkStrongRecoveryChemical 700 false && checkStrongRecoveryChemical 700 true &&
      checkStrongRecoveryShape 700) = true := by decide +kernel

theorem strong_row_701 :
    (checkStrongRecoveryChemical 701 false && checkStrongRecoveryChemical 701 true &&
      checkStrongRecoveryShape 701) = true := by decide +kernel

theorem strong_row_702 :
    (checkStrongRecoveryChemical 702 false && checkStrongRecoveryChemical 702 true &&
      checkStrongRecoveryShape 702) = true := by decide +kernel

theorem strong_row_703 :
    (checkStrongRecoveryChemical 703 false && checkStrongRecoveryChemical 703 true &&
      checkStrongRecoveryShape 703) = true := by decide +kernel

theorem strong_recovery_rows_688_703 :
    (List.range' 688 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_688, strong_row_689, strong_row_690, strong_row_691, strong_row_692, strong_row_693, strong_row_694, strong_row_695, strong_row_696, strong_row_697, strong_row_698, strong_row_699, strong_row_700, strong_row_701, strong_row_702, strong_row_703, Bool.and_self]

end P161Formal
