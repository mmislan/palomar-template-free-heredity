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

theorem strong_row_736 :
    (checkStrongRecoveryChemical 736 false && checkStrongRecoveryChemical 736 true &&
      checkStrongRecoveryShape 736) = true := by decide +kernel

theorem strong_row_737 :
    (checkStrongRecoveryChemical 737 false && checkStrongRecoveryChemical 737 true &&
      checkStrongRecoveryShape 737) = true := by decide +kernel

theorem strong_row_738 :
    (checkStrongRecoveryChemical 738 false && checkStrongRecoveryChemical 738 true &&
      checkStrongRecoveryShape 738) = true := by decide +kernel

theorem strong_row_739 :
    (checkStrongRecoveryChemical 739 false && checkStrongRecoveryChemical 739 true &&
      checkStrongRecoveryShape 739) = true := by decide +kernel

theorem strong_row_740 :
    (checkStrongRecoveryChemical 740 false && checkStrongRecoveryChemical 740 true &&
      checkStrongRecoveryShape 740) = true := by decide +kernel

theorem strong_row_741 :
    (checkStrongRecoveryChemical 741 false && checkStrongRecoveryChemical 741 true &&
      checkStrongRecoveryShape 741) = true := by decide +kernel

theorem strong_row_742 :
    (checkStrongRecoveryChemical 742 false && checkStrongRecoveryChemical 742 true &&
      checkStrongRecoveryShape 742) = true := by decide +kernel

theorem strong_row_743 :
    (checkStrongRecoveryChemical 743 false && checkStrongRecoveryChemical 743 true &&
      checkStrongRecoveryShape 743) = true := by decide +kernel

theorem strong_row_744 :
    (checkStrongRecoveryChemical 744 false && checkStrongRecoveryChemical 744 true &&
      checkStrongRecoveryShape 744) = true := by decide +kernel

theorem strong_row_745 :
    (checkStrongRecoveryChemical 745 false && checkStrongRecoveryChemical 745 true &&
      checkStrongRecoveryShape 745) = true := by decide +kernel

theorem strong_row_746 :
    (checkStrongRecoveryChemical 746 false && checkStrongRecoveryChemical 746 true &&
      checkStrongRecoveryShape 746) = true := by decide +kernel

theorem strong_row_747 :
    (checkStrongRecoveryChemical 747 false && checkStrongRecoveryChemical 747 true &&
      checkStrongRecoveryShape 747) = true := by decide +kernel

theorem strong_row_748 :
    (checkStrongRecoveryChemical 748 false && checkStrongRecoveryChemical 748 true &&
      checkStrongRecoveryShape 748) = true := by decide +kernel

theorem strong_row_749 :
    (checkStrongRecoveryChemical 749 false && checkStrongRecoveryChemical 749 true &&
      checkStrongRecoveryShape 749) = true := by decide +kernel

theorem strong_row_750 :
    (checkStrongRecoveryChemical 750 false && checkStrongRecoveryChemical 750 true &&
      checkStrongRecoveryShape 750) = true := by decide +kernel

theorem strong_row_751 :
    (checkStrongRecoveryChemical 751 false && checkStrongRecoveryChemical 751 true &&
      checkStrongRecoveryShape 751) = true := by decide +kernel

theorem strong_recovery_rows_736_751 :
    (List.range' 736 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_736, strong_row_737, strong_row_738, strong_row_739, strong_row_740, strong_row_741, strong_row_742, strong_row_743, strong_row_744, strong_row_745, strong_row_746, strong_row_747, strong_row_748, strong_row_749, strong_row_750, strong_row_751, Bool.and_self]

end P161Formal
