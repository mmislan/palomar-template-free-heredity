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

theorem strong_row_752 :
    (checkStrongRecoveryChemical 752 false && checkStrongRecoveryChemical 752 true &&
      checkStrongRecoveryShape 752) = true := by decide +kernel

theorem strong_row_753 :
    (checkStrongRecoveryChemical 753 false && checkStrongRecoveryChemical 753 true &&
      checkStrongRecoveryShape 753) = true := by decide +kernel

theorem strong_row_754 :
    (checkStrongRecoveryChemical 754 false && checkStrongRecoveryChemical 754 true &&
      checkStrongRecoveryShape 754) = true := by decide +kernel

theorem strong_row_755 :
    (checkStrongRecoveryChemical 755 false && checkStrongRecoveryChemical 755 true &&
      checkStrongRecoveryShape 755) = true := by decide +kernel

theorem strong_row_756 :
    (checkStrongRecoveryChemical 756 false && checkStrongRecoveryChemical 756 true &&
      checkStrongRecoveryShape 756) = true := by decide +kernel

theorem strong_row_757 :
    (checkStrongRecoveryChemical 757 false && checkStrongRecoveryChemical 757 true &&
      checkStrongRecoveryShape 757) = true := by decide +kernel

theorem strong_row_758 :
    (checkStrongRecoveryChemical 758 false && checkStrongRecoveryChemical 758 true &&
      checkStrongRecoveryShape 758) = true := by decide +kernel

theorem strong_row_759 :
    (checkStrongRecoveryChemical 759 false && checkStrongRecoveryChemical 759 true &&
      checkStrongRecoveryShape 759) = true := by decide +kernel

theorem strong_row_760 :
    (checkStrongRecoveryChemical 760 false && checkStrongRecoveryChemical 760 true &&
      checkStrongRecoveryShape 760) = true := by decide +kernel

theorem strong_row_761 :
    (checkStrongRecoveryChemical 761 false && checkStrongRecoveryChemical 761 true &&
      checkStrongRecoveryShape 761) = true := by decide +kernel

theorem strong_row_762 :
    (checkStrongRecoveryChemical 762 false && checkStrongRecoveryChemical 762 true &&
      checkStrongRecoveryShape 762) = true := by decide +kernel

theorem strong_row_763 :
    (checkStrongRecoveryChemical 763 false && checkStrongRecoveryChemical 763 true &&
      checkStrongRecoveryShape 763) = true := by decide +kernel

theorem strong_row_764 :
    (checkStrongRecoveryChemical 764 false && checkStrongRecoveryChemical 764 true &&
      checkStrongRecoveryShape 764) = true := by decide +kernel

theorem strong_row_765 :
    (checkStrongRecoveryChemical 765 false && checkStrongRecoveryChemical 765 true &&
      checkStrongRecoveryShape 765) = true := by decide +kernel

theorem strong_row_766 :
    (checkStrongRecoveryChemical 766 false && checkStrongRecoveryChemical 766 true &&
      checkStrongRecoveryShape 766) = true := by decide +kernel

theorem strong_row_767 :
    (checkStrongRecoveryChemical 767 false && checkStrongRecoveryChemical 767 true &&
      checkStrongRecoveryShape 767) = true := by decide +kernel

theorem strong_recovery_rows_752_767 :
    (List.range' 752 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_752, strong_row_753, strong_row_754, strong_row_755, strong_row_756, strong_row_757, strong_row_758, strong_row_759, strong_row_760, strong_row_761, strong_row_762, strong_row_763, strong_row_764, strong_row_765, strong_row_766, strong_row_767, Bool.and_self]

end P161Formal
