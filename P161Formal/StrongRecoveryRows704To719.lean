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

theorem strong_row_704 :
    (checkStrongRecoveryChemical 704 false && checkStrongRecoveryChemical 704 true &&
      checkStrongRecoveryShape 704) = true := by decide +kernel

theorem strong_row_705 :
    (checkStrongRecoveryChemical 705 false && checkStrongRecoveryChemical 705 true &&
      checkStrongRecoveryShape 705) = true := by decide +kernel

theorem strong_row_706 :
    (checkStrongRecoveryChemical 706 false && checkStrongRecoveryChemical 706 true &&
      checkStrongRecoveryShape 706) = true := by decide +kernel

theorem strong_row_707 :
    (checkStrongRecoveryChemical 707 false && checkStrongRecoveryChemical 707 true &&
      checkStrongRecoveryShape 707) = true := by decide +kernel

theorem strong_row_708 :
    (checkStrongRecoveryChemical 708 false && checkStrongRecoveryChemical 708 true &&
      checkStrongRecoveryShape 708) = true := by decide +kernel

theorem strong_row_709 :
    (checkStrongRecoveryChemical 709 false && checkStrongRecoveryChemical 709 true &&
      checkStrongRecoveryShape 709) = true := by decide +kernel

theorem strong_row_710 :
    (checkStrongRecoveryChemical 710 false && checkStrongRecoveryChemical 710 true &&
      checkStrongRecoveryShape 710) = true := by decide +kernel

theorem strong_row_711 :
    (checkStrongRecoveryChemical 711 false && checkStrongRecoveryChemical 711 true &&
      checkStrongRecoveryShape 711) = true := by decide +kernel

theorem strong_row_712 :
    (checkStrongRecoveryChemical 712 false && checkStrongRecoveryChemical 712 true &&
      checkStrongRecoveryShape 712) = true := by decide +kernel

theorem strong_row_713 :
    (checkStrongRecoveryChemical 713 false && checkStrongRecoveryChemical 713 true &&
      checkStrongRecoveryShape 713) = true := by decide +kernel

theorem strong_row_714 :
    (checkStrongRecoveryChemical 714 false && checkStrongRecoveryChemical 714 true &&
      checkStrongRecoveryShape 714) = true := by decide +kernel

theorem strong_row_715 :
    (checkStrongRecoveryChemical 715 false && checkStrongRecoveryChemical 715 true &&
      checkStrongRecoveryShape 715) = true := by decide +kernel

theorem strong_row_716 :
    (checkStrongRecoveryChemical 716 false && checkStrongRecoveryChemical 716 true &&
      checkStrongRecoveryShape 716) = true := by decide +kernel

theorem strong_row_717 :
    (checkStrongRecoveryChemical 717 false && checkStrongRecoveryChemical 717 true &&
      checkStrongRecoveryShape 717) = true := by decide +kernel

theorem strong_row_718 :
    (checkStrongRecoveryChemical 718 false && checkStrongRecoveryChemical 718 true &&
      checkStrongRecoveryShape 718) = true := by decide +kernel

theorem strong_row_719 :
    (checkStrongRecoveryChemical 719 false && checkStrongRecoveryChemical 719 true &&
      checkStrongRecoveryShape 719) = true := by decide +kernel

theorem strong_recovery_rows_704_719 :
    (List.range' 704 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_704, strong_row_705, strong_row_706, strong_row_707, strong_row_708, strong_row_709, strong_row_710, strong_row_711, strong_row_712, strong_row_713, strong_row_714, strong_row_715, strong_row_716, strong_row_717, strong_row_718, strong_row_719, Bool.and_self]

end P161Formal
