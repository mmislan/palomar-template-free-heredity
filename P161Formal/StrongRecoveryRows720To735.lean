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

theorem strong_row_720 :
    (checkStrongRecoveryChemical 720 false && checkStrongRecoveryChemical 720 true &&
      checkStrongRecoveryShape 720) = true := by decide +kernel

theorem strong_row_721 :
    (checkStrongRecoveryChemical 721 false && checkStrongRecoveryChemical 721 true &&
      checkStrongRecoveryShape 721) = true := by decide +kernel

theorem strong_row_722 :
    (checkStrongRecoveryChemical 722 false && checkStrongRecoveryChemical 722 true &&
      checkStrongRecoveryShape 722) = true := by decide +kernel

theorem strong_row_723 :
    (checkStrongRecoveryChemical 723 false && checkStrongRecoveryChemical 723 true &&
      checkStrongRecoveryShape 723) = true := by decide +kernel

theorem strong_row_724 :
    (checkStrongRecoveryChemical 724 false && checkStrongRecoveryChemical 724 true &&
      checkStrongRecoveryShape 724) = true := by decide +kernel

theorem strong_row_725 :
    (checkStrongRecoveryChemical 725 false && checkStrongRecoveryChemical 725 true &&
      checkStrongRecoveryShape 725) = true := by decide +kernel

theorem strong_row_726 :
    (checkStrongRecoveryChemical 726 false && checkStrongRecoveryChemical 726 true &&
      checkStrongRecoveryShape 726) = true := by decide +kernel

theorem strong_row_727 :
    (checkStrongRecoveryChemical 727 false && checkStrongRecoveryChemical 727 true &&
      checkStrongRecoveryShape 727) = true := by decide +kernel

theorem strong_row_728 :
    (checkStrongRecoveryChemical 728 false && checkStrongRecoveryChemical 728 true &&
      checkStrongRecoveryShape 728) = true := by decide +kernel

theorem strong_row_729 :
    (checkStrongRecoveryChemical 729 false && checkStrongRecoveryChemical 729 true &&
      checkStrongRecoveryShape 729) = true := by decide +kernel

theorem strong_row_730 :
    (checkStrongRecoveryChemical 730 false && checkStrongRecoveryChemical 730 true &&
      checkStrongRecoveryShape 730) = true := by decide +kernel

theorem strong_row_731 :
    (checkStrongRecoveryChemical 731 false && checkStrongRecoveryChemical 731 true &&
      checkStrongRecoveryShape 731) = true := by decide +kernel

theorem strong_row_732 :
    (checkStrongRecoveryChemical 732 false && checkStrongRecoveryChemical 732 true &&
      checkStrongRecoveryShape 732) = true := by decide +kernel

theorem strong_row_733 :
    (checkStrongRecoveryChemical 733 false && checkStrongRecoveryChemical 733 true &&
      checkStrongRecoveryShape 733) = true := by decide +kernel

theorem strong_row_734 :
    (checkStrongRecoveryChemical 734 false && checkStrongRecoveryChemical 734 true &&
      checkStrongRecoveryShape 734) = true := by decide +kernel

theorem strong_row_735 :
    (checkStrongRecoveryChemical 735 false && checkStrongRecoveryChemical 735 true &&
      checkStrongRecoveryShape 735) = true := by decide +kernel

theorem strong_recovery_rows_720_735 :
    (List.range' 720 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_720, strong_row_721, strong_row_722, strong_row_723, strong_row_724, strong_row_725, strong_row_726, strong_row_727, strong_row_728, strong_row_729, strong_row_730, strong_row_731, strong_row_732, strong_row_733, strong_row_734, strong_row_735, Bool.and_self]

end P161Formal
