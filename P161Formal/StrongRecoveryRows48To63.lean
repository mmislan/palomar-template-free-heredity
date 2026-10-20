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

theorem strong_row_48 :
    (checkStrongRecoveryChemical 48 false && checkStrongRecoveryChemical 48 true &&
      checkStrongRecoveryShape 48) = true := by decide +kernel

theorem strong_row_49 :
    (checkStrongRecoveryChemical 49 false && checkStrongRecoveryChemical 49 true &&
      checkStrongRecoveryShape 49) = true := by decide +kernel

theorem strong_row_50 :
    (checkStrongRecoveryChemical 50 false && checkStrongRecoveryChemical 50 true &&
      checkStrongRecoveryShape 50) = true := by decide +kernel

theorem strong_row_51 :
    (checkStrongRecoveryChemical 51 false && checkStrongRecoveryChemical 51 true &&
      checkStrongRecoveryShape 51) = true := by decide +kernel

theorem strong_row_52 :
    (checkStrongRecoveryChemical 52 false && checkStrongRecoveryChemical 52 true &&
      checkStrongRecoveryShape 52) = true := by decide +kernel

theorem strong_row_53 :
    (checkStrongRecoveryChemical 53 false && checkStrongRecoveryChemical 53 true &&
      checkStrongRecoveryShape 53) = true := by decide +kernel

theorem strong_row_54 :
    (checkStrongRecoveryChemical 54 false && checkStrongRecoveryChemical 54 true &&
      checkStrongRecoveryShape 54) = true := by decide +kernel

theorem strong_row_55 :
    (checkStrongRecoveryChemical 55 false && checkStrongRecoveryChemical 55 true &&
      checkStrongRecoveryShape 55) = true := by decide +kernel

theorem strong_row_56 :
    (checkStrongRecoveryChemical 56 false && checkStrongRecoveryChemical 56 true &&
      checkStrongRecoveryShape 56) = true := by decide +kernel

theorem strong_row_57 :
    (checkStrongRecoveryChemical 57 false && checkStrongRecoveryChemical 57 true &&
      checkStrongRecoveryShape 57) = true := by decide +kernel

theorem strong_row_58 :
    (checkStrongRecoveryChemical 58 false && checkStrongRecoveryChemical 58 true &&
      checkStrongRecoveryShape 58) = true := by decide +kernel

theorem strong_row_59 :
    (checkStrongRecoveryChemical 59 false && checkStrongRecoveryChemical 59 true &&
      checkStrongRecoveryShape 59) = true := by decide +kernel

theorem strong_row_60 :
    (checkStrongRecoveryChemical 60 false && checkStrongRecoveryChemical 60 true &&
      checkStrongRecoveryShape 60) = true := by decide +kernel

theorem strong_row_61 :
    (checkStrongRecoveryChemical 61 false && checkStrongRecoveryChemical 61 true &&
      checkStrongRecoveryShape 61) = true := by decide +kernel

theorem strong_row_62 :
    (checkStrongRecoveryChemical 62 false && checkStrongRecoveryChemical 62 true &&
      checkStrongRecoveryShape 62) = true := by decide +kernel

theorem strong_row_63 :
    (checkStrongRecoveryChemical 63 false && checkStrongRecoveryChemical 63 true &&
      checkStrongRecoveryShape 63) = true := by decide +kernel

theorem strong_recovery_rows_48_63 :
    (List.range' 48 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_48, strong_row_49, strong_row_50, strong_row_51, strong_row_52, strong_row_53, strong_row_54, strong_row_55, strong_row_56, strong_row_57, strong_row_58, strong_row_59, strong_row_60, strong_row_61, strong_row_62, strong_row_63, Bool.and_self]

end P161Formal
