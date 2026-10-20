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

theorem strong_row_32 :
    (checkStrongRecoveryChemical 32 false && checkStrongRecoveryChemical 32 true &&
      checkStrongRecoveryShape 32) = true := by decide +kernel

theorem strong_row_33 :
    (checkStrongRecoveryChemical 33 false && checkStrongRecoveryChemical 33 true &&
      checkStrongRecoveryShape 33) = true := by decide +kernel

theorem strong_row_34 :
    (checkStrongRecoveryChemical 34 false && checkStrongRecoveryChemical 34 true &&
      checkStrongRecoveryShape 34) = true := by decide +kernel

theorem strong_row_35 :
    (checkStrongRecoveryChemical 35 false && checkStrongRecoveryChemical 35 true &&
      checkStrongRecoveryShape 35) = true := by decide +kernel

theorem strong_row_36 :
    (checkStrongRecoveryChemical 36 false && checkStrongRecoveryChemical 36 true &&
      checkStrongRecoveryShape 36) = true := by decide +kernel

theorem strong_row_37 :
    (checkStrongRecoveryChemical 37 false && checkStrongRecoveryChemical 37 true &&
      checkStrongRecoveryShape 37) = true := by decide +kernel

theorem strong_row_38 :
    (checkStrongRecoveryChemical 38 false && checkStrongRecoveryChemical 38 true &&
      checkStrongRecoveryShape 38) = true := by decide +kernel

theorem strong_row_39 :
    (checkStrongRecoveryChemical 39 false && checkStrongRecoveryChemical 39 true &&
      checkStrongRecoveryShape 39) = true := by decide +kernel

theorem strong_row_40 :
    (checkStrongRecoveryChemical 40 false && checkStrongRecoveryChemical 40 true &&
      checkStrongRecoveryShape 40) = true := by decide +kernel

theorem strong_row_41 :
    (checkStrongRecoveryChemical 41 false && checkStrongRecoveryChemical 41 true &&
      checkStrongRecoveryShape 41) = true := by decide +kernel

theorem strong_row_42 :
    (checkStrongRecoveryChemical 42 false && checkStrongRecoveryChemical 42 true &&
      checkStrongRecoveryShape 42) = true := by decide +kernel

theorem strong_row_43 :
    (checkStrongRecoveryChemical 43 false && checkStrongRecoveryChemical 43 true &&
      checkStrongRecoveryShape 43) = true := by decide +kernel

theorem strong_row_44 :
    (checkStrongRecoveryChemical 44 false && checkStrongRecoveryChemical 44 true &&
      checkStrongRecoveryShape 44) = true := by decide +kernel

theorem strong_row_45 :
    (checkStrongRecoveryChemical 45 false && checkStrongRecoveryChemical 45 true &&
      checkStrongRecoveryShape 45) = true := by decide +kernel

theorem strong_row_46 :
    (checkStrongRecoveryChemical 46 false && checkStrongRecoveryChemical 46 true &&
      checkStrongRecoveryShape 46) = true := by decide +kernel

theorem strong_row_47 :
    (checkStrongRecoveryChemical 47 false && checkStrongRecoveryChemical 47 true &&
      checkStrongRecoveryShape 47) = true := by decide +kernel

theorem strong_recovery_rows_32_47 :
    (List.range' 32 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_32, strong_row_33, strong_row_34, strong_row_35, strong_row_36, strong_row_37, strong_row_38, strong_row_39, strong_row_40, strong_row_41, strong_row_42, strong_row_43, strong_row_44, strong_row_45, strong_row_46, strong_row_47, Bool.and_self]

end P161Formal
