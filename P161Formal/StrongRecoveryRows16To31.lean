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

theorem strong_row_16 :
    (checkStrongRecoveryChemical 16 false && checkStrongRecoveryChemical 16 true &&
      checkStrongRecoveryShape 16) = true := by decide +kernel

theorem strong_row_17 :
    (checkStrongRecoveryChemical 17 false && checkStrongRecoveryChemical 17 true &&
      checkStrongRecoveryShape 17) = true := by decide +kernel

theorem strong_row_18 :
    (checkStrongRecoveryChemical 18 false && checkStrongRecoveryChemical 18 true &&
      checkStrongRecoveryShape 18) = true := by decide +kernel

theorem strong_row_19 :
    (checkStrongRecoveryChemical 19 false && checkStrongRecoveryChemical 19 true &&
      checkStrongRecoveryShape 19) = true := by decide +kernel

theorem strong_row_20 :
    (checkStrongRecoveryChemical 20 false && checkStrongRecoveryChemical 20 true &&
      checkStrongRecoveryShape 20) = true := by decide +kernel

theorem strong_row_21 :
    (checkStrongRecoveryChemical 21 false && checkStrongRecoveryChemical 21 true &&
      checkStrongRecoveryShape 21) = true := by decide +kernel

theorem strong_row_22 :
    (checkStrongRecoveryChemical 22 false && checkStrongRecoveryChemical 22 true &&
      checkStrongRecoveryShape 22) = true := by decide +kernel

theorem strong_row_23 :
    (checkStrongRecoveryChemical 23 false && checkStrongRecoveryChemical 23 true &&
      checkStrongRecoveryShape 23) = true := by decide +kernel

theorem strong_row_24 :
    (checkStrongRecoveryChemical 24 false && checkStrongRecoveryChemical 24 true &&
      checkStrongRecoveryShape 24) = true := by decide +kernel

theorem strong_row_25 :
    (checkStrongRecoveryChemical 25 false && checkStrongRecoveryChemical 25 true &&
      checkStrongRecoveryShape 25) = true := by decide +kernel

theorem strong_row_26 :
    (checkStrongRecoveryChemical 26 false && checkStrongRecoveryChemical 26 true &&
      checkStrongRecoveryShape 26) = true := by decide +kernel

theorem strong_row_27 :
    (checkStrongRecoveryChemical 27 false && checkStrongRecoveryChemical 27 true &&
      checkStrongRecoveryShape 27) = true := by decide +kernel

theorem strong_row_28 :
    (checkStrongRecoveryChemical 28 false && checkStrongRecoveryChemical 28 true &&
      checkStrongRecoveryShape 28) = true := by decide +kernel

theorem strong_row_29 :
    (checkStrongRecoveryChemical 29 false && checkStrongRecoveryChemical 29 true &&
      checkStrongRecoveryShape 29) = true := by decide +kernel

theorem strong_row_30 :
    (checkStrongRecoveryChemical 30 false && checkStrongRecoveryChemical 30 true &&
      checkStrongRecoveryShape 30) = true := by decide +kernel

theorem strong_row_31 :
    (checkStrongRecoveryChemical 31 false && checkStrongRecoveryChemical 31 true &&
      checkStrongRecoveryShape 31) = true := by decide +kernel

theorem strong_recovery_rows_16_31 :
    (List.range' 16 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_16, strong_row_17, strong_row_18, strong_row_19, strong_row_20, strong_row_21, strong_row_22, strong_row_23, strong_row_24, strong_row_25, strong_row_26, strong_row_27, strong_row_28, strong_row_29, strong_row_30, strong_row_31, Bool.and_self]

end P161Formal
