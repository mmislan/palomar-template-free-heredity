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

theorem strong_row_64 :
    (checkStrongRecoveryChemical 64 false && checkStrongRecoveryChemical 64 true &&
      checkStrongRecoveryShape 64) = true := by decide +kernel

theorem strong_row_65 :
    (checkStrongRecoveryChemical 65 false && checkStrongRecoveryChemical 65 true &&
      checkStrongRecoveryShape 65) = true := by decide +kernel

theorem strong_row_66 :
    (checkStrongRecoveryChemical 66 false && checkStrongRecoveryChemical 66 true &&
      checkStrongRecoveryShape 66) = true := by decide +kernel

theorem strong_row_67 :
    (checkStrongRecoveryChemical 67 false && checkStrongRecoveryChemical 67 true &&
      checkStrongRecoveryShape 67) = true := by decide +kernel

theorem strong_row_68 :
    (checkStrongRecoveryChemical 68 false && checkStrongRecoveryChemical 68 true &&
      checkStrongRecoveryShape 68) = true := by decide +kernel

theorem strong_row_69 :
    (checkStrongRecoveryChemical 69 false && checkStrongRecoveryChemical 69 true &&
      checkStrongRecoveryShape 69) = true := by decide +kernel

theorem strong_row_70 :
    (checkStrongRecoveryChemical 70 false && checkStrongRecoveryChemical 70 true &&
      checkStrongRecoveryShape 70) = true := by decide +kernel

theorem strong_row_71 :
    (checkStrongRecoveryChemical 71 false && checkStrongRecoveryChemical 71 true &&
      checkStrongRecoveryShape 71) = true := by decide +kernel

theorem strong_row_72 :
    (checkStrongRecoveryChemical 72 false && checkStrongRecoveryChemical 72 true &&
      checkStrongRecoveryShape 72) = true := by decide +kernel

theorem strong_row_73 :
    (checkStrongRecoveryChemical 73 false && checkStrongRecoveryChemical 73 true &&
      checkStrongRecoveryShape 73) = true := by decide +kernel

theorem strong_row_74 :
    (checkStrongRecoveryChemical 74 false && checkStrongRecoveryChemical 74 true &&
      checkStrongRecoveryShape 74) = true := by decide +kernel

theorem strong_row_75 :
    (checkStrongRecoveryChemical 75 false && checkStrongRecoveryChemical 75 true &&
      checkStrongRecoveryShape 75) = true := by decide +kernel

theorem strong_row_76 :
    (checkStrongRecoveryChemical 76 false && checkStrongRecoveryChemical 76 true &&
      checkStrongRecoveryShape 76) = true := by decide +kernel

theorem strong_row_77 :
    (checkStrongRecoveryChemical 77 false && checkStrongRecoveryChemical 77 true &&
      checkStrongRecoveryShape 77) = true := by decide +kernel

theorem strong_row_78 :
    (checkStrongRecoveryChemical 78 false && checkStrongRecoveryChemical 78 true &&
      checkStrongRecoveryShape 78) = true := by decide +kernel

theorem strong_row_79 :
    (checkStrongRecoveryChemical 79 false && checkStrongRecoveryChemical 79 true &&
      checkStrongRecoveryShape 79) = true := by decide +kernel

theorem strong_recovery_rows_64_79 :
    (List.range' 64 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_64, strong_row_65, strong_row_66, strong_row_67, strong_row_68, strong_row_69, strong_row_70, strong_row_71, strong_row_72, strong_row_73, strong_row_74, strong_row_75, strong_row_76, strong_row_77, strong_row_78, strong_row_79, Bool.and_self]

end P161Formal
