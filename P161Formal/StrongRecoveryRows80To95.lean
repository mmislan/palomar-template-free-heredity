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

theorem strong_row_80 :
    (checkStrongRecoveryChemical 80 false && checkStrongRecoveryChemical 80 true &&
      checkStrongRecoveryShape 80) = true := by decide +kernel

theorem strong_row_81 :
    (checkStrongRecoveryChemical 81 false && checkStrongRecoveryChemical 81 true &&
      checkStrongRecoveryShape 81) = true := by decide +kernel

theorem strong_row_82 :
    (checkStrongRecoveryChemical 82 false && checkStrongRecoveryChemical 82 true &&
      checkStrongRecoveryShape 82) = true := by decide +kernel

theorem strong_row_83 :
    (checkStrongRecoveryChemical 83 false && checkStrongRecoveryChemical 83 true &&
      checkStrongRecoveryShape 83) = true := by decide +kernel

theorem strong_row_84 :
    (checkStrongRecoveryChemical 84 false && checkStrongRecoveryChemical 84 true &&
      checkStrongRecoveryShape 84) = true := by decide +kernel

theorem strong_row_85 :
    (checkStrongRecoveryChemical 85 false && checkStrongRecoveryChemical 85 true &&
      checkStrongRecoveryShape 85) = true := by decide +kernel

theorem strong_row_86 :
    (checkStrongRecoveryChemical 86 false && checkStrongRecoveryChemical 86 true &&
      checkStrongRecoveryShape 86) = true := by decide +kernel

theorem strong_row_87 :
    (checkStrongRecoveryChemical 87 false && checkStrongRecoveryChemical 87 true &&
      checkStrongRecoveryShape 87) = true := by decide +kernel

theorem strong_row_88 :
    (checkStrongRecoveryChemical 88 false && checkStrongRecoveryChemical 88 true &&
      checkStrongRecoveryShape 88) = true := by decide +kernel

theorem strong_row_89 :
    (checkStrongRecoveryChemical 89 false && checkStrongRecoveryChemical 89 true &&
      checkStrongRecoveryShape 89) = true := by decide +kernel

theorem strong_row_90 :
    (checkStrongRecoveryChemical 90 false && checkStrongRecoveryChemical 90 true &&
      checkStrongRecoveryShape 90) = true := by decide +kernel

theorem strong_row_91 :
    (checkStrongRecoveryChemical 91 false && checkStrongRecoveryChemical 91 true &&
      checkStrongRecoveryShape 91) = true := by decide +kernel

theorem strong_row_92 :
    (checkStrongRecoveryChemical 92 false && checkStrongRecoveryChemical 92 true &&
      checkStrongRecoveryShape 92) = true := by decide +kernel

theorem strong_row_93 :
    (checkStrongRecoveryChemical 93 false && checkStrongRecoveryChemical 93 true &&
      checkStrongRecoveryShape 93) = true := by decide +kernel

theorem strong_row_94 :
    (checkStrongRecoveryChemical 94 false && checkStrongRecoveryChemical 94 true &&
      checkStrongRecoveryShape 94) = true := by decide +kernel

theorem strong_row_95 :
    (checkStrongRecoveryChemical 95 false && checkStrongRecoveryChemical 95 true &&
      checkStrongRecoveryShape 95) = true := by decide +kernel

theorem strong_recovery_rows_80_95 :
    (List.range' 80 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_80, strong_row_81, strong_row_82, strong_row_83, strong_row_84, strong_row_85, strong_row_86, strong_row_87, strong_row_88, strong_row_89, strong_row_90, strong_row_91, strong_row_92, strong_row_93, strong_row_94, strong_row_95, Bool.and_self]

end P161Formal
