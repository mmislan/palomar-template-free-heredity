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

theorem strong_row_112 :
    (checkStrongRecoveryChemical 112 false && checkStrongRecoveryChemical 112 true &&
      checkStrongRecoveryShape 112) = true := by decide +kernel

theorem strong_row_113 :
    (checkStrongRecoveryChemical 113 false && checkStrongRecoveryChemical 113 true &&
      checkStrongRecoveryShape 113) = true := by decide +kernel

theorem strong_row_114 :
    (checkStrongRecoveryChemical 114 false && checkStrongRecoveryChemical 114 true &&
      checkStrongRecoveryShape 114) = true := by decide +kernel

theorem strong_row_115 :
    (checkStrongRecoveryChemical 115 false && checkStrongRecoveryChemical 115 true &&
      checkStrongRecoveryShape 115) = true := by decide +kernel

theorem strong_row_116 :
    (checkStrongRecoveryChemical 116 false && checkStrongRecoveryChemical 116 true &&
      checkStrongRecoveryShape 116) = true := by decide +kernel

theorem strong_row_117 :
    (checkStrongRecoveryChemical 117 false && checkStrongRecoveryChemical 117 true &&
      checkStrongRecoveryShape 117) = true := by decide +kernel

theorem strong_row_118 :
    (checkStrongRecoveryChemical 118 false && checkStrongRecoveryChemical 118 true &&
      checkStrongRecoveryShape 118) = true := by decide +kernel

theorem strong_row_119 :
    (checkStrongRecoveryChemical 119 false && checkStrongRecoveryChemical 119 true &&
      checkStrongRecoveryShape 119) = true := by decide +kernel

theorem strong_row_120 :
    (checkStrongRecoveryChemical 120 false && checkStrongRecoveryChemical 120 true &&
      checkStrongRecoveryShape 120) = true := by decide +kernel

theorem strong_row_121 :
    (checkStrongRecoveryChemical 121 false && checkStrongRecoveryChemical 121 true &&
      checkStrongRecoveryShape 121) = true := by decide +kernel

theorem strong_row_122 :
    (checkStrongRecoveryChemical 122 false && checkStrongRecoveryChemical 122 true &&
      checkStrongRecoveryShape 122) = true := by decide +kernel

theorem strong_row_123 :
    (checkStrongRecoveryChemical 123 false && checkStrongRecoveryChemical 123 true &&
      checkStrongRecoveryShape 123) = true := by decide +kernel

theorem strong_row_124 :
    (checkStrongRecoveryChemical 124 false && checkStrongRecoveryChemical 124 true &&
      checkStrongRecoveryShape 124) = true := by decide +kernel

theorem strong_row_125 :
    (checkStrongRecoveryChemical 125 false && checkStrongRecoveryChemical 125 true &&
      checkStrongRecoveryShape 125) = true := by decide +kernel

theorem strong_row_126 :
    (checkStrongRecoveryChemical 126 false && checkStrongRecoveryChemical 126 true &&
      checkStrongRecoveryShape 126) = true := by decide +kernel

theorem strong_row_127 :
    (checkStrongRecoveryChemical 127 false && checkStrongRecoveryChemical 127 true &&
      checkStrongRecoveryShape 127) = true := by decide +kernel

theorem strong_recovery_rows_112_127 :
    (List.range' 112 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_112, strong_row_113, strong_row_114, strong_row_115, strong_row_116, strong_row_117, strong_row_118, strong_row_119, strong_row_120, strong_row_121, strong_row_122, strong_row_123, strong_row_124, strong_row_125, strong_row_126, strong_row_127, Bool.and_self]

end P161Formal
