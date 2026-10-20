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

theorem strong_row_128 :
    (checkStrongRecoveryChemical 128 false && checkStrongRecoveryChemical 128 true &&
      checkStrongRecoveryShape 128) = true := by decide +kernel

theorem strong_row_129 :
    (checkStrongRecoveryChemical 129 false && checkStrongRecoveryChemical 129 true &&
      checkStrongRecoveryShape 129) = true := by decide +kernel

theorem strong_row_130 :
    (checkStrongRecoveryChemical 130 false && checkStrongRecoveryChemical 130 true &&
      checkStrongRecoveryShape 130) = true := by decide +kernel

theorem strong_row_131 :
    (checkStrongRecoveryChemical 131 false && checkStrongRecoveryChemical 131 true &&
      checkStrongRecoveryShape 131) = true := by decide +kernel

theorem strong_row_132 :
    (checkStrongRecoveryChemical 132 false && checkStrongRecoveryChemical 132 true &&
      checkStrongRecoveryShape 132) = true := by decide +kernel

theorem strong_row_133 :
    (checkStrongRecoveryChemical 133 false && checkStrongRecoveryChemical 133 true &&
      checkStrongRecoveryShape 133) = true := by decide +kernel

theorem strong_row_134 :
    (checkStrongRecoveryChemical 134 false && checkStrongRecoveryChemical 134 true &&
      checkStrongRecoveryShape 134) = true := by decide +kernel

theorem strong_row_135 :
    (checkStrongRecoveryChemical 135 false && checkStrongRecoveryChemical 135 true &&
      checkStrongRecoveryShape 135) = true := by decide +kernel

theorem strong_row_136 :
    (checkStrongRecoveryChemical 136 false && checkStrongRecoveryChemical 136 true &&
      checkStrongRecoveryShape 136) = true := by decide +kernel

theorem strong_row_137 :
    (checkStrongRecoveryChemical 137 false && checkStrongRecoveryChemical 137 true &&
      checkStrongRecoveryShape 137) = true := by decide +kernel

theorem strong_row_138 :
    (checkStrongRecoveryChemical 138 false && checkStrongRecoveryChemical 138 true &&
      checkStrongRecoveryShape 138) = true := by decide +kernel

theorem strong_row_139 :
    (checkStrongRecoveryChemical 139 false && checkStrongRecoveryChemical 139 true &&
      checkStrongRecoveryShape 139) = true := by decide +kernel

theorem strong_row_140 :
    (checkStrongRecoveryChemical 140 false && checkStrongRecoveryChemical 140 true &&
      checkStrongRecoveryShape 140) = true := by decide +kernel

theorem strong_row_141 :
    (checkStrongRecoveryChemical 141 false && checkStrongRecoveryChemical 141 true &&
      checkStrongRecoveryShape 141) = true := by decide +kernel

theorem strong_row_142 :
    (checkStrongRecoveryChemical 142 false && checkStrongRecoveryChemical 142 true &&
      checkStrongRecoveryShape 142) = true := by decide +kernel

theorem strong_row_143 :
    (checkStrongRecoveryChemical 143 false && checkStrongRecoveryChemical 143 true &&
      checkStrongRecoveryShape 143) = true := by decide +kernel

theorem strong_recovery_rows_128_143 :
    (List.range' 128 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_128, strong_row_129, strong_row_130, strong_row_131, strong_row_132, strong_row_133, strong_row_134, strong_row_135, strong_row_136, strong_row_137, strong_row_138, strong_row_139, strong_row_140, strong_row_141, strong_row_142, strong_row_143, Bool.and_self]

end P161Formal
