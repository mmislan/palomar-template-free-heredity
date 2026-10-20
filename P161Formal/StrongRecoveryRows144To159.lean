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

theorem strong_row_144 :
    (checkStrongRecoveryChemical 144 false && checkStrongRecoveryChemical 144 true &&
      checkStrongRecoveryShape 144) = true := by decide +kernel

theorem strong_row_145 :
    (checkStrongRecoveryChemical 145 false && checkStrongRecoveryChemical 145 true &&
      checkStrongRecoveryShape 145) = true := by decide +kernel

theorem strong_row_146 :
    (checkStrongRecoveryChemical 146 false && checkStrongRecoveryChemical 146 true &&
      checkStrongRecoveryShape 146) = true := by decide +kernel

theorem strong_row_147 :
    (checkStrongRecoveryChemical 147 false && checkStrongRecoveryChemical 147 true &&
      checkStrongRecoveryShape 147) = true := by decide +kernel

theorem strong_row_148 :
    (checkStrongRecoveryChemical 148 false && checkStrongRecoveryChemical 148 true &&
      checkStrongRecoveryShape 148) = true := by decide +kernel

theorem strong_row_149 :
    (checkStrongRecoveryChemical 149 false && checkStrongRecoveryChemical 149 true &&
      checkStrongRecoveryShape 149) = true := by decide +kernel

theorem strong_row_150 :
    (checkStrongRecoveryChemical 150 false && checkStrongRecoveryChemical 150 true &&
      checkStrongRecoveryShape 150) = true := by decide +kernel

theorem strong_row_151 :
    (checkStrongRecoveryChemical 151 false && checkStrongRecoveryChemical 151 true &&
      checkStrongRecoveryShape 151) = true := by decide +kernel

theorem strong_row_152 :
    (checkStrongRecoveryChemical 152 false && checkStrongRecoveryChemical 152 true &&
      checkStrongRecoveryShape 152) = true := by decide +kernel

theorem strong_row_153 :
    (checkStrongRecoveryChemical 153 false && checkStrongRecoveryChemical 153 true &&
      checkStrongRecoveryShape 153) = true := by decide +kernel

theorem strong_row_154 :
    (checkStrongRecoveryChemical 154 false && checkStrongRecoveryChemical 154 true &&
      checkStrongRecoveryShape 154) = true := by decide +kernel

theorem strong_row_155 :
    (checkStrongRecoveryChemical 155 false && checkStrongRecoveryChemical 155 true &&
      checkStrongRecoveryShape 155) = true := by decide +kernel

theorem strong_row_156 :
    (checkStrongRecoveryChemical 156 false && checkStrongRecoveryChemical 156 true &&
      checkStrongRecoveryShape 156) = true := by decide +kernel

theorem strong_row_157 :
    (checkStrongRecoveryChemical 157 false && checkStrongRecoveryChemical 157 true &&
      checkStrongRecoveryShape 157) = true := by decide +kernel

theorem strong_row_158 :
    (checkStrongRecoveryChemical 158 false && checkStrongRecoveryChemical 158 true &&
      checkStrongRecoveryShape 158) = true := by decide +kernel

theorem strong_row_159 :
    (checkStrongRecoveryChemical 159 false && checkStrongRecoveryChemical 159 true &&
      checkStrongRecoveryShape 159) = true := by decide +kernel

theorem strong_recovery_rows_144_159 :
    (List.range' 144 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_144, strong_row_145, strong_row_146, strong_row_147, strong_row_148, strong_row_149, strong_row_150, strong_row_151, strong_row_152, strong_row_153, strong_row_154, strong_row_155, strong_row_156, strong_row_157, strong_row_158, strong_row_159, Bool.and_self]

end P161Formal
