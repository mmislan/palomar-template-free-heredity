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

theorem strong_row_160 :
    (checkStrongRecoveryChemical 160 false && checkStrongRecoveryChemical 160 true &&
      checkStrongRecoveryShape 160) = true := by decide +kernel

theorem strong_row_161 :
    (checkStrongRecoveryChemical 161 false && checkStrongRecoveryChemical 161 true &&
      checkStrongRecoveryShape 161) = true := by decide +kernel

theorem strong_row_162 :
    (checkStrongRecoveryChemical 162 false && checkStrongRecoveryChemical 162 true &&
      checkStrongRecoveryShape 162) = true := by decide +kernel

theorem strong_row_163 :
    (checkStrongRecoveryChemical 163 false && checkStrongRecoveryChemical 163 true &&
      checkStrongRecoveryShape 163) = true := by decide +kernel

theorem strong_row_164 :
    (checkStrongRecoveryChemical 164 false && checkStrongRecoveryChemical 164 true &&
      checkStrongRecoveryShape 164) = true := by decide +kernel

theorem strong_row_165 :
    (checkStrongRecoveryChemical 165 false && checkStrongRecoveryChemical 165 true &&
      checkStrongRecoveryShape 165) = true := by decide +kernel

theorem strong_row_166 :
    (checkStrongRecoveryChemical 166 false && checkStrongRecoveryChemical 166 true &&
      checkStrongRecoveryShape 166) = true := by decide +kernel

theorem strong_row_167 :
    (checkStrongRecoveryChemical 167 false && checkStrongRecoveryChemical 167 true &&
      checkStrongRecoveryShape 167) = true := by decide +kernel

theorem strong_row_168 :
    (checkStrongRecoveryChemical 168 false && checkStrongRecoveryChemical 168 true &&
      checkStrongRecoveryShape 168) = true := by decide +kernel

theorem strong_row_169 :
    (checkStrongRecoveryChemical 169 false && checkStrongRecoveryChemical 169 true &&
      checkStrongRecoveryShape 169) = true := by decide +kernel

theorem strong_row_170 :
    (checkStrongRecoveryChemical 170 false && checkStrongRecoveryChemical 170 true &&
      checkStrongRecoveryShape 170) = true := by decide +kernel

theorem strong_row_171 :
    (checkStrongRecoveryChemical 171 false && checkStrongRecoveryChemical 171 true &&
      checkStrongRecoveryShape 171) = true := by decide +kernel

theorem strong_row_172 :
    (checkStrongRecoveryChemical 172 false && checkStrongRecoveryChemical 172 true &&
      checkStrongRecoveryShape 172) = true := by decide +kernel

theorem strong_row_173 :
    (checkStrongRecoveryChemical 173 false && checkStrongRecoveryChemical 173 true &&
      checkStrongRecoveryShape 173) = true := by decide +kernel

theorem strong_row_174 :
    (checkStrongRecoveryChemical 174 false && checkStrongRecoveryChemical 174 true &&
      checkStrongRecoveryShape 174) = true := by decide +kernel

theorem strong_row_175 :
    (checkStrongRecoveryChemical 175 false && checkStrongRecoveryChemical 175 true &&
      checkStrongRecoveryShape 175) = true := by decide +kernel

theorem strong_recovery_rows_160_175 :
    (List.range' 160 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_160, strong_row_161, strong_row_162, strong_row_163, strong_row_164, strong_row_165, strong_row_166, strong_row_167, strong_row_168, strong_row_169, strong_row_170, strong_row_171, strong_row_172, strong_row_173, strong_row_174, strong_row_175, Bool.and_self]

end P161Formal
