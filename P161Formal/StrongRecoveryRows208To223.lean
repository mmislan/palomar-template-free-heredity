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

theorem strong_row_208 :
    (checkStrongRecoveryChemical 208 false && checkStrongRecoveryChemical 208 true &&
      checkStrongRecoveryShape 208) = true := by decide +kernel

theorem strong_row_209 :
    (checkStrongRecoveryChemical 209 false && checkStrongRecoveryChemical 209 true &&
      checkStrongRecoveryShape 209) = true := by decide +kernel

theorem strong_row_210 :
    (checkStrongRecoveryChemical 210 false && checkStrongRecoveryChemical 210 true &&
      checkStrongRecoveryShape 210) = true := by decide +kernel

theorem strong_row_211 :
    (checkStrongRecoveryChemical 211 false && checkStrongRecoveryChemical 211 true &&
      checkStrongRecoveryShape 211) = true := by decide +kernel

theorem strong_row_212 :
    (checkStrongRecoveryChemical 212 false && checkStrongRecoveryChemical 212 true &&
      checkStrongRecoveryShape 212) = true := by decide +kernel

theorem strong_row_213 :
    (checkStrongRecoveryChemical 213 false && checkStrongRecoveryChemical 213 true &&
      checkStrongRecoveryShape 213) = true := by decide +kernel

theorem strong_row_214 :
    (checkStrongRecoveryChemical 214 false && checkStrongRecoveryChemical 214 true &&
      checkStrongRecoveryShape 214) = true := by decide +kernel

theorem strong_row_215 :
    (checkStrongRecoveryChemical 215 false && checkStrongRecoveryChemical 215 true &&
      checkStrongRecoveryShape 215) = true := by decide +kernel

theorem strong_row_216 :
    (checkStrongRecoveryChemical 216 false && checkStrongRecoveryChemical 216 true &&
      checkStrongRecoveryShape 216) = true := by decide +kernel

theorem strong_row_217 :
    (checkStrongRecoveryChemical 217 false && checkStrongRecoveryChemical 217 true &&
      checkStrongRecoveryShape 217) = true := by decide +kernel

theorem strong_row_218 :
    (checkStrongRecoveryChemical 218 false && checkStrongRecoveryChemical 218 true &&
      checkStrongRecoveryShape 218) = true := by decide +kernel

theorem strong_row_219 :
    (checkStrongRecoveryChemical 219 false && checkStrongRecoveryChemical 219 true &&
      checkStrongRecoveryShape 219) = true := by decide +kernel

theorem strong_row_220 :
    (checkStrongRecoveryChemical 220 false && checkStrongRecoveryChemical 220 true &&
      checkStrongRecoveryShape 220) = true := by decide +kernel

theorem strong_row_221 :
    (checkStrongRecoveryChemical 221 false && checkStrongRecoveryChemical 221 true &&
      checkStrongRecoveryShape 221) = true := by decide +kernel

theorem strong_row_222 :
    (checkStrongRecoveryChemical 222 false && checkStrongRecoveryChemical 222 true &&
      checkStrongRecoveryShape 222) = true := by decide +kernel

theorem strong_row_223 :
    (checkStrongRecoveryChemical 223 false && checkStrongRecoveryChemical 223 true &&
      checkStrongRecoveryShape 223) = true := by decide +kernel

theorem strong_recovery_rows_208_223 :
    (List.range' 208 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_208, strong_row_209, strong_row_210, strong_row_211, strong_row_212, strong_row_213, strong_row_214, strong_row_215, strong_row_216, strong_row_217, strong_row_218, strong_row_219, strong_row_220, strong_row_221, strong_row_222, strong_row_223, Bool.and_self]

end P161Formal
