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

theorem strong_row_240 :
    (checkStrongRecoveryChemical 240 false && checkStrongRecoveryChemical 240 true &&
      checkStrongRecoveryShape 240) = true := by decide +kernel

theorem strong_row_241 :
    (checkStrongRecoveryChemical 241 false && checkStrongRecoveryChemical 241 true &&
      checkStrongRecoveryShape 241) = true := by decide +kernel

theorem strong_row_242 :
    (checkStrongRecoveryChemical 242 false && checkStrongRecoveryChemical 242 true &&
      checkStrongRecoveryShape 242) = true := by decide +kernel

theorem strong_row_243 :
    (checkStrongRecoveryChemical 243 false && checkStrongRecoveryChemical 243 true &&
      checkStrongRecoveryShape 243) = true := by decide +kernel

theorem strong_row_244 :
    (checkStrongRecoveryChemical 244 false && checkStrongRecoveryChemical 244 true &&
      checkStrongRecoveryShape 244) = true := by decide +kernel

theorem strong_row_245 :
    (checkStrongRecoveryChemical 245 false && checkStrongRecoveryChemical 245 true &&
      checkStrongRecoveryShape 245) = true := by decide +kernel

theorem strong_row_246 :
    (checkStrongRecoveryChemical 246 false && checkStrongRecoveryChemical 246 true &&
      checkStrongRecoveryShape 246) = true := by decide +kernel

theorem strong_row_247 :
    (checkStrongRecoveryChemical 247 false && checkStrongRecoveryChemical 247 true &&
      checkStrongRecoveryShape 247) = true := by decide +kernel

theorem strong_row_248 :
    (checkStrongRecoveryChemical 248 false && checkStrongRecoveryChemical 248 true &&
      checkStrongRecoveryShape 248) = true := by decide +kernel

theorem strong_row_249 :
    (checkStrongRecoveryChemical 249 false && checkStrongRecoveryChemical 249 true &&
      checkStrongRecoveryShape 249) = true := by decide +kernel

theorem strong_row_250 :
    (checkStrongRecoveryChemical 250 false && checkStrongRecoveryChemical 250 true &&
      checkStrongRecoveryShape 250) = true := by decide +kernel

theorem strong_row_251 :
    (checkStrongRecoveryChemical 251 false && checkStrongRecoveryChemical 251 true &&
      checkStrongRecoveryShape 251) = true := by decide +kernel

theorem strong_row_252 :
    (checkStrongRecoveryChemical 252 false && checkStrongRecoveryChemical 252 true &&
      checkStrongRecoveryShape 252) = true := by decide +kernel

theorem strong_row_253 :
    (checkStrongRecoveryChemical 253 false && checkStrongRecoveryChemical 253 true &&
      checkStrongRecoveryShape 253) = true := by decide +kernel

theorem strong_row_254 :
    (checkStrongRecoveryChemical 254 false && checkStrongRecoveryChemical 254 true &&
      checkStrongRecoveryShape 254) = true := by decide +kernel

theorem strong_row_255 :
    (checkStrongRecoveryChemical 255 false && checkStrongRecoveryChemical 255 true &&
      checkStrongRecoveryShape 255) = true := by decide +kernel

theorem strong_recovery_rows_240_255 :
    (List.range' 240 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_240, strong_row_241, strong_row_242, strong_row_243, strong_row_244, strong_row_245, strong_row_246, strong_row_247, strong_row_248, strong_row_249, strong_row_250, strong_row_251, strong_row_252, strong_row_253, strong_row_254, strong_row_255, Bool.and_self]

end P161Formal
