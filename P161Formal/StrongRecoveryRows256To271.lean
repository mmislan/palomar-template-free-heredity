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

theorem strong_row_256 :
    (checkStrongRecoveryChemical 256 false && checkStrongRecoveryChemical 256 true &&
      checkStrongRecoveryShape 256) = true := by decide +kernel

theorem strong_row_257 :
    (checkStrongRecoveryChemical 257 false && checkStrongRecoveryChemical 257 true &&
      checkStrongRecoveryShape 257) = true := by decide +kernel

theorem strong_row_258 :
    (checkStrongRecoveryChemical 258 false && checkStrongRecoveryChemical 258 true &&
      checkStrongRecoveryShape 258) = true := by decide +kernel

theorem strong_row_259 :
    (checkStrongRecoveryChemical 259 false && checkStrongRecoveryChemical 259 true &&
      checkStrongRecoveryShape 259) = true := by decide +kernel

theorem strong_row_260 :
    (checkStrongRecoveryChemical 260 false && checkStrongRecoveryChemical 260 true &&
      checkStrongRecoveryShape 260) = true := by decide +kernel

theorem strong_row_261 :
    (checkStrongRecoveryChemical 261 false && checkStrongRecoveryChemical 261 true &&
      checkStrongRecoveryShape 261) = true := by decide +kernel

theorem strong_row_262 :
    (checkStrongRecoveryChemical 262 false && checkStrongRecoveryChemical 262 true &&
      checkStrongRecoveryShape 262) = true := by decide +kernel

theorem strong_row_263 :
    (checkStrongRecoveryChemical 263 false && checkStrongRecoveryChemical 263 true &&
      checkStrongRecoveryShape 263) = true := by decide +kernel

theorem strong_row_264 :
    (checkStrongRecoveryChemical 264 false && checkStrongRecoveryChemical 264 true &&
      checkStrongRecoveryShape 264) = true := by decide +kernel

theorem strong_row_265 :
    (checkStrongRecoveryChemical 265 false && checkStrongRecoveryChemical 265 true &&
      checkStrongRecoveryShape 265) = true := by decide +kernel

theorem strong_row_266 :
    (checkStrongRecoveryChemical 266 false && checkStrongRecoveryChemical 266 true &&
      checkStrongRecoveryShape 266) = true := by decide +kernel

theorem strong_row_267 :
    (checkStrongRecoveryChemical 267 false && checkStrongRecoveryChemical 267 true &&
      checkStrongRecoveryShape 267) = true := by decide +kernel

theorem strong_row_268 :
    (checkStrongRecoveryChemical 268 false && checkStrongRecoveryChemical 268 true &&
      checkStrongRecoveryShape 268) = true := by decide +kernel

theorem strong_row_269 :
    (checkStrongRecoveryChemical 269 false && checkStrongRecoveryChemical 269 true &&
      checkStrongRecoveryShape 269) = true := by decide +kernel

theorem strong_row_270 :
    (checkStrongRecoveryChemical 270 false && checkStrongRecoveryChemical 270 true &&
      checkStrongRecoveryShape 270) = true := by decide +kernel

theorem strong_row_271 :
    (checkStrongRecoveryChemical 271 false && checkStrongRecoveryChemical 271 true &&
      checkStrongRecoveryShape 271) = true := by decide +kernel

theorem strong_recovery_rows_256_271 :
    (List.range' 256 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_256, strong_row_257, strong_row_258, strong_row_259, strong_row_260, strong_row_261, strong_row_262, strong_row_263, strong_row_264, strong_row_265, strong_row_266, strong_row_267, strong_row_268, strong_row_269, strong_row_270, strong_row_271, Bool.and_self]

end P161Formal
