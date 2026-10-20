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

theorem strong_row_224 :
    (checkStrongRecoveryChemical 224 false && checkStrongRecoveryChemical 224 true &&
      checkStrongRecoveryShape 224) = true := by decide +kernel

theorem strong_row_225 :
    (checkStrongRecoveryChemical 225 false && checkStrongRecoveryChemical 225 true &&
      checkStrongRecoveryShape 225) = true := by decide +kernel

theorem strong_row_226 :
    (checkStrongRecoveryChemical 226 false && checkStrongRecoveryChemical 226 true &&
      checkStrongRecoveryShape 226) = true := by decide +kernel

theorem strong_row_227 :
    (checkStrongRecoveryChemical 227 false && checkStrongRecoveryChemical 227 true &&
      checkStrongRecoveryShape 227) = true := by decide +kernel

theorem strong_row_228 :
    (checkStrongRecoveryChemical 228 false && checkStrongRecoveryChemical 228 true &&
      checkStrongRecoveryShape 228) = true := by decide +kernel

theorem strong_row_229 :
    (checkStrongRecoveryChemical 229 false && checkStrongRecoveryChemical 229 true &&
      checkStrongRecoveryShape 229) = true := by decide +kernel

theorem strong_row_230 :
    (checkStrongRecoveryChemical 230 false && checkStrongRecoveryChemical 230 true &&
      checkStrongRecoveryShape 230) = true := by decide +kernel

theorem strong_row_231 :
    (checkStrongRecoveryChemical 231 false && checkStrongRecoveryChemical 231 true &&
      checkStrongRecoveryShape 231) = true := by decide +kernel

theorem strong_row_232 :
    (checkStrongRecoveryChemical 232 false && checkStrongRecoveryChemical 232 true &&
      checkStrongRecoveryShape 232) = true := by decide +kernel

theorem strong_row_233 :
    (checkStrongRecoveryChemical 233 false && checkStrongRecoveryChemical 233 true &&
      checkStrongRecoveryShape 233) = true := by decide +kernel

theorem strong_row_234 :
    (checkStrongRecoveryChemical 234 false && checkStrongRecoveryChemical 234 true &&
      checkStrongRecoveryShape 234) = true := by decide +kernel

theorem strong_row_235 :
    (checkStrongRecoveryChemical 235 false && checkStrongRecoveryChemical 235 true &&
      checkStrongRecoveryShape 235) = true := by decide +kernel

theorem strong_row_236 :
    (checkStrongRecoveryChemical 236 false && checkStrongRecoveryChemical 236 true &&
      checkStrongRecoveryShape 236) = true := by decide +kernel

theorem strong_row_237 :
    (checkStrongRecoveryChemical 237 false && checkStrongRecoveryChemical 237 true &&
      checkStrongRecoveryShape 237) = true := by decide +kernel

theorem strong_row_238 :
    (checkStrongRecoveryChemical 238 false && checkStrongRecoveryChemical 238 true &&
      checkStrongRecoveryShape 238) = true := by decide +kernel

theorem strong_row_239 :
    (checkStrongRecoveryChemical 239 false && checkStrongRecoveryChemical 239 true &&
      checkStrongRecoveryShape 239) = true := by decide +kernel

theorem strong_recovery_rows_224_239 :
    (List.range' 224 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_224, strong_row_225, strong_row_226, strong_row_227, strong_row_228, strong_row_229, strong_row_230, strong_row_231, strong_row_232, strong_row_233, strong_row_234, strong_row_235, strong_row_236, strong_row_237, strong_row_238, strong_row_239, Bool.and_self]

end P161Formal
