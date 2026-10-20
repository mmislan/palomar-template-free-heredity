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

theorem strong_row_272 :
    (checkStrongRecoveryChemical 272 false && checkStrongRecoveryChemical 272 true &&
      checkStrongRecoveryShape 272) = true := by decide +kernel

theorem strong_row_273 :
    (checkStrongRecoveryChemical 273 false && checkStrongRecoveryChemical 273 true &&
      checkStrongRecoveryShape 273) = true := by decide +kernel

theorem strong_row_274 :
    (checkStrongRecoveryChemical 274 false && checkStrongRecoveryChemical 274 true &&
      checkStrongRecoveryShape 274) = true := by decide +kernel

theorem strong_row_275 :
    (checkStrongRecoveryChemical 275 false && checkStrongRecoveryChemical 275 true &&
      checkStrongRecoveryShape 275) = true := by decide +kernel

theorem strong_row_276 :
    (checkStrongRecoveryChemical 276 false && checkStrongRecoveryChemical 276 true &&
      checkStrongRecoveryShape 276) = true := by decide +kernel

theorem strong_row_277 :
    (checkStrongRecoveryChemical 277 false && checkStrongRecoveryChemical 277 true &&
      checkStrongRecoveryShape 277) = true := by decide +kernel

theorem strong_row_278 :
    (checkStrongRecoveryChemical 278 false && checkStrongRecoveryChemical 278 true &&
      checkStrongRecoveryShape 278) = true := by decide +kernel

theorem strong_row_279 :
    (checkStrongRecoveryChemical 279 false && checkStrongRecoveryChemical 279 true &&
      checkStrongRecoveryShape 279) = true := by decide +kernel

theorem strong_row_280 :
    (checkStrongRecoveryChemical 280 false && checkStrongRecoveryChemical 280 true &&
      checkStrongRecoveryShape 280) = true := by decide +kernel

theorem strong_row_281 :
    (checkStrongRecoveryChemical 281 false && checkStrongRecoveryChemical 281 true &&
      checkStrongRecoveryShape 281) = true := by decide +kernel

theorem strong_row_282 :
    (checkStrongRecoveryChemical 282 false && checkStrongRecoveryChemical 282 true &&
      checkStrongRecoveryShape 282) = true := by decide +kernel

theorem strong_row_283 :
    (checkStrongRecoveryChemical 283 false && checkStrongRecoveryChemical 283 true &&
      checkStrongRecoveryShape 283) = true := by decide +kernel

theorem strong_row_284 :
    (checkStrongRecoveryChemical 284 false && checkStrongRecoveryChemical 284 true &&
      checkStrongRecoveryShape 284) = true := by decide +kernel

theorem strong_row_285 :
    (checkStrongRecoveryChemical 285 false && checkStrongRecoveryChemical 285 true &&
      checkStrongRecoveryShape 285) = true := by decide +kernel

theorem strong_row_286 :
    (checkStrongRecoveryChemical 286 false && checkStrongRecoveryChemical 286 true &&
      checkStrongRecoveryShape 286) = true := by decide +kernel

theorem strong_row_287 :
    (checkStrongRecoveryChemical 287 false && checkStrongRecoveryChemical 287 true &&
      checkStrongRecoveryShape 287) = true := by decide +kernel

theorem strong_recovery_rows_272_287 :
    (List.range' 272 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_272, strong_row_273, strong_row_274, strong_row_275, strong_row_276, strong_row_277, strong_row_278, strong_row_279, strong_row_280, strong_row_281, strong_row_282, strong_row_283, strong_row_284, strong_row_285, strong_row_286, strong_row_287, Bool.and_self]

end P161Formal
