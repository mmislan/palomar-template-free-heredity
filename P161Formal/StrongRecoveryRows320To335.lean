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

theorem strong_row_320 :
    (checkStrongRecoveryChemical 320 false && checkStrongRecoveryChemical 320 true &&
      checkStrongRecoveryShape 320) = true := by decide +kernel

theorem strong_row_321 :
    (checkStrongRecoveryChemical 321 false && checkStrongRecoveryChemical 321 true &&
      checkStrongRecoveryShape 321) = true := by decide +kernel

theorem strong_row_322 :
    (checkStrongRecoveryChemical 322 false && checkStrongRecoveryChemical 322 true &&
      checkStrongRecoveryShape 322) = true := by decide +kernel

theorem strong_row_323 :
    (checkStrongRecoveryChemical 323 false && checkStrongRecoveryChemical 323 true &&
      checkStrongRecoveryShape 323) = true := by decide +kernel

theorem strong_row_324 :
    (checkStrongRecoveryChemical 324 false && checkStrongRecoveryChemical 324 true &&
      checkStrongRecoveryShape 324) = true := by decide +kernel

theorem strong_row_325 :
    (checkStrongRecoveryChemical 325 false && checkStrongRecoveryChemical 325 true &&
      checkStrongRecoveryShape 325) = true := by decide +kernel

theorem strong_row_326 :
    (checkStrongRecoveryChemical 326 false && checkStrongRecoveryChemical 326 true &&
      checkStrongRecoveryShape 326) = true := by decide +kernel

theorem strong_row_327 :
    (checkStrongRecoveryChemical 327 false && checkStrongRecoveryChemical 327 true &&
      checkStrongRecoveryShape 327) = true := by decide +kernel

theorem strong_row_328 :
    (checkStrongRecoveryChemical 328 false && checkStrongRecoveryChemical 328 true &&
      checkStrongRecoveryShape 328) = true := by decide +kernel

theorem strong_row_329 :
    (checkStrongRecoveryChemical 329 false && checkStrongRecoveryChemical 329 true &&
      checkStrongRecoveryShape 329) = true := by decide +kernel

theorem strong_row_330 :
    (checkStrongRecoveryChemical 330 false && checkStrongRecoveryChemical 330 true &&
      checkStrongRecoveryShape 330) = true := by decide +kernel

theorem strong_row_331 :
    (checkStrongRecoveryChemical 331 false && checkStrongRecoveryChemical 331 true &&
      checkStrongRecoveryShape 331) = true := by decide +kernel

theorem strong_row_332 :
    (checkStrongRecoveryChemical 332 false && checkStrongRecoveryChemical 332 true &&
      checkStrongRecoveryShape 332) = true := by decide +kernel

theorem strong_row_333 :
    (checkStrongRecoveryChemical 333 false && checkStrongRecoveryChemical 333 true &&
      checkStrongRecoveryShape 333) = true := by decide +kernel

theorem strong_row_334 :
    (checkStrongRecoveryChemical 334 false && checkStrongRecoveryChemical 334 true &&
      checkStrongRecoveryShape 334) = true := by decide +kernel

theorem strong_row_335 :
    (checkStrongRecoveryChemical 335 false && checkStrongRecoveryChemical 335 true &&
      checkStrongRecoveryShape 335) = true := by decide +kernel

theorem strong_recovery_rows_320_335 :
    (List.range' 320 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_320, strong_row_321, strong_row_322, strong_row_323, strong_row_324, strong_row_325, strong_row_326, strong_row_327, strong_row_328, strong_row_329, strong_row_330, strong_row_331, strong_row_332, strong_row_333, strong_row_334, strong_row_335, Bool.and_self]

end P161Formal
