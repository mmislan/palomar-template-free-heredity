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

theorem strong_row_368 :
    (checkStrongRecoveryChemical 368 false && checkStrongRecoveryChemical 368 true &&
      checkStrongRecoveryShape 368) = true := by decide +kernel

theorem strong_row_369 :
    (checkStrongRecoveryChemical 369 false && checkStrongRecoveryChemical 369 true &&
      checkStrongRecoveryShape 369) = true := by decide +kernel

theorem strong_row_370 :
    (checkStrongRecoveryChemical 370 false && checkStrongRecoveryChemical 370 true &&
      checkStrongRecoveryShape 370) = true := by decide +kernel

theorem strong_row_371 :
    (checkStrongRecoveryChemical 371 false && checkStrongRecoveryChemical 371 true &&
      checkStrongRecoveryShape 371) = true := by decide +kernel

theorem strong_row_372 :
    (checkStrongRecoveryChemical 372 false && checkStrongRecoveryChemical 372 true &&
      checkStrongRecoveryShape 372) = true := by decide +kernel

theorem strong_row_373 :
    (checkStrongRecoveryChemical 373 false && checkStrongRecoveryChemical 373 true &&
      checkStrongRecoveryShape 373) = true := by decide +kernel

theorem strong_row_374 :
    (checkStrongRecoveryChemical 374 false && checkStrongRecoveryChemical 374 true &&
      checkStrongRecoveryShape 374) = true := by decide +kernel

theorem strong_row_375 :
    (checkStrongRecoveryChemical 375 false && checkStrongRecoveryChemical 375 true &&
      checkStrongRecoveryShape 375) = true := by decide +kernel

theorem strong_row_376 :
    (checkStrongRecoveryChemical 376 false && checkStrongRecoveryChemical 376 true &&
      checkStrongRecoveryShape 376) = true := by decide +kernel

theorem strong_row_377 :
    (checkStrongRecoveryChemical 377 false && checkStrongRecoveryChemical 377 true &&
      checkStrongRecoveryShape 377) = true := by decide +kernel

theorem strong_row_378 :
    (checkStrongRecoveryChemical 378 false && checkStrongRecoveryChemical 378 true &&
      checkStrongRecoveryShape 378) = true := by decide +kernel

theorem strong_row_379 :
    (checkStrongRecoveryChemical 379 false && checkStrongRecoveryChemical 379 true &&
      checkStrongRecoveryShape 379) = true := by decide +kernel

theorem strong_row_380 :
    (checkStrongRecoveryChemical 380 false && checkStrongRecoveryChemical 380 true &&
      checkStrongRecoveryShape 380) = true := by decide +kernel

theorem strong_row_381 :
    (checkStrongRecoveryChemical 381 false && checkStrongRecoveryChemical 381 true &&
      checkStrongRecoveryShape 381) = true := by decide +kernel

theorem strong_row_382 :
    (checkStrongRecoveryChemical 382 false && checkStrongRecoveryChemical 382 true &&
      checkStrongRecoveryShape 382) = true := by decide +kernel

theorem strong_row_383 :
    (checkStrongRecoveryChemical 383 false && checkStrongRecoveryChemical 383 true &&
      checkStrongRecoveryShape 383) = true := by decide +kernel

theorem strong_recovery_rows_368_383 :
    (List.range' 368 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_368, strong_row_369, strong_row_370, strong_row_371, strong_row_372, strong_row_373, strong_row_374, strong_row_375, strong_row_376, strong_row_377, strong_row_378, strong_row_379, strong_row_380, strong_row_381, strong_row_382, strong_row_383, Bool.and_self]

end P161Formal
