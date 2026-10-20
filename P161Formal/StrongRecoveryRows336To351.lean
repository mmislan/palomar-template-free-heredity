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

theorem strong_row_336 :
    (checkStrongRecoveryChemical 336 false && checkStrongRecoveryChemical 336 true &&
      checkStrongRecoveryShape 336) = true := by decide +kernel

theorem strong_row_337 :
    (checkStrongRecoveryChemical 337 false && checkStrongRecoveryChemical 337 true &&
      checkStrongRecoveryShape 337) = true := by decide +kernel

theorem strong_row_338 :
    (checkStrongRecoveryChemical 338 false && checkStrongRecoveryChemical 338 true &&
      checkStrongRecoveryShape 338) = true := by decide +kernel

theorem strong_row_339 :
    (checkStrongRecoveryChemical 339 false && checkStrongRecoveryChemical 339 true &&
      checkStrongRecoveryShape 339) = true := by decide +kernel

theorem strong_row_340 :
    (checkStrongRecoveryChemical 340 false && checkStrongRecoveryChemical 340 true &&
      checkStrongRecoveryShape 340) = true := by decide +kernel

theorem strong_row_341 :
    (checkStrongRecoveryChemical 341 false && checkStrongRecoveryChemical 341 true &&
      checkStrongRecoveryShape 341) = true := by decide +kernel

theorem strong_row_342 :
    (checkStrongRecoveryChemical 342 false && checkStrongRecoveryChemical 342 true &&
      checkStrongRecoveryShape 342) = true := by decide +kernel

theorem strong_row_343 :
    (checkStrongRecoveryChemical 343 false && checkStrongRecoveryChemical 343 true &&
      checkStrongRecoveryShape 343) = true := by decide +kernel

theorem strong_row_344 :
    (checkStrongRecoveryChemical 344 false && checkStrongRecoveryChemical 344 true &&
      checkStrongRecoveryShape 344) = true := by decide +kernel

theorem strong_row_345 :
    (checkStrongRecoveryChemical 345 false && checkStrongRecoveryChemical 345 true &&
      checkStrongRecoveryShape 345) = true := by decide +kernel

theorem strong_row_346 :
    (checkStrongRecoveryChemical 346 false && checkStrongRecoveryChemical 346 true &&
      checkStrongRecoveryShape 346) = true := by decide +kernel

theorem strong_row_347 :
    (checkStrongRecoveryChemical 347 false && checkStrongRecoveryChemical 347 true &&
      checkStrongRecoveryShape 347) = true := by decide +kernel

theorem strong_row_348 :
    (checkStrongRecoveryChemical 348 false && checkStrongRecoveryChemical 348 true &&
      checkStrongRecoveryShape 348) = true := by decide +kernel

theorem strong_row_349 :
    (checkStrongRecoveryChemical 349 false && checkStrongRecoveryChemical 349 true &&
      checkStrongRecoveryShape 349) = true := by decide +kernel

theorem strong_row_350 :
    (checkStrongRecoveryChemical 350 false && checkStrongRecoveryChemical 350 true &&
      checkStrongRecoveryShape 350) = true := by decide +kernel

theorem strong_row_351 :
    (checkStrongRecoveryChemical 351 false && checkStrongRecoveryChemical 351 true &&
      checkStrongRecoveryShape 351) = true := by decide +kernel

theorem strong_recovery_rows_336_351 :
    (List.range' 336 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_336, strong_row_337, strong_row_338, strong_row_339, strong_row_340, strong_row_341, strong_row_342, strong_row_343, strong_row_344, strong_row_345, strong_row_346, strong_row_347, strong_row_348, strong_row_349, strong_row_350, strong_row_351, Bool.and_self]

end P161Formal
