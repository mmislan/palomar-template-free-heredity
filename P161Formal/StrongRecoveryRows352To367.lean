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

theorem strong_row_352 :
    (checkStrongRecoveryChemical 352 false && checkStrongRecoveryChemical 352 true &&
      checkStrongRecoveryShape 352) = true := by decide +kernel

theorem strong_row_353 :
    (checkStrongRecoveryChemical 353 false && checkStrongRecoveryChemical 353 true &&
      checkStrongRecoveryShape 353) = true := by decide +kernel

theorem strong_row_354 :
    (checkStrongRecoveryChemical 354 false && checkStrongRecoveryChemical 354 true &&
      checkStrongRecoveryShape 354) = true := by decide +kernel

theorem strong_row_355 :
    (checkStrongRecoveryChemical 355 false && checkStrongRecoveryChemical 355 true &&
      checkStrongRecoveryShape 355) = true := by decide +kernel

theorem strong_row_356 :
    (checkStrongRecoveryChemical 356 false && checkStrongRecoveryChemical 356 true &&
      checkStrongRecoveryShape 356) = true := by decide +kernel

theorem strong_row_357 :
    (checkStrongRecoveryChemical 357 false && checkStrongRecoveryChemical 357 true &&
      checkStrongRecoveryShape 357) = true := by decide +kernel

theorem strong_row_358 :
    (checkStrongRecoveryChemical 358 false && checkStrongRecoveryChemical 358 true &&
      checkStrongRecoveryShape 358) = true := by decide +kernel

theorem strong_row_359 :
    (checkStrongRecoveryChemical 359 false && checkStrongRecoveryChemical 359 true &&
      checkStrongRecoveryShape 359) = true := by decide +kernel

theorem strong_row_360 :
    (checkStrongRecoveryChemical 360 false && checkStrongRecoveryChemical 360 true &&
      checkStrongRecoveryShape 360) = true := by decide +kernel

theorem strong_row_361 :
    (checkStrongRecoveryChemical 361 false && checkStrongRecoveryChemical 361 true &&
      checkStrongRecoveryShape 361) = true := by decide +kernel

theorem strong_row_362 :
    (checkStrongRecoveryChemical 362 false && checkStrongRecoveryChemical 362 true &&
      checkStrongRecoveryShape 362) = true := by decide +kernel

theorem strong_row_363 :
    (checkStrongRecoveryChemical 363 false && checkStrongRecoveryChemical 363 true &&
      checkStrongRecoveryShape 363) = true := by decide +kernel

theorem strong_row_364 :
    (checkStrongRecoveryChemical 364 false && checkStrongRecoveryChemical 364 true &&
      checkStrongRecoveryShape 364) = true := by decide +kernel

theorem strong_row_365 :
    (checkStrongRecoveryChemical 365 false && checkStrongRecoveryChemical 365 true &&
      checkStrongRecoveryShape 365) = true := by decide +kernel

theorem strong_row_366 :
    (checkStrongRecoveryChemical 366 false && checkStrongRecoveryChemical 366 true &&
      checkStrongRecoveryShape 366) = true := by decide +kernel

theorem strong_row_367 :
    (checkStrongRecoveryChemical 367 false && checkStrongRecoveryChemical 367 true &&
      checkStrongRecoveryShape 367) = true := by decide +kernel

theorem strong_recovery_rows_352_367 :
    (List.range' 352 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_352, strong_row_353, strong_row_354, strong_row_355, strong_row_356, strong_row_357, strong_row_358, strong_row_359, strong_row_360, strong_row_361, strong_row_362, strong_row_363, strong_row_364, strong_row_365, strong_row_366, strong_row_367, Bool.and_self]

end P161Formal
