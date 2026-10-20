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

theorem strong_row_384 :
    (checkStrongRecoveryChemical 384 false && checkStrongRecoveryChemical 384 true &&
      checkStrongRecoveryShape 384) = true := by decide +kernel

theorem strong_row_385 :
    (checkStrongRecoveryChemical 385 false && checkStrongRecoveryChemical 385 true &&
      checkStrongRecoveryShape 385) = true := by decide +kernel

theorem strong_row_386 :
    (checkStrongRecoveryChemical 386 false && checkStrongRecoveryChemical 386 true &&
      checkStrongRecoveryShape 386) = true := by decide +kernel

theorem strong_row_387 :
    (checkStrongRecoveryChemical 387 false && checkStrongRecoveryChemical 387 true &&
      checkStrongRecoveryShape 387) = true := by decide +kernel

theorem strong_row_388 :
    (checkStrongRecoveryChemical 388 false && checkStrongRecoveryChemical 388 true &&
      checkStrongRecoveryShape 388) = true := by decide +kernel

theorem strong_row_389 :
    (checkStrongRecoveryChemical 389 false && checkStrongRecoveryChemical 389 true &&
      checkStrongRecoveryShape 389) = true := by decide +kernel

theorem strong_row_390 :
    (checkStrongRecoveryChemical 390 false && checkStrongRecoveryChemical 390 true &&
      checkStrongRecoveryShape 390) = true := by decide +kernel

theorem strong_row_391 :
    (checkStrongRecoveryChemical 391 false && checkStrongRecoveryChemical 391 true &&
      checkStrongRecoveryShape 391) = true := by decide +kernel

theorem strong_row_392 :
    (checkStrongRecoveryChemical 392 false && checkStrongRecoveryChemical 392 true &&
      checkStrongRecoveryShape 392) = true := by decide +kernel

theorem strong_row_393 :
    (checkStrongRecoveryChemical 393 false && checkStrongRecoveryChemical 393 true &&
      checkStrongRecoveryShape 393) = true := by decide +kernel

theorem strong_row_394 :
    (checkStrongRecoveryChemical 394 false && checkStrongRecoveryChemical 394 true &&
      checkStrongRecoveryShape 394) = true := by decide +kernel

theorem strong_row_395 :
    (checkStrongRecoveryChemical 395 false && checkStrongRecoveryChemical 395 true &&
      checkStrongRecoveryShape 395) = true := by decide +kernel

theorem strong_row_396 :
    (checkStrongRecoveryChemical 396 false && checkStrongRecoveryChemical 396 true &&
      checkStrongRecoveryShape 396) = true := by decide +kernel

theorem strong_row_397 :
    (checkStrongRecoveryChemical 397 false && checkStrongRecoveryChemical 397 true &&
      checkStrongRecoveryShape 397) = true := by decide +kernel

theorem strong_row_398 :
    (checkStrongRecoveryChemical 398 false && checkStrongRecoveryChemical 398 true &&
      checkStrongRecoveryShape 398) = true := by decide +kernel

theorem strong_row_399 :
    (checkStrongRecoveryChemical 399 false && checkStrongRecoveryChemical 399 true &&
      checkStrongRecoveryShape 399) = true := by decide +kernel

theorem strong_recovery_rows_384_399 :
    (List.range' 384 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_384, strong_row_385, strong_row_386, strong_row_387, strong_row_388, strong_row_389, strong_row_390, strong_row_391, strong_row_392, strong_row_393, strong_row_394, strong_row_395, strong_row_396, strong_row_397, strong_row_398, strong_row_399, Bool.and_self]

end P161Formal
