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

theorem strong_row_416 :
    (checkStrongRecoveryChemical 416 false && checkStrongRecoveryChemical 416 true &&
      checkStrongRecoveryShape 416) = true := by decide +kernel

theorem strong_row_417 :
    (checkStrongRecoveryChemical 417 false && checkStrongRecoveryChemical 417 true &&
      checkStrongRecoveryShape 417) = true := by decide +kernel

theorem strong_row_418 :
    (checkStrongRecoveryChemical 418 false && checkStrongRecoveryChemical 418 true &&
      checkStrongRecoveryShape 418) = true := by decide +kernel

theorem strong_row_419 :
    (checkStrongRecoveryChemical 419 false && checkStrongRecoveryChemical 419 true &&
      checkStrongRecoveryShape 419) = true := by decide +kernel

theorem strong_row_420 :
    (checkStrongRecoveryChemical 420 false && checkStrongRecoveryChemical 420 true &&
      checkStrongRecoveryShape 420) = true := by decide +kernel

theorem strong_row_421 :
    (checkStrongRecoveryChemical 421 false && checkStrongRecoveryChemical 421 true &&
      checkStrongRecoveryShape 421) = true := by decide +kernel

theorem strong_row_422 :
    (checkStrongRecoveryChemical 422 false && checkStrongRecoveryChemical 422 true &&
      checkStrongRecoveryShape 422) = true := by decide +kernel

theorem strong_row_423 :
    (checkStrongRecoveryChemical 423 false && checkStrongRecoveryChemical 423 true &&
      checkStrongRecoveryShape 423) = true := by decide +kernel

theorem strong_row_424 :
    (checkStrongRecoveryChemical 424 false && checkStrongRecoveryChemical 424 true &&
      checkStrongRecoveryShape 424) = true := by decide +kernel

theorem strong_row_425 :
    (checkStrongRecoveryChemical 425 false && checkStrongRecoveryChemical 425 true &&
      checkStrongRecoveryShape 425) = true := by decide +kernel

theorem strong_row_426 :
    (checkStrongRecoveryChemical 426 false && checkStrongRecoveryChemical 426 true &&
      checkStrongRecoveryShape 426) = true := by decide +kernel

theorem strong_row_427 :
    (checkStrongRecoveryChemical 427 false && checkStrongRecoveryChemical 427 true &&
      checkStrongRecoveryShape 427) = true := by decide +kernel

theorem strong_row_428 :
    (checkStrongRecoveryChemical 428 false && checkStrongRecoveryChemical 428 true &&
      checkStrongRecoveryShape 428) = true := by decide +kernel

theorem strong_row_429 :
    (checkStrongRecoveryChemical 429 false && checkStrongRecoveryChemical 429 true &&
      checkStrongRecoveryShape 429) = true := by decide +kernel

theorem strong_row_430 :
    (checkStrongRecoveryChemical 430 false && checkStrongRecoveryChemical 430 true &&
      checkStrongRecoveryShape 430) = true := by decide +kernel

theorem strong_row_431 :
    (checkStrongRecoveryChemical 431 false && checkStrongRecoveryChemical 431 true &&
      checkStrongRecoveryShape 431) = true := by decide +kernel

theorem strong_recovery_rows_416_431 :
    (List.range' 416 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_416, strong_row_417, strong_row_418, strong_row_419, strong_row_420, strong_row_421, strong_row_422, strong_row_423, strong_row_424, strong_row_425, strong_row_426, strong_row_427, strong_row_428, strong_row_429, strong_row_430, strong_row_431, Bool.and_self]

end P161Formal
