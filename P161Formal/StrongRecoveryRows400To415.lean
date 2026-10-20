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

theorem strong_row_400 :
    (checkStrongRecoveryChemical 400 false && checkStrongRecoveryChemical 400 true &&
      checkStrongRecoveryShape 400) = true := by decide +kernel

theorem strong_row_401 :
    (checkStrongRecoveryChemical 401 false && checkStrongRecoveryChemical 401 true &&
      checkStrongRecoveryShape 401) = true := by decide +kernel

theorem strong_row_402 :
    (checkStrongRecoveryChemical 402 false && checkStrongRecoveryChemical 402 true &&
      checkStrongRecoveryShape 402) = true := by decide +kernel

theorem strong_row_403 :
    (checkStrongRecoveryChemical 403 false && checkStrongRecoveryChemical 403 true &&
      checkStrongRecoveryShape 403) = true := by decide +kernel

theorem strong_row_404 :
    (checkStrongRecoveryChemical 404 false && checkStrongRecoveryChemical 404 true &&
      checkStrongRecoveryShape 404) = true := by decide +kernel

theorem strong_row_405 :
    (checkStrongRecoveryChemical 405 false && checkStrongRecoveryChemical 405 true &&
      checkStrongRecoveryShape 405) = true := by decide +kernel

theorem strong_row_406 :
    (checkStrongRecoveryChemical 406 false && checkStrongRecoveryChemical 406 true &&
      checkStrongRecoveryShape 406) = true := by decide +kernel

theorem strong_row_407 :
    (checkStrongRecoveryChemical 407 false && checkStrongRecoveryChemical 407 true &&
      checkStrongRecoveryShape 407) = true := by decide +kernel

theorem strong_row_408 :
    (checkStrongRecoveryChemical 408 false && checkStrongRecoveryChemical 408 true &&
      checkStrongRecoveryShape 408) = true := by decide +kernel

theorem strong_row_409 :
    (checkStrongRecoveryChemical 409 false && checkStrongRecoveryChemical 409 true &&
      checkStrongRecoveryShape 409) = true := by decide +kernel

theorem strong_row_410 :
    (checkStrongRecoveryChemical 410 false && checkStrongRecoveryChemical 410 true &&
      checkStrongRecoveryShape 410) = true := by decide +kernel

theorem strong_row_411 :
    (checkStrongRecoveryChemical 411 false && checkStrongRecoveryChemical 411 true &&
      checkStrongRecoveryShape 411) = true := by decide +kernel

theorem strong_row_412 :
    (checkStrongRecoveryChemical 412 false && checkStrongRecoveryChemical 412 true &&
      checkStrongRecoveryShape 412) = true := by decide +kernel

theorem strong_row_413 :
    (checkStrongRecoveryChemical 413 false && checkStrongRecoveryChemical 413 true &&
      checkStrongRecoveryShape 413) = true := by decide +kernel

theorem strong_row_414 :
    (checkStrongRecoveryChemical 414 false && checkStrongRecoveryChemical 414 true &&
      checkStrongRecoveryShape 414) = true := by decide +kernel

theorem strong_row_415 :
    (checkStrongRecoveryChemical 415 false && checkStrongRecoveryChemical 415 true &&
      checkStrongRecoveryShape 415) = true := by decide +kernel

theorem strong_recovery_rows_400_415 :
    (List.range' 400 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_400, strong_row_401, strong_row_402, strong_row_403, strong_row_404, strong_row_405, strong_row_406, strong_row_407, strong_row_408, strong_row_409, strong_row_410, strong_row_411, strong_row_412, strong_row_413, strong_row_414, strong_row_415, Bool.and_self]

end P161Formal
