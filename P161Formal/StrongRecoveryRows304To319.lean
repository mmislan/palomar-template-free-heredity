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

theorem strong_row_304 :
    (checkStrongRecoveryChemical 304 false && checkStrongRecoveryChemical 304 true &&
      checkStrongRecoveryShape 304) = true := by decide +kernel

theorem strong_row_305 :
    (checkStrongRecoveryChemical 305 false && checkStrongRecoveryChemical 305 true &&
      checkStrongRecoveryShape 305) = true := by decide +kernel

theorem strong_row_306 :
    (checkStrongRecoveryChemical 306 false && checkStrongRecoveryChemical 306 true &&
      checkStrongRecoveryShape 306) = true := by decide +kernel

theorem strong_row_307 :
    (checkStrongRecoveryChemical 307 false && checkStrongRecoveryChemical 307 true &&
      checkStrongRecoveryShape 307) = true := by decide +kernel

theorem strong_row_308 :
    (checkStrongRecoveryChemical 308 false && checkStrongRecoveryChemical 308 true &&
      checkStrongRecoveryShape 308) = true := by decide +kernel

theorem strong_row_309 :
    (checkStrongRecoveryChemical 309 false && checkStrongRecoveryChemical 309 true &&
      checkStrongRecoveryShape 309) = true := by decide +kernel

theorem strong_row_310 :
    (checkStrongRecoveryChemical 310 false && checkStrongRecoveryChemical 310 true &&
      checkStrongRecoveryShape 310) = true := by decide +kernel

theorem strong_row_311 :
    (checkStrongRecoveryChemical 311 false && checkStrongRecoveryChemical 311 true &&
      checkStrongRecoveryShape 311) = true := by decide +kernel

theorem strong_row_312 :
    (checkStrongRecoveryChemical 312 false && checkStrongRecoveryChemical 312 true &&
      checkStrongRecoveryShape 312) = true := by decide +kernel

theorem strong_row_313 :
    (checkStrongRecoveryChemical 313 false && checkStrongRecoveryChemical 313 true &&
      checkStrongRecoveryShape 313) = true := by decide +kernel

theorem strong_row_314 :
    (checkStrongRecoveryChemical 314 false && checkStrongRecoveryChemical 314 true &&
      checkStrongRecoveryShape 314) = true := by decide +kernel

theorem strong_row_315 :
    (checkStrongRecoveryChemical 315 false && checkStrongRecoveryChemical 315 true &&
      checkStrongRecoveryShape 315) = true := by decide +kernel

theorem strong_row_316 :
    (checkStrongRecoveryChemical 316 false && checkStrongRecoveryChemical 316 true &&
      checkStrongRecoveryShape 316) = true := by decide +kernel

theorem strong_row_317 :
    (checkStrongRecoveryChemical 317 false && checkStrongRecoveryChemical 317 true &&
      checkStrongRecoveryShape 317) = true := by decide +kernel

theorem strong_row_318 :
    (checkStrongRecoveryChemical 318 false && checkStrongRecoveryChemical 318 true &&
      checkStrongRecoveryShape 318) = true := by decide +kernel

theorem strong_row_319 :
    (checkStrongRecoveryChemical 319 false && checkStrongRecoveryChemical 319 true &&
      checkStrongRecoveryShape 319) = true := by decide +kernel

theorem strong_recovery_rows_304_319 :
    (List.range' 304 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_304, strong_row_305, strong_row_306, strong_row_307, strong_row_308, strong_row_309, strong_row_310, strong_row_311, strong_row_312, strong_row_313, strong_row_314, strong_row_315, strong_row_316, strong_row_317, strong_row_318, strong_row_319, Bool.and_self]

end P161Formal
