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

theorem strong_row_288 :
    (checkStrongRecoveryChemical 288 false && checkStrongRecoveryChemical 288 true &&
      checkStrongRecoveryShape 288) = true := by decide +kernel

theorem strong_row_289 :
    (checkStrongRecoveryChemical 289 false && checkStrongRecoveryChemical 289 true &&
      checkStrongRecoveryShape 289) = true := by decide +kernel

theorem strong_row_290 :
    (checkStrongRecoveryChemical 290 false && checkStrongRecoveryChemical 290 true &&
      checkStrongRecoveryShape 290) = true := by decide +kernel

theorem strong_row_291 :
    (checkStrongRecoveryChemical 291 false && checkStrongRecoveryChemical 291 true &&
      checkStrongRecoveryShape 291) = true := by decide +kernel

theorem strong_row_292 :
    (checkStrongRecoveryChemical 292 false && checkStrongRecoveryChemical 292 true &&
      checkStrongRecoveryShape 292) = true := by decide +kernel

theorem strong_row_293 :
    (checkStrongRecoveryChemical 293 false && checkStrongRecoveryChemical 293 true &&
      checkStrongRecoveryShape 293) = true := by decide +kernel

theorem strong_row_294 :
    (checkStrongRecoveryChemical 294 false && checkStrongRecoveryChemical 294 true &&
      checkStrongRecoveryShape 294) = true := by decide +kernel

theorem strong_row_295 :
    (checkStrongRecoveryChemical 295 false && checkStrongRecoveryChemical 295 true &&
      checkStrongRecoveryShape 295) = true := by decide +kernel

theorem strong_row_296 :
    (checkStrongRecoveryChemical 296 false && checkStrongRecoveryChemical 296 true &&
      checkStrongRecoveryShape 296) = true := by decide +kernel

theorem strong_row_297 :
    (checkStrongRecoveryChemical 297 false && checkStrongRecoveryChemical 297 true &&
      checkStrongRecoveryShape 297) = true := by decide +kernel

theorem strong_row_298 :
    (checkStrongRecoveryChemical 298 false && checkStrongRecoveryChemical 298 true &&
      checkStrongRecoveryShape 298) = true := by decide +kernel

theorem strong_row_299 :
    (checkStrongRecoveryChemical 299 false && checkStrongRecoveryChemical 299 true &&
      checkStrongRecoveryShape 299) = true := by decide +kernel

theorem strong_row_300 :
    (checkStrongRecoveryChemical 300 false && checkStrongRecoveryChemical 300 true &&
      checkStrongRecoveryShape 300) = true := by decide +kernel

theorem strong_row_301 :
    (checkStrongRecoveryChemical 301 false && checkStrongRecoveryChemical 301 true &&
      checkStrongRecoveryShape 301) = true := by decide +kernel

theorem strong_row_302 :
    (checkStrongRecoveryChemical 302 false && checkStrongRecoveryChemical 302 true &&
      checkStrongRecoveryShape 302) = true := by decide +kernel

theorem strong_row_303 :
    (checkStrongRecoveryChemical 303 false && checkStrongRecoveryChemical 303 true &&
      checkStrongRecoveryShape 303) = true := by decide +kernel

theorem strong_recovery_rows_288_303 :
    (List.range' 288 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_288, strong_row_289, strong_row_290, strong_row_291, strong_row_292, strong_row_293, strong_row_294, strong_row_295, strong_row_296, strong_row_297, strong_row_298, strong_row_299, strong_row_300, strong_row_301, strong_row_302, strong_row_303, Bool.and_self]

end P161Formal
