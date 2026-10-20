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

theorem strong_row_192 :
    (checkStrongRecoveryChemical 192 false && checkStrongRecoveryChemical 192 true &&
      checkStrongRecoveryShape 192) = true := by decide +kernel

theorem strong_row_193 :
    (checkStrongRecoveryChemical 193 false && checkStrongRecoveryChemical 193 true &&
      checkStrongRecoveryShape 193) = true := by decide +kernel

theorem strong_row_194 :
    (checkStrongRecoveryChemical 194 false && checkStrongRecoveryChemical 194 true &&
      checkStrongRecoveryShape 194) = true := by decide +kernel

theorem strong_row_195 :
    (checkStrongRecoveryChemical 195 false && checkStrongRecoveryChemical 195 true &&
      checkStrongRecoveryShape 195) = true := by decide +kernel

theorem strong_row_196 :
    (checkStrongRecoveryChemical 196 false && checkStrongRecoveryChemical 196 true &&
      checkStrongRecoveryShape 196) = true := by decide +kernel

theorem strong_row_197 :
    (checkStrongRecoveryChemical 197 false && checkStrongRecoveryChemical 197 true &&
      checkStrongRecoveryShape 197) = true := by decide +kernel

theorem strong_row_198 :
    (checkStrongRecoveryChemical 198 false && checkStrongRecoveryChemical 198 true &&
      checkStrongRecoveryShape 198) = true := by decide +kernel

theorem strong_row_199 :
    (checkStrongRecoveryChemical 199 false && checkStrongRecoveryChemical 199 true &&
      checkStrongRecoveryShape 199) = true := by decide +kernel

theorem strong_row_200 :
    (checkStrongRecoveryChemical 200 false && checkStrongRecoveryChemical 200 true &&
      checkStrongRecoveryShape 200) = true := by decide +kernel

theorem strong_row_201 :
    (checkStrongRecoveryChemical 201 false && checkStrongRecoveryChemical 201 true &&
      checkStrongRecoveryShape 201) = true := by decide +kernel

theorem strong_row_202 :
    (checkStrongRecoveryChemical 202 false && checkStrongRecoveryChemical 202 true &&
      checkStrongRecoveryShape 202) = true := by decide +kernel

theorem strong_row_203 :
    (checkStrongRecoveryChemical 203 false && checkStrongRecoveryChemical 203 true &&
      checkStrongRecoveryShape 203) = true := by decide +kernel

theorem strong_row_204 :
    (checkStrongRecoveryChemical 204 false && checkStrongRecoveryChemical 204 true &&
      checkStrongRecoveryShape 204) = true := by decide +kernel

theorem strong_row_205 :
    (checkStrongRecoveryChemical 205 false && checkStrongRecoveryChemical 205 true &&
      checkStrongRecoveryShape 205) = true := by decide +kernel

theorem strong_row_206 :
    (checkStrongRecoveryChemical 206 false && checkStrongRecoveryChemical 206 true &&
      checkStrongRecoveryShape 206) = true := by decide +kernel

theorem strong_row_207 :
    (checkStrongRecoveryChemical 207 false && checkStrongRecoveryChemical 207 true &&
      checkStrongRecoveryShape 207) = true := by decide +kernel

theorem strong_recovery_rows_192_207 :
    (List.range' 192 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_192, strong_row_193, strong_row_194, strong_row_195, strong_row_196, strong_row_197, strong_row_198, strong_row_199, strong_row_200, strong_row_201, strong_row_202, strong_row_203, strong_row_204, strong_row_205, strong_row_206, strong_row_207, Bool.and_self]

end P161Formal
