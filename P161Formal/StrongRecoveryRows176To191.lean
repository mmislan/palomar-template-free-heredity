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

theorem strong_row_176 :
    (checkStrongRecoveryChemical 176 false && checkStrongRecoveryChemical 176 true &&
      checkStrongRecoveryShape 176) = true := by decide +kernel

theorem strong_row_177 :
    (checkStrongRecoveryChemical 177 false && checkStrongRecoveryChemical 177 true &&
      checkStrongRecoveryShape 177) = true := by decide +kernel

theorem strong_row_178 :
    (checkStrongRecoveryChemical 178 false && checkStrongRecoveryChemical 178 true &&
      checkStrongRecoveryShape 178) = true := by decide +kernel

theorem strong_row_179 :
    (checkStrongRecoveryChemical 179 false && checkStrongRecoveryChemical 179 true &&
      checkStrongRecoveryShape 179) = true := by decide +kernel

theorem strong_row_180 :
    (checkStrongRecoveryChemical 180 false && checkStrongRecoveryChemical 180 true &&
      checkStrongRecoveryShape 180) = true := by decide +kernel

theorem strong_row_181 :
    (checkStrongRecoveryChemical 181 false && checkStrongRecoveryChemical 181 true &&
      checkStrongRecoveryShape 181) = true := by decide +kernel

theorem strong_row_182 :
    (checkStrongRecoveryChemical 182 false && checkStrongRecoveryChemical 182 true &&
      checkStrongRecoveryShape 182) = true := by decide +kernel

theorem strong_row_183 :
    (checkStrongRecoveryChemical 183 false && checkStrongRecoveryChemical 183 true &&
      checkStrongRecoveryShape 183) = true := by decide +kernel

theorem strong_row_184 :
    (checkStrongRecoveryChemical 184 false && checkStrongRecoveryChemical 184 true &&
      checkStrongRecoveryShape 184) = true := by decide +kernel

theorem strong_row_185 :
    (checkStrongRecoveryChemical 185 false && checkStrongRecoveryChemical 185 true &&
      checkStrongRecoveryShape 185) = true := by decide +kernel

theorem strong_row_186 :
    (checkStrongRecoveryChemical 186 false && checkStrongRecoveryChemical 186 true &&
      checkStrongRecoveryShape 186) = true := by decide +kernel

theorem strong_row_187 :
    (checkStrongRecoveryChemical 187 false && checkStrongRecoveryChemical 187 true &&
      checkStrongRecoveryShape 187) = true := by decide +kernel

theorem strong_row_188 :
    (checkStrongRecoveryChemical 188 false && checkStrongRecoveryChemical 188 true &&
      checkStrongRecoveryShape 188) = true := by decide +kernel

theorem strong_row_189 :
    (checkStrongRecoveryChemical 189 false && checkStrongRecoveryChemical 189 true &&
      checkStrongRecoveryShape 189) = true := by decide +kernel

theorem strong_row_190 :
    (checkStrongRecoveryChemical 190 false && checkStrongRecoveryChemical 190 true &&
      checkStrongRecoveryShape 190) = true := by decide +kernel

theorem strong_row_191 :
    (checkStrongRecoveryChemical 191 false && checkStrongRecoveryChemical 191 true &&
      checkStrongRecoveryShape 191) = true := by decide +kernel

theorem strong_recovery_rows_176_191 :
    (List.range' 176 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_176, strong_row_177, strong_row_178, strong_row_179, strong_row_180, strong_row_181, strong_row_182, strong_row_183, strong_row_184, strong_row_185, strong_row_186, strong_row_187, strong_row_188, strong_row_189, strong_row_190, strong_row_191, Bool.and_self]

end P161Formal
