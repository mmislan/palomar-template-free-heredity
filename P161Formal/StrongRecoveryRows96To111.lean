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

theorem strong_row_96 :
    (checkStrongRecoveryChemical 96 false && checkStrongRecoveryChemical 96 true &&
      checkStrongRecoveryShape 96) = true := by decide +kernel

theorem strong_row_97 :
    (checkStrongRecoveryChemical 97 false && checkStrongRecoveryChemical 97 true &&
      checkStrongRecoveryShape 97) = true := by decide +kernel

theorem strong_row_98 :
    (checkStrongRecoveryChemical 98 false && checkStrongRecoveryChemical 98 true &&
      checkStrongRecoveryShape 98) = true := by decide +kernel

theorem strong_row_99 :
    (checkStrongRecoveryChemical 99 false && checkStrongRecoveryChemical 99 true &&
      checkStrongRecoveryShape 99) = true := by decide +kernel

theorem strong_row_100 :
    (checkStrongRecoveryChemical 100 false && checkStrongRecoveryChemical 100 true &&
      checkStrongRecoveryShape 100) = true := by decide +kernel

theorem strong_row_101 :
    (checkStrongRecoveryChemical 101 false && checkStrongRecoveryChemical 101 true &&
      checkStrongRecoveryShape 101) = true := by decide +kernel

theorem strong_row_102 :
    (checkStrongRecoveryChemical 102 false && checkStrongRecoveryChemical 102 true &&
      checkStrongRecoveryShape 102) = true := by decide +kernel

theorem strong_row_103 :
    (checkStrongRecoveryChemical 103 false && checkStrongRecoveryChemical 103 true &&
      checkStrongRecoveryShape 103) = true := by decide +kernel

theorem strong_row_104 :
    (checkStrongRecoveryChemical 104 false && checkStrongRecoveryChemical 104 true &&
      checkStrongRecoveryShape 104) = true := by decide +kernel

theorem strong_row_105 :
    (checkStrongRecoveryChemical 105 false && checkStrongRecoveryChemical 105 true &&
      checkStrongRecoveryShape 105) = true := by decide +kernel

theorem strong_row_106 :
    (checkStrongRecoveryChemical 106 false && checkStrongRecoveryChemical 106 true &&
      checkStrongRecoveryShape 106) = true := by decide +kernel

theorem strong_row_107 :
    (checkStrongRecoveryChemical 107 false && checkStrongRecoveryChemical 107 true &&
      checkStrongRecoveryShape 107) = true := by decide +kernel

theorem strong_row_108 :
    (checkStrongRecoveryChemical 108 false && checkStrongRecoveryChemical 108 true &&
      checkStrongRecoveryShape 108) = true := by decide +kernel

theorem strong_row_109 :
    (checkStrongRecoveryChemical 109 false && checkStrongRecoveryChemical 109 true &&
      checkStrongRecoveryShape 109) = true := by decide +kernel

theorem strong_row_110 :
    (checkStrongRecoveryChemical 110 false && checkStrongRecoveryChemical 110 true &&
      checkStrongRecoveryShape 110) = true := by decide +kernel

theorem strong_row_111 :
    (checkStrongRecoveryChemical 111 false && checkStrongRecoveryChemical 111 true &&
      checkStrongRecoveryShape 111) = true := by decide +kernel

theorem strong_recovery_rows_96_111 :
    (List.range' 96 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_96, strong_row_97, strong_row_98, strong_row_99, strong_row_100, strong_row_101, strong_row_102, strong_row_103, strong_row_104, strong_row_105, strong_row_106, strong_row_107, strong_row_108, strong_row_109, strong_row_110, strong_row_111, Bool.and_self]

end P161Formal
