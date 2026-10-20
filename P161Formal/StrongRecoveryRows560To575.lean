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

theorem strong_row_560 :
    (checkStrongRecoveryChemical 560 false && checkStrongRecoveryChemical 560 true &&
      checkStrongRecoveryShape 560) = true := by decide +kernel

theorem strong_row_561 :
    (checkStrongRecoveryChemical 561 false && checkStrongRecoveryChemical 561 true &&
      checkStrongRecoveryShape 561) = true := by decide +kernel

theorem strong_row_562 :
    (checkStrongRecoveryChemical 562 false && checkStrongRecoveryChemical 562 true &&
      checkStrongRecoveryShape 562) = true := by decide +kernel

theorem strong_row_563 :
    (checkStrongRecoveryChemical 563 false && checkStrongRecoveryChemical 563 true &&
      checkStrongRecoveryShape 563) = true := by decide +kernel

theorem strong_row_564 :
    (checkStrongRecoveryChemical 564 false && checkStrongRecoveryChemical 564 true &&
      checkStrongRecoveryShape 564) = true := by decide +kernel

theorem strong_row_565 :
    (checkStrongRecoveryChemical 565 false && checkStrongRecoveryChemical 565 true &&
      checkStrongRecoveryShape 565) = true := by decide +kernel

theorem strong_row_566 :
    (checkStrongRecoveryChemical 566 false && checkStrongRecoveryChemical 566 true &&
      checkStrongRecoveryShape 566) = true := by decide +kernel

theorem strong_row_567 :
    (checkStrongRecoveryChemical 567 false && checkStrongRecoveryChemical 567 true &&
      checkStrongRecoveryShape 567) = true := by decide +kernel

theorem strong_row_568 :
    (checkStrongRecoveryChemical 568 false && checkStrongRecoveryChemical 568 true &&
      checkStrongRecoveryShape 568) = true := by decide +kernel

theorem strong_row_569 :
    (checkStrongRecoveryChemical 569 false && checkStrongRecoveryChemical 569 true &&
      checkStrongRecoveryShape 569) = true := by decide +kernel

theorem strong_row_570 :
    (checkStrongRecoveryChemical 570 false && checkStrongRecoveryChemical 570 true &&
      checkStrongRecoveryShape 570) = true := by decide +kernel

theorem strong_row_571 :
    (checkStrongRecoveryChemical 571 false && checkStrongRecoveryChemical 571 true &&
      checkStrongRecoveryShape 571) = true := by decide +kernel

theorem strong_row_572 :
    (checkStrongRecoveryChemical 572 false && checkStrongRecoveryChemical 572 true &&
      checkStrongRecoveryShape 572) = true := by decide +kernel

theorem strong_row_573 :
    (checkStrongRecoveryChemical 573 false && checkStrongRecoveryChemical 573 true &&
      checkStrongRecoveryShape 573) = true := by decide +kernel

theorem strong_row_574 :
    (checkStrongRecoveryChemical 574 false && checkStrongRecoveryChemical 574 true &&
      checkStrongRecoveryShape 574) = true := by decide +kernel

theorem strong_row_575 :
    (checkStrongRecoveryChemical 575 false && checkStrongRecoveryChemical 575 true &&
      checkStrongRecoveryShape 575) = true := by decide +kernel

theorem strong_recovery_rows_560_575 :
    (List.range' 560 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_560, strong_row_561, strong_row_562, strong_row_563, strong_row_564, strong_row_565, strong_row_566, strong_row_567, strong_row_568, strong_row_569, strong_row_570, strong_row_571, strong_row_572, strong_row_573, strong_row_574, strong_row_575, Bool.and_self]

end P161Formal
