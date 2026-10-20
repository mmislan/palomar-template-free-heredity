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

theorem strong_row_624 :
    (checkStrongRecoveryChemical 624 false && checkStrongRecoveryChemical 624 true &&
      checkStrongRecoveryShape 624) = true := by decide +kernel

theorem strong_row_625 :
    (checkStrongRecoveryChemical 625 false && checkStrongRecoveryChemical 625 true &&
      checkStrongRecoveryShape 625) = true := by decide +kernel

theorem strong_row_626 :
    (checkStrongRecoveryChemical 626 false && checkStrongRecoveryChemical 626 true &&
      checkStrongRecoveryShape 626) = true := by decide +kernel

theorem strong_row_627 :
    (checkStrongRecoveryChemical 627 false && checkStrongRecoveryChemical 627 true &&
      checkStrongRecoveryShape 627) = true := by decide +kernel

theorem strong_row_628 :
    (checkStrongRecoveryChemical 628 false && checkStrongRecoveryChemical 628 true &&
      checkStrongRecoveryShape 628) = true := by decide +kernel

theorem strong_row_629 :
    (checkStrongRecoveryChemical 629 false && checkStrongRecoveryChemical 629 true &&
      checkStrongRecoveryShape 629) = true := by decide +kernel

theorem strong_row_630 :
    (checkStrongRecoveryChemical 630 false && checkStrongRecoveryChemical 630 true &&
      checkStrongRecoveryShape 630) = true := by decide +kernel

theorem strong_row_631 :
    (checkStrongRecoveryChemical 631 false && checkStrongRecoveryChemical 631 true &&
      checkStrongRecoveryShape 631) = true := by decide +kernel

theorem strong_row_632 :
    (checkStrongRecoveryChemical 632 false && checkStrongRecoveryChemical 632 true &&
      checkStrongRecoveryShape 632) = true := by decide +kernel

theorem strong_row_633 :
    (checkStrongRecoveryChemical 633 false && checkStrongRecoveryChemical 633 true &&
      checkStrongRecoveryShape 633) = true := by decide +kernel

theorem strong_row_634 :
    (checkStrongRecoveryChemical 634 false && checkStrongRecoveryChemical 634 true &&
      checkStrongRecoveryShape 634) = true := by decide +kernel

theorem strong_row_635 :
    (checkStrongRecoveryChemical 635 false && checkStrongRecoveryChemical 635 true &&
      checkStrongRecoveryShape 635) = true := by decide +kernel

theorem strong_row_636 :
    (checkStrongRecoveryChemical 636 false && checkStrongRecoveryChemical 636 true &&
      checkStrongRecoveryShape 636) = true := by decide +kernel

theorem strong_row_637 :
    (checkStrongRecoveryChemical 637 false && checkStrongRecoveryChemical 637 true &&
      checkStrongRecoveryShape 637) = true := by decide +kernel

theorem strong_row_638 :
    (checkStrongRecoveryChemical 638 false && checkStrongRecoveryChemical 638 true &&
      checkStrongRecoveryShape 638) = true := by decide +kernel

theorem strong_row_639 :
    (checkStrongRecoveryChemical 639 false && checkStrongRecoveryChemical 639 true &&
      checkStrongRecoveryShape 639) = true := by decide +kernel

theorem strong_recovery_rows_624_639 :
    (List.range' 624 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_624, strong_row_625, strong_row_626, strong_row_627, strong_row_628, strong_row_629, strong_row_630, strong_row_631, strong_row_632, strong_row_633, strong_row_634, strong_row_635, strong_row_636, strong_row_637, strong_row_638, strong_row_639, Bool.and_self]

end P161Formal
