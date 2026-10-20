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

theorem strong_row_608 :
    (checkStrongRecoveryChemical 608 false && checkStrongRecoveryChemical 608 true &&
      checkStrongRecoveryShape 608) = true := by decide +kernel

theorem strong_row_609 :
    (checkStrongRecoveryChemical 609 false && checkStrongRecoveryChemical 609 true &&
      checkStrongRecoveryShape 609) = true := by decide +kernel

theorem strong_row_610 :
    (checkStrongRecoveryChemical 610 false && checkStrongRecoveryChemical 610 true &&
      checkStrongRecoveryShape 610) = true := by decide +kernel

theorem strong_row_611 :
    (checkStrongRecoveryChemical 611 false && checkStrongRecoveryChemical 611 true &&
      checkStrongRecoveryShape 611) = true := by decide +kernel

theorem strong_row_612 :
    (checkStrongRecoveryChemical 612 false && checkStrongRecoveryChemical 612 true &&
      checkStrongRecoveryShape 612) = true := by decide +kernel

theorem strong_row_613 :
    (checkStrongRecoveryChemical 613 false && checkStrongRecoveryChemical 613 true &&
      checkStrongRecoveryShape 613) = true := by decide +kernel

theorem strong_row_614 :
    (checkStrongRecoveryChemical 614 false && checkStrongRecoveryChemical 614 true &&
      checkStrongRecoveryShape 614) = true := by decide +kernel

theorem strong_row_615 :
    (checkStrongRecoveryChemical 615 false && checkStrongRecoveryChemical 615 true &&
      checkStrongRecoveryShape 615) = true := by decide +kernel

theorem strong_row_616 :
    (checkStrongRecoveryChemical 616 false && checkStrongRecoveryChemical 616 true &&
      checkStrongRecoveryShape 616) = true := by decide +kernel

theorem strong_row_617 :
    (checkStrongRecoveryChemical 617 false && checkStrongRecoveryChemical 617 true &&
      checkStrongRecoveryShape 617) = true := by decide +kernel

theorem strong_row_618 :
    (checkStrongRecoveryChemical 618 false && checkStrongRecoveryChemical 618 true &&
      checkStrongRecoveryShape 618) = true := by decide +kernel

theorem strong_row_619 :
    (checkStrongRecoveryChemical 619 false && checkStrongRecoveryChemical 619 true &&
      checkStrongRecoveryShape 619) = true := by decide +kernel

theorem strong_row_620 :
    (checkStrongRecoveryChemical 620 false && checkStrongRecoveryChemical 620 true &&
      checkStrongRecoveryShape 620) = true := by decide +kernel

theorem strong_row_621 :
    (checkStrongRecoveryChemical 621 false && checkStrongRecoveryChemical 621 true &&
      checkStrongRecoveryShape 621) = true := by decide +kernel

theorem strong_row_622 :
    (checkStrongRecoveryChemical 622 false && checkStrongRecoveryChemical 622 true &&
      checkStrongRecoveryShape 622) = true := by decide +kernel

theorem strong_row_623 :
    (checkStrongRecoveryChemical 623 false && checkStrongRecoveryChemical 623 true &&
      checkStrongRecoveryShape 623) = true := by decide +kernel

theorem strong_recovery_rows_608_623 :
    (List.range' 608 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_608, strong_row_609, strong_row_610, strong_row_611, strong_row_612, strong_row_613, strong_row_614, strong_row_615, strong_row_616, strong_row_617, strong_row_618, strong_row_619, strong_row_620, strong_row_621, strong_row_622, strong_row_623, Bool.and_self]

end P161Formal
