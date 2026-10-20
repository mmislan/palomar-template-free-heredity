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

theorem strong_row_640 :
    (checkStrongRecoveryChemical 640 false && checkStrongRecoveryChemical 640 true &&
      checkStrongRecoveryShape 640) = true := by decide +kernel

theorem strong_row_641 :
    (checkStrongRecoveryChemical 641 false && checkStrongRecoveryChemical 641 true &&
      checkStrongRecoveryShape 641) = true := by decide +kernel

theorem strong_row_642 :
    (checkStrongRecoveryChemical 642 false && checkStrongRecoveryChemical 642 true &&
      checkStrongRecoveryShape 642) = true := by decide +kernel

theorem strong_row_643 :
    (checkStrongRecoveryChemical 643 false && checkStrongRecoveryChemical 643 true &&
      checkStrongRecoveryShape 643) = true := by decide +kernel

theorem strong_row_644 :
    (checkStrongRecoveryChemical 644 false && checkStrongRecoveryChemical 644 true &&
      checkStrongRecoveryShape 644) = true := by decide +kernel

theorem strong_row_645 :
    (checkStrongRecoveryChemical 645 false && checkStrongRecoveryChemical 645 true &&
      checkStrongRecoveryShape 645) = true := by decide +kernel

theorem strong_row_646 :
    (checkStrongRecoveryChemical 646 false && checkStrongRecoveryChemical 646 true &&
      checkStrongRecoveryShape 646) = true := by decide +kernel

theorem strong_row_647 :
    (checkStrongRecoveryChemical 647 false && checkStrongRecoveryChemical 647 true &&
      checkStrongRecoveryShape 647) = true := by decide +kernel

theorem strong_row_648 :
    (checkStrongRecoveryChemical 648 false && checkStrongRecoveryChemical 648 true &&
      checkStrongRecoveryShape 648) = true := by decide +kernel

theorem strong_row_649 :
    (checkStrongRecoveryChemical 649 false && checkStrongRecoveryChemical 649 true &&
      checkStrongRecoveryShape 649) = true := by decide +kernel

theorem strong_row_650 :
    (checkStrongRecoveryChemical 650 false && checkStrongRecoveryChemical 650 true &&
      checkStrongRecoveryShape 650) = true := by decide +kernel

theorem strong_row_651 :
    (checkStrongRecoveryChemical 651 false && checkStrongRecoveryChemical 651 true &&
      checkStrongRecoveryShape 651) = true := by decide +kernel

theorem strong_row_652 :
    (checkStrongRecoveryChemical 652 false && checkStrongRecoveryChemical 652 true &&
      checkStrongRecoveryShape 652) = true := by decide +kernel

theorem strong_row_653 :
    (checkStrongRecoveryChemical 653 false && checkStrongRecoveryChemical 653 true &&
      checkStrongRecoveryShape 653) = true := by decide +kernel

theorem strong_row_654 :
    (checkStrongRecoveryChemical 654 false && checkStrongRecoveryChemical 654 true &&
      checkStrongRecoveryShape 654) = true := by decide +kernel

theorem strong_row_655 :
    (checkStrongRecoveryChemical 655 false && checkStrongRecoveryChemical 655 true &&
      checkStrongRecoveryShape 655) = true := by decide +kernel

theorem strong_recovery_rows_640_655 :
    (List.range' 640 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_640, strong_row_641, strong_row_642, strong_row_643, strong_row_644, strong_row_645, strong_row_646, strong_row_647, strong_row_648, strong_row_649, strong_row_650, strong_row_651, strong_row_652, strong_row_653, strong_row_654, strong_row_655, Bool.and_self]

end P161Formal
