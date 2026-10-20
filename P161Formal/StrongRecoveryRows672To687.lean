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

theorem strong_row_672 :
    (checkStrongRecoveryChemical 672 false && checkStrongRecoveryChemical 672 true &&
      checkStrongRecoveryShape 672) = true := by decide +kernel

theorem strong_row_673 :
    (checkStrongRecoveryChemical 673 false && checkStrongRecoveryChemical 673 true &&
      checkStrongRecoveryShape 673) = true := by decide +kernel

theorem strong_row_674 :
    (checkStrongRecoveryChemical 674 false && checkStrongRecoveryChemical 674 true &&
      checkStrongRecoveryShape 674) = true := by decide +kernel

theorem strong_row_675 :
    (checkStrongRecoveryChemical 675 false && checkStrongRecoveryChemical 675 true &&
      checkStrongRecoveryShape 675) = true := by decide +kernel

theorem strong_row_676 :
    (checkStrongRecoveryChemical 676 false && checkStrongRecoveryChemical 676 true &&
      checkStrongRecoveryShape 676) = true := by decide +kernel

theorem strong_row_677 :
    (checkStrongRecoveryChemical 677 false && checkStrongRecoveryChemical 677 true &&
      checkStrongRecoveryShape 677) = true := by decide +kernel

theorem strong_row_678 :
    (checkStrongRecoveryChemical 678 false && checkStrongRecoveryChemical 678 true &&
      checkStrongRecoveryShape 678) = true := by decide +kernel

theorem strong_row_679 :
    (checkStrongRecoveryChemical 679 false && checkStrongRecoveryChemical 679 true &&
      checkStrongRecoveryShape 679) = true := by decide +kernel

theorem strong_row_680 :
    (checkStrongRecoveryChemical 680 false && checkStrongRecoveryChemical 680 true &&
      checkStrongRecoveryShape 680) = true := by decide +kernel

theorem strong_row_681 :
    (checkStrongRecoveryChemical 681 false && checkStrongRecoveryChemical 681 true &&
      checkStrongRecoveryShape 681) = true := by decide +kernel

theorem strong_row_682 :
    (checkStrongRecoveryChemical 682 false && checkStrongRecoveryChemical 682 true &&
      checkStrongRecoveryShape 682) = true := by decide +kernel

theorem strong_row_683 :
    (checkStrongRecoveryChemical 683 false && checkStrongRecoveryChemical 683 true &&
      checkStrongRecoveryShape 683) = true := by decide +kernel

theorem strong_row_684 :
    (checkStrongRecoveryChemical 684 false && checkStrongRecoveryChemical 684 true &&
      checkStrongRecoveryShape 684) = true := by decide +kernel

theorem strong_row_685 :
    (checkStrongRecoveryChemical 685 false && checkStrongRecoveryChemical 685 true &&
      checkStrongRecoveryShape 685) = true := by decide +kernel

theorem strong_row_686 :
    (checkStrongRecoveryChemical 686 false && checkStrongRecoveryChemical 686 true &&
      checkStrongRecoveryShape 686) = true := by decide +kernel

theorem strong_row_687 :
    (checkStrongRecoveryChemical 687 false && checkStrongRecoveryChemical 687 true &&
      checkStrongRecoveryShape 687) = true := by decide +kernel

theorem strong_recovery_rows_672_687 :
    (List.range' 672 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_672, strong_row_673, strong_row_674, strong_row_675, strong_row_676, strong_row_677, strong_row_678, strong_row_679, strong_row_680, strong_row_681, strong_row_682, strong_row_683, strong_row_684, strong_row_685, strong_row_686, strong_row_687, Bool.and_self]

end P161Formal
