module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_672 : checkTailEnclosureParent 672 = true := by decide +kernel

theorem tail_enclosure_row_673 : checkTailEnclosureParent 673 = true := by decide +kernel

theorem tail_enclosure_row_674 : checkTailEnclosureParent 674 = true := by decide +kernel

theorem tail_enclosure_row_675 : checkTailEnclosureParent 675 = true := by decide +kernel

theorem tail_enclosure_row_676 : checkTailEnclosureParent 676 = true := by decide +kernel

theorem tail_enclosure_row_677 : checkTailEnclosureParent 677 = true := by decide +kernel

theorem tail_enclosure_row_678 : checkTailEnclosureParent 678 = true := by decide +kernel

theorem tail_enclosure_row_679 : checkTailEnclosureParent 679 = true := by decide +kernel

theorem tail_enclosure_row_680 : checkTailEnclosureParent 680 = true := by decide +kernel

theorem tail_enclosure_row_681 : checkTailEnclosureParent 681 = true := by decide +kernel

theorem tail_enclosure_row_682 : checkTailEnclosureParent 682 = true := by decide +kernel

theorem tail_enclosure_row_683 : checkTailEnclosureParent 683 = true := by decide +kernel

theorem tail_enclosure_row_684 : checkTailEnclosureParent 684 = true := by decide +kernel

theorem tail_enclosure_row_685 : checkTailEnclosureParent 685 = true := by decide +kernel

theorem tail_enclosure_row_686 : checkTailEnclosureParent 686 = true := by decide +kernel

theorem tail_enclosure_row_687 : checkTailEnclosureParent 687 = true := by decide +kernel

theorem tail_enclosure_rows_672_687 :
    (List.range' 672 16).all checkTailEnclosureParent = true := by
  change ([672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_672, tail_enclosure_row_673, tail_enclosure_row_674, tail_enclosure_row_675, tail_enclosure_row_676, tail_enclosure_row_677, tail_enclosure_row_678, tail_enclosure_row_679, tail_enclosure_row_680, tail_enclosure_row_681, tail_enclosure_row_682, tail_enclosure_row_683, tail_enclosure_row_684, tail_enclosure_row_685, tail_enclosure_row_686, tail_enclosure_row_687,Bool.and_self]

end P161Formal
