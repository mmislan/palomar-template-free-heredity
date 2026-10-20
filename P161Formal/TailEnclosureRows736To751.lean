module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_736 : checkTailEnclosureParent 736 = true := by decide +kernel

theorem tail_enclosure_row_737 : checkTailEnclosureParent 737 = true := by decide +kernel

theorem tail_enclosure_row_738 : checkTailEnclosureParent 738 = true := by decide +kernel

theorem tail_enclosure_row_739 : checkTailEnclosureParent 739 = true := by decide +kernel

theorem tail_enclosure_row_740 : checkTailEnclosureParent 740 = true := by decide +kernel

theorem tail_enclosure_row_741 : checkTailEnclosureParent 741 = true := by decide +kernel

theorem tail_enclosure_row_742 : checkTailEnclosureParent 742 = true := by decide +kernel

theorem tail_enclosure_row_743 : checkTailEnclosureParent 743 = true := by decide +kernel

theorem tail_enclosure_row_744 : checkTailEnclosureParent 744 = true := by decide +kernel

theorem tail_enclosure_row_745 : checkTailEnclosureParent 745 = true := by decide +kernel

theorem tail_enclosure_row_746 : checkTailEnclosureParent 746 = true := by decide +kernel

theorem tail_enclosure_row_747 : checkTailEnclosureParent 747 = true := by decide +kernel

theorem tail_enclosure_row_748 : checkTailEnclosureParent 748 = true := by decide +kernel

theorem tail_enclosure_row_749 : checkTailEnclosureParent 749 = true := by decide +kernel

theorem tail_enclosure_row_750 : checkTailEnclosureParent 750 = true := by decide +kernel

theorem tail_enclosure_row_751 : checkTailEnclosureParent 751 = true := by decide +kernel

theorem tail_enclosure_rows_736_751 :
    (List.range' 736 16).all checkTailEnclosureParent = true := by
  change ([736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_736, tail_enclosure_row_737, tail_enclosure_row_738, tail_enclosure_row_739, tail_enclosure_row_740, tail_enclosure_row_741, tail_enclosure_row_742, tail_enclosure_row_743, tail_enclosure_row_744, tail_enclosure_row_745, tail_enclosure_row_746, tail_enclosure_row_747, tail_enclosure_row_748, tail_enclosure_row_749, tail_enclosure_row_750, tail_enclosure_row_751,Bool.and_self]

end P161Formal
