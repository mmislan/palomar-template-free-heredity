module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_656 : checkTailEnclosureParent 656 = true := by decide +kernel

theorem tail_enclosure_row_657 : checkTailEnclosureParent 657 = true := by decide +kernel

theorem tail_enclosure_row_658 : checkTailEnclosureParent 658 = true := by decide +kernel

theorem tail_enclosure_row_659 : checkTailEnclosureParent 659 = true := by decide +kernel

theorem tail_enclosure_row_660 : checkTailEnclosureParent 660 = true := by decide +kernel

theorem tail_enclosure_row_661 : checkTailEnclosureParent 661 = true := by decide +kernel

theorem tail_enclosure_row_662 : checkTailEnclosureParent 662 = true := by decide +kernel

theorem tail_enclosure_row_663 : checkTailEnclosureParent 663 = true := by decide +kernel

theorem tail_enclosure_row_664 : checkTailEnclosureParent 664 = true := by decide +kernel

theorem tail_enclosure_row_665 : checkTailEnclosureParent 665 = true := by decide +kernel

theorem tail_enclosure_row_666 : checkTailEnclosureParent 666 = true := by decide +kernel

theorem tail_enclosure_row_667 : checkTailEnclosureParent 667 = true := by decide +kernel

theorem tail_enclosure_row_668 : checkTailEnclosureParent 668 = true := by decide +kernel

theorem tail_enclosure_row_669 : checkTailEnclosureParent 669 = true := by decide +kernel

theorem tail_enclosure_row_670 : checkTailEnclosureParent 670 = true := by decide +kernel

theorem tail_enclosure_row_671 : checkTailEnclosureParent 671 = true := by decide +kernel

theorem tail_enclosure_rows_656_671 :
    (List.range' 656 16).all checkTailEnclosureParent = true := by
  change ([656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_656, tail_enclosure_row_657, tail_enclosure_row_658, tail_enclosure_row_659, tail_enclosure_row_660, tail_enclosure_row_661, tail_enclosure_row_662, tail_enclosure_row_663, tail_enclosure_row_664, tail_enclosure_row_665, tail_enclosure_row_666, tail_enclosure_row_667, tail_enclosure_row_668, tail_enclosure_row_669, tail_enclosure_row_670, tail_enclosure_row_671,Bool.and_self]

end P161Formal
