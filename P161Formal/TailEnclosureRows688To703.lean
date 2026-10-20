module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_688 : checkTailEnclosureParent 688 = true := by decide +kernel

theorem tail_enclosure_row_689 : checkTailEnclosureParent 689 = true := by decide +kernel

theorem tail_enclosure_row_690 : checkTailEnclosureParent 690 = true := by decide +kernel

theorem tail_enclosure_row_691 : checkTailEnclosureParent 691 = true := by decide +kernel

theorem tail_enclosure_row_692 : checkTailEnclosureParent 692 = true := by decide +kernel

theorem tail_enclosure_row_693 : checkTailEnclosureParent 693 = true := by decide +kernel

theorem tail_enclosure_row_694 : checkTailEnclosureParent 694 = true := by decide +kernel

theorem tail_enclosure_row_695 : checkTailEnclosureParent 695 = true := by decide +kernel

theorem tail_enclosure_row_696 : checkTailEnclosureParent 696 = true := by decide +kernel

theorem tail_enclosure_row_697 : checkTailEnclosureParent 697 = true := by decide +kernel

theorem tail_enclosure_row_698 : checkTailEnclosureParent 698 = true := by decide +kernel

theorem tail_enclosure_row_699 : checkTailEnclosureParent 699 = true := by decide +kernel

theorem tail_enclosure_row_700 : checkTailEnclosureParent 700 = true := by decide +kernel

theorem tail_enclosure_row_701 : checkTailEnclosureParent 701 = true := by decide +kernel

theorem tail_enclosure_row_702 : checkTailEnclosureParent 702 = true := by decide +kernel

theorem tail_enclosure_row_703 : checkTailEnclosureParent 703 = true := by decide +kernel

theorem tail_enclosure_rows_688_703 :
    (List.range' 688 16).all checkTailEnclosureParent = true := by
  change ([688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_688, tail_enclosure_row_689, tail_enclosure_row_690, tail_enclosure_row_691, tail_enclosure_row_692, tail_enclosure_row_693, tail_enclosure_row_694, tail_enclosure_row_695, tail_enclosure_row_696, tail_enclosure_row_697, tail_enclosure_row_698, tail_enclosure_row_699, tail_enclosure_row_700, tail_enclosure_row_701, tail_enclosure_row_702, tail_enclosure_row_703,Bool.and_self]

end P161Formal
