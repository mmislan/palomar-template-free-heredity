module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_704 : checkTailEnclosureParent 704 = true := by decide +kernel

theorem tail_enclosure_row_705 : checkTailEnclosureParent 705 = true := by decide +kernel

theorem tail_enclosure_row_706 : checkTailEnclosureParent 706 = true := by decide +kernel

theorem tail_enclosure_row_707 : checkTailEnclosureParent 707 = true := by decide +kernel

theorem tail_enclosure_row_708 : checkTailEnclosureParent 708 = true := by decide +kernel

theorem tail_enclosure_row_709 : checkTailEnclosureParent 709 = true := by decide +kernel

theorem tail_enclosure_row_710 : checkTailEnclosureParent 710 = true := by decide +kernel

theorem tail_enclosure_row_711 : checkTailEnclosureParent 711 = true := by decide +kernel

theorem tail_enclosure_row_712 : checkTailEnclosureParent 712 = true := by decide +kernel

theorem tail_enclosure_row_713 : checkTailEnclosureParent 713 = true := by decide +kernel

theorem tail_enclosure_row_714 : checkTailEnclosureParent 714 = true := by decide +kernel

theorem tail_enclosure_row_715 : checkTailEnclosureParent 715 = true := by decide +kernel

theorem tail_enclosure_row_716 : checkTailEnclosureParent 716 = true := by decide +kernel

theorem tail_enclosure_row_717 : checkTailEnclosureParent 717 = true := by decide +kernel

theorem tail_enclosure_row_718 : checkTailEnclosureParent 718 = true := by decide +kernel

theorem tail_enclosure_row_719 : checkTailEnclosureParent 719 = true := by decide +kernel

theorem tail_enclosure_rows_704_719 :
    (List.range' 704 16).all checkTailEnclosureParent = true := by
  change ([704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_704, tail_enclosure_row_705, tail_enclosure_row_706, tail_enclosure_row_707, tail_enclosure_row_708, tail_enclosure_row_709, tail_enclosure_row_710, tail_enclosure_row_711, tail_enclosure_row_712, tail_enclosure_row_713, tail_enclosure_row_714, tail_enclosure_row_715, tail_enclosure_row_716, tail_enclosure_row_717, tail_enclosure_row_718, tail_enclosure_row_719,Bool.and_self]

end P161Formal
