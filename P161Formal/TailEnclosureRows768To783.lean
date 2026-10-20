module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_768 : checkTailEnclosureParent 768 = true := by decide +kernel

theorem tail_enclosure_row_769 : checkTailEnclosureParent 769 = true := by decide +kernel

theorem tail_enclosure_row_770 : checkTailEnclosureParent 770 = true := by decide +kernel

theorem tail_enclosure_row_771 : checkTailEnclosureParent 771 = true := by decide +kernel

theorem tail_enclosure_row_772 : checkTailEnclosureParent 772 = true := by decide +kernel

theorem tail_enclosure_row_773 : checkTailEnclosureParent 773 = true := by decide +kernel

theorem tail_enclosure_row_774 : checkTailEnclosureParent 774 = true := by decide +kernel

theorem tail_enclosure_row_775 : checkTailEnclosureParent 775 = true := by decide +kernel

theorem tail_enclosure_row_776 : checkTailEnclosureParent 776 = true := by decide +kernel

theorem tail_enclosure_row_777 : checkTailEnclosureParent 777 = true := by decide +kernel

theorem tail_enclosure_row_778 : checkTailEnclosureParent 778 = true := by decide +kernel

theorem tail_enclosure_row_779 : checkTailEnclosureParent 779 = true := by decide +kernel

theorem tail_enclosure_row_780 : checkTailEnclosureParent 780 = true := by decide +kernel

theorem tail_enclosure_row_781 : checkTailEnclosureParent 781 = true := by decide +kernel

theorem tail_enclosure_row_782 : checkTailEnclosureParent 782 = true := by decide +kernel

theorem tail_enclosure_row_783 : checkTailEnclosureParent 783 = true := by decide +kernel

theorem tail_enclosure_rows_768_783 :
    (List.range' 768 16).all checkTailEnclosureParent = true := by
  change ([768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_768, tail_enclosure_row_769, tail_enclosure_row_770, tail_enclosure_row_771, tail_enclosure_row_772, tail_enclosure_row_773, tail_enclosure_row_774, tail_enclosure_row_775, tail_enclosure_row_776, tail_enclosure_row_777, tail_enclosure_row_778, tail_enclosure_row_779, tail_enclosure_row_780, tail_enclosure_row_781, tail_enclosure_row_782, tail_enclosure_row_783,Bool.and_self]

end P161Formal
