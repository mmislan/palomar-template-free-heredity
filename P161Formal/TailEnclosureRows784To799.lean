module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_784 : checkTailEnclosureParent 784 = true := by decide +kernel

theorem tail_enclosure_row_785 : checkTailEnclosureParent 785 = true := by decide +kernel

theorem tail_enclosure_row_786 : checkTailEnclosureParent 786 = true := by decide +kernel

theorem tail_enclosure_row_787 : checkTailEnclosureParent 787 = true := by decide +kernel

theorem tail_enclosure_row_788 : checkTailEnclosureParent 788 = true := by decide +kernel

theorem tail_enclosure_row_789 : checkTailEnclosureParent 789 = true := by decide +kernel

theorem tail_enclosure_row_790 : checkTailEnclosureParent 790 = true := by decide +kernel

theorem tail_enclosure_row_791 : checkTailEnclosureParent 791 = true := by decide +kernel

theorem tail_enclosure_row_792 : checkTailEnclosureParent 792 = true := by decide +kernel

theorem tail_enclosure_row_793 : checkTailEnclosureParent 793 = true := by decide +kernel

theorem tail_enclosure_row_794 : checkTailEnclosureParent 794 = true := by decide +kernel

theorem tail_enclosure_row_795 : checkTailEnclosureParent 795 = true := by decide +kernel

theorem tail_enclosure_row_796 : checkTailEnclosureParent 796 = true := by decide +kernel

theorem tail_enclosure_row_797 : checkTailEnclosureParent 797 = true := by decide +kernel

theorem tail_enclosure_row_798 : checkTailEnclosureParent 798 = true := by decide +kernel

theorem tail_enclosure_row_799 : checkTailEnclosureParent 799 = true := by decide +kernel

theorem tail_enclosure_rows_784_799 :
    (List.range' 784 16).all checkTailEnclosureParent = true := by
  change ([784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_784, tail_enclosure_row_785, tail_enclosure_row_786, tail_enclosure_row_787, tail_enclosure_row_788, tail_enclosure_row_789, tail_enclosure_row_790, tail_enclosure_row_791, tail_enclosure_row_792, tail_enclosure_row_793, tail_enclosure_row_794, tail_enclosure_row_795, tail_enclosure_row_796, tail_enclosure_row_797, tail_enclosure_row_798, tail_enclosure_row_799,Bool.and_self]

end P161Formal
