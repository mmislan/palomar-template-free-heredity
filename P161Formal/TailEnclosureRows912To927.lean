module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_912 : checkTailEnclosureParent 912 = true := by decide +kernel

theorem tail_enclosure_row_913 : checkTailEnclosureParent 913 = true := by decide +kernel

theorem tail_enclosure_row_914 : checkTailEnclosureParent 914 = true := by decide +kernel

theorem tail_enclosure_row_915 : checkTailEnclosureParent 915 = true := by decide +kernel

theorem tail_enclosure_row_916 : checkTailEnclosureParent 916 = true := by decide +kernel

theorem tail_enclosure_row_917 : checkTailEnclosureParent 917 = true := by decide +kernel

theorem tail_enclosure_row_918 : checkTailEnclosureParent 918 = true := by decide +kernel

theorem tail_enclosure_row_919 : checkTailEnclosureParent 919 = true := by decide +kernel

theorem tail_enclosure_row_920 : checkTailEnclosureParent 920 = true := by decide +kernel

theorem tail_enclosure_row_921 : checkTailEnclosureParent 921 = true := by decide +kernel

theorem tail_enclosure_row_922 : checkTailEnclosureParent 922 = true := by decide +kernel

theorem tail_enclosure_row_923 : checkTailEnclosureParent 923 = true := by decide +kernel

theorem tail_enclosure_row_924 : checkTailEnclosureParent 924 = true := by decide +kernel

theorem tail_enclosure_row_925 : checkTailEnclosureParent 925 = true := by decide +kernel

theorem tail_enclosure_row_926 : checkTailEnclosureParent 926 = true := by decide +kernel

theorem tail_enclosure_row_927 : checkTailEnclosureParent 927 = true := by decide +kernel

theorem tail_enclosure_rows_912_927 :
    (List.range' 912 16).all checkTailEnclosureParent = true := by
  change ([912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_912, tail_enclosure_row_913, tail_enclosure_row_914, tail_enclosure_row_915, tail_enclosure_row_916, tail_enclosure_row_917, tail_enclosure_row_918, tail_enclosure_row_919, tail_enclosure_row_920, tail_enclosure_row_921, tail_enclosure_row_922, tail_enclosure_row_923, tail_enclosure_row_924, tail_enclosure_row_925, tail_enclosure_row_926, tail_enclosure_row_927,Bool.and_self]

end P161Formal
