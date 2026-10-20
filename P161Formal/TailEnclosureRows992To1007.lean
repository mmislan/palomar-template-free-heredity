module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_992 : checkTailEnclosureParent 992 = true := by decide +kernel

theorem tail_enclosure_row_993 : checkTailEnclosureParent 993 = true := by decide +kernel

theorem tail_enclosure_row_994 : checkTailEnclosureParent 994 = true := by decide +kernel

theorem tail_enclosure_row_995 : checkTailEnclosureParent 995 = true := by decide +kernel

theorem tail_enclosure_row_996 : checkTailEnclosureParent 996 = true := by decide +kernel

theorem tail_enclosure_row_997 : checkTailEnclosureParent 997 = true := by decide +kernel

theorem tail_enclosure_row_998 : checkTailEnclosureParent 998 = true := by decide +kernel

theorem tail_enclosure_row_999 : checkTailEnclosureParent 999 = true := by decide +kernel

theorem tail_enclosure_row_1000 : checkTailEnclosureParent 1000 = true := by decide +kernel

theorem tail_enclosure_row_1001 : checkTailEnclosureParent 1001 = true := by decide +kernel

theorem tail_enclosure_row_1002 : checkTailEnclosureParent 1002 = true := by decide +kernel

theorem tail_enclosure_row_1003 : checkTailEnclosureParent 1003 = true := by decide +kernel

theorem tail_enclosure_row_1004 : checkTailEnclosureParent 1004 = true := by decide +kernel

theorem tail_enclosure_row_1005 : checkTailEnclosureParent 1005 = true := by decide +kernel

theorem tail_enclosure_row_1006 : checkTailEnclosureParent 1006 = true := by decide +kernel

theorem tail_enclosure_row_1007 : checkTailEnclosureParent 1007 = true := by decide +kernel

theorem tail_enclosure_rows_992_1007 :
    (List.range' 992 16).all checkTailEnclosureParent = true := by
  change ([992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_992, tail_enclosure_row_993, tail_enclosure_row_994, tail_enclosure_row_995, tail_enclosure_row_996, tail_enclosure_row_997, tail_enclosure_row_998, tail_enclosure_row_999, tail_enclosure_row_1000, tail_enclosure_row_1001, tail_enclosure_row_1002, tail_enclosure_row_1003, tail_enclosure_row_1004, tail_enclosure_row_1005, tail_enclosure_row_1006, tail_enclosure_row_1007,Bool.and_self]

end P161Formal
