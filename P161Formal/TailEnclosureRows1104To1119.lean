module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1104 : checkTailEnclosureParent 1104 = true := by decide +kernel

theorem tail_enclosure_row_1105 : checkTailEnclosureParent 1105 = true := by decide +kernel

theorem tail_enclosure_row_1106 : checkTailEnclosureParent 1106 = true := by decide +kernel

theorem tail_enclosure_row_1107 : checkTailEnclosureParent 1107 = true := by decide +kernel

theorem tail_enclosure_row_1108 : checkTailEnclosureParent 1108 = true := by decide +kernel

theorem tail_enclosure_row_1109 : checkTailEnclosureParent 1109 = true := by decide +kernel

theorem tail_enclosure_row_1110 : checkTailEnclosureParent 1110 = true := by decide +kernel

theorem tail_enclosure_row_1111 : checkTailEnclosureParent 1111 = true := by decide +kernel

theorem tail_enclosure_row_1112 : checkTailEnclosureParent 1112 = true := by decide +kernel

theorem tail_enclosure_row_1113 : checkTailEnclosureParent 1113 = true := by decide +kernel

theorem tail_enclosure_row_1114 : checkTailEnclosureParent 1114 = true := by decide +kernel

theorem tail_enclosure_row_1115 : checkTailEnclosureParent 1115 = true := by decide +kernel

theorem tail_enclosure_row_1116 : checkTailEnclosureParent 1116 = true := by decide +kernel

theorem tail_enclosure_row_1117 : checkTailEnclosureParent 1117 = true := by decide +kernel

theorem tail_enclosure_row_1118 : checkTailEnclosureParent 1118 = true := by decide +kernel

theorem tail_enclosure_row_1119 : checkTailEnclosureParent 1119 = true := by decide +kernel

theorem tail_enclosure_rows_1104_1119 :
    (List.range' 1104 16).all checkTailEnclosureParent = true := by
  change ([1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1104, tail_enclosure_row_1105, tail_enclosure_row_1106, tail_enclosure_row_1107, tail_enclosure_row_1108, tail_enclosure_row_1109, tail_enclosure_row_1110, tail_enclosure_row_1111, tail_enclosure_row_1112, tail_enclosure_row_1113, tail_enclosure_row_1114, tail_enclosure_row_1115, tail_enclosure_row_1116, tail_enclosure_row_1117, tail_enclosure_row_1118, tail_enclosure_row_1119,Bool.and_self]

end P161Formal
