module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1120 : checkTailEnclosureParent 1120 = true := by decide +kernel

theorem tail_enclosure_row_1121 : checkTailEnclosureParent 1121 = true := by decide +kernel

theorem tail_enclosure_row_1122 : checkTailEnclosureParent 1122 = true := by decide +kernel

theorem tail_enclosure_row_1123 : checkTailEnclosureParent 1123 = true := by decide +kernel

theorem tail_enclosure_row_1124 : checkTailEnclosureParent 1124 = true := by decide +kernel

theorem tail_enclosure_row_1125 : checkTailEnclosureParent 1125 = true := by decide +kernel

theorem tail_enclosure_row_1126 : checkTailEnclosureParent 1126 = true := by decide +kernel

theorem tail_enclosure_row_1127 : checkTailEnclosureParent 1127 = true := by decide +kernel

theorem tail_enclosure_row_1128 : checkTailEnclosureParent 1128 = true := by decide +kernel

theorem tail_enclosure_row_1129 : checkTailEnclosureParent 1129 = true := by decide +kernel

theorem tail_enclosure_row_1130 : checkTailEnclosureParent 1130 = true := by decide +kernel

theorem tail_enclosure_row_1131 : checkTailEnclosureParent 1131 = true := by decide +kernel

theorem tail_enclosure_row_1132 : checkTailEnclosureParent 1132 = true := by decide +kernel

theorem tail_enclosure_row_1133 : checkTailEnclosureParent 1133 = true := by decide +kernel

theorem tail_enclosure_row_1134 : checkTailEnclosureParent 1134 = true := by decide +kernel

theorem tail_enclosure_row_1135 : checkTailEnclosureParent 1135 = true := by decide +kernel

theorem tail_enclosure_rows_1120_1135 :
    (List.range' 1120 16).all checkTailEnclosureParent = true := by
  change ([1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1120, tail_enclosure_row_1121, tail_enclosure_row_1122, tail_enclosure_row_1123, tail_enclosure_row_1124, tail_enclosure_row_1125, tail_enclosure_row_1126, tail_enclosure_row_1127, tail_enclosure_row_1128, tail_enclosure_row_1129, tail_enclosure_row_1130, tail_enclosure_row_1131, tail_enclosure_row_1132, tail_enclosure_row_1133, tail_enclosure_row_1134, tail_enclosure_row_1135,Bool.and_self]

end P161Formal
