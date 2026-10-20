module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1152 : checkTailEnclosureParent 1152 = true := by decide +kernel

theorem tail_enclosure_row_1153 : checkTailEnclosureParent 1153 = true := by decide +kernel

theorem tail_enclosure_row_1154 : checkTailEnclosureParent 1154 = true := by decide +kernel

theorem tail_enclosure_row_1155 : checkTailEnclosureParent 1155 = true := by decide +kernel

theorem tail_enclosure_row_1156 : checkTailEnclosureParent 1156 = true := by decide +kernel

theorem tail_enclosure_row_1157 : checkTailEnclosureParent 1157 = true := by decide +kernel

theorem tail_enclosure_row_1158 : checkTailEnclosureParent 1158 = true := by decide +kernel

theorem tail_enclosure_row_1159 : checkTailEnclosureParent 1159 = true := by decide +kernel

theorem tail_enclosure_row_1160 : checkTailEnclosureParent 1160 = true := by decide +kernel

theorem tail_enclosure_row_1161 : checkTailEnclosureParent 1161 = true := by decide +kernel

theorem tail_enclosure_row_1162 : checkTailEnclosureParent 1162 = true := by decide +kernel

theorem tail_enclosure_row_1163 : checkTailEnclosureParent 1163 = true := by decide +kernel

theorem tail_enclosure_row_1164 : checkTailEnclosureParent 1164 = true := by decide +kernel

theorem tail_enclosure_row_1165 : checkTailEnclosureParent 1165 = true := by decide +kernel

theorem tail_enclosure_rows_1152_1165 :
    (List.range' 1152 14).all checkTailEnclosureParent = true := by
  change ([1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1152, tail_enclosure_row_1153, tail_enclosure_row_1154, tail_enclosure_row_1155, tail_enclosure_row_1156, tail_enclosure_row_1157, tail_enclosure_row_1158, tail_enclosure_row_1159, tail_enclosure_row_1160, tail_enclosure_row_1161, tail_enclosure_row_1162, tail_enclosure_row_1163, tail_enclosure_row_1164, tail_enclosure_row_1165,Bool.and_self]

end P161Formal
