module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1088 : checkTailEnclosureParent 1088 = true := by decide +kernel

theorem tail_enclosure_row_1089 : checkTailEnclosureParent 1089 = true := by decide +kernel

theorem tail_enclosure_row_1090 : checkTailEnclosureParent 1090 = true := by decide +kernel

theorem tail_enclosure_row_1091 : checkTailEnclosureParent 1091 = true := by decide +kernel

theorem tail_enclosure_row_1092 : checkTailEnclosureParent 1092 = true := by decide +kernel

theorem tail_enclosure_row_1093 : checkTailEnclosureParent 1093 = true := by decide +kernel

theorem tail_enclosure_row_1094 : checkTailEnclosureParent 1094 = true := by decide +kernel

theorem tail_enclosure_row_1095 : checkTailEnclosureParent 1095 = true := by decide +kernel

theorem tail_enclosure_row_1096 : checkTailEnclosureParent 1096 = true := by decide +kernel

theorem tail_enclosure_row_1097 : checkTailEnclosureParent 1097 = true := by decide +kernel

theorem tail_enclosure_row_1098 : checkTailEnclosureParent 1098 = true := by decide +kernel

theorem tail_enclosure_row_1099 : checkTailEnclosureParent 1099 = true := by decide +kernel

theorem tail_enclosure_row_1100 : checkTailEnclosureParent 1100 = true := by decide +kernel

theorem tail_enclosure_row_1101 : checkTailEnclosureParent 1101 = true := by decide +kernel

theorem tail_enclosure_row_1102 : checkTailEnclosureParent 1102 = true := by decide +kernel

theorem tail_enclosure_row_1103 : checkTailEnclosureParent 1103 = true := by decide +kernel

theorem tail_enclosure_rows_1088_1103 :
    (List.range' 1088 16).all checkTailEnclosureParent = true := by
  change ([1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1088, tail_enclosure_row_1089, tail_enclosure_row_1090, tail_enclosure_row_1091, tail_enclosure_row_1092, tail_enclosure_row_1093, tail_enclosure_row_1094, tail_enclosure_row_1095, tail_enclosure_row_1096, tail_enclosure_row_1097, tail_enclosure_row_1098, tail_enclosure_row_1099, tail_enclosure_row_1100, tail_enclosure_row_1101, tail_enclosure_row_1102, tail_enclosure_row_1103,Bool.and_self]

end P161Formal
