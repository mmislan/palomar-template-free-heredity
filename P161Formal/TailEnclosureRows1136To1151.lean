module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1136 : checkTailEnclosureParent 1136 = true := by decide +kernel

theorem tail_enclosure_row_1137 : checkTailEnclosureParent 1137 = true := by decide +kernel

theorem tail_enclosure_row_1138 : checkTailEnclosureParent 1138 = true := by decide +kernel

theorem tail_enclosure_row_1139 : checkTailEnclosureParent 1139 = true := by decide +kernel

theorem tail_enclosure_row_1140 : checkTailEnclosureParent 1140 = true := by decide +kernel

theorem tail_enclosure_row_1141 : checkTailEnclosureParent 1141 = true := by decide +kernel

theorem tail_enclosure_row_1142 : checkTailEnclosureParent 1142 = true := by decide +kernel

theorem tail_enclosure_row_1143 : checkTailEnclosureParent 1143 = true := by decide +kernel

theorem tail_enclosure_row_1144 : checkTailEnclosureParent 1144 = true := by decide +kernel

theorem tail_enclosure_row_1145 : checkTailEnclosureParent 1145 = true := by decide +kernel

theorem tail_enclosure_row_1146 : checkTailEnclosureParent 1146 = true := by decide +kernel

theorem tail_enclosure_row_1147 : checkTailEnclosureParent 1147 = true := by decide +kernel

theorem tail_enclosure_row_1148 : checkTailEnclosureParent 1148 = true := by decide +kernel

theorem tail_enclosure_row_1149 : checkTailEnclosureParent 1149 = true := by decide +kernel

theorem tail_enclosure_row_1150 : checkTailEnclosureParent 1150 = true := by decide +kernel

theorem tail_enclosure_row_1151 : checkTailEnclosureParent 1151 = true := by decide +kernel

theorem tail_enclosure_rows_1136_1151 :
    (List.range' 1136 16).all checkTailEnclosureParent = true := by
  change ([1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1136, tail_enclosure_row_1137, tail_enclosure_row_1138, tail_enclosure_row_1139, tail_enclosure_row_1140, tail_enclosure_row_1141, tail_enclosure_row_1142, tail_enclosure_row_1143, tail_enclosure_row_1144, tail_enclosure_row_1145, tail_enclosure_row_1146, tail_enclosure_row_1147, tail_enclosure_row_1148, tail_enclosure_row_1149, tail_enclosure_row_1150, tail_enclosure_row_1151,Bool.and_self]

end P161Formal
