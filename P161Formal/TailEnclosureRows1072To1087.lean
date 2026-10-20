module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1072 : checkTailEnclosureParent 1072 = true := by decide +kernel

theorem tail_enclosure_row_1073 : checkTailEnclosureParent 1073 = true := by decide +kernel

theorem tail_enclosure_row_1074 : checkTailEnclosureParent 1074 = true := by decide +kernel

theorem tail_enclosure_row_1075 : checkTailEnclosureParent 1075 = true := by decide +kernel

theorem tail_enclosure_row_1076 : checkTailEnclosureParent 1076 = true := by decide +kernel

theorem tail_enclosure_row_1077 : checkTailEnclosureParent 1077 = true := by decide +kernel

theorem tail_enclosure_row_1078 : checkTailEnclosureParent 1078 = true := by decide +kernel

theorem tail_enclosure_row_1079 : checkTailEnclosureParent 1079 = true := by decide +kernel

theorem tail_enclosure_row_1080 : checkTailEnclosureParent 1080 = true := by decide +kernel

theorem tail_enclosure_row_1081 : checkTailEnclosureParent 1081 = true := by decide +kernel

theorem tail_enclosure_row_1082 : checkTailEnclosureParent 1082 = true := by decide +kernel

theorem tail_enclosure_row_1083 : checkTailEnclosureParent 1083 = true := by decide +kernel

theorem tail_enclosure_row_1084 : checkTailEnclosureParent 1084 = true := by decide +kernel

theorem tail_enclosure_row_1085 : checkTailEnclosureParent 1085 = true := by decide +kernel

theorem tail_enclosure_row_1086 : checkTailEnclosureParent 1086 = true := by decide +kernel

theorem tail_enclosure_row_1087 : checkTailEnclosureParent 1087 = true := by decide +kernel

theorem tail_enclosure_rows_1072_1087 :
    (List.range' 1072 16).all checkTailEnclosureParent = true := by
  change ([1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1072, tail_enclosure_row_1073, tail_enclosure_row_1074, tail_enclosure_row_1075, tail_enclosure_row_1076, tail_enclosure_row_1077, tail_enclosure_row_1078, tail_enclosure_row_1079, tail_enclosure_row_1080, tail_enclosure_row_1081, tail_enclosure_row_1082, tail_enclosure_row_1083, tail_enclosure_row_1084, tail_enclosure_row_1085, tail_enclosure_row_1086, tail_enclosure_row_1087,Bool.and_self]

end P161Formal
