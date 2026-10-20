module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1056 : checkTailEnclosureParent 1056 = true := by decide +kernel

theorem tail_enclosure_row_1057 : checkTailEnclosureParent 1057 = true := by decide +kernel

theorem tail_enclosure_row_1058 : checkTailEnclosureParent 1058 = true := by decide +kernel

theorem tail_enclosure_row_1059 : checkTailEnclosureParent 1059 = true := by decide +kernel

theorem tail_enclosure_row_1060 : checkTailEnclosureParent 1060 = true := by decide +kernel

theorem tail_enclosure_row_1061 : checkTailEnclosureParent 1061 = true := by decide +kernel

theorem tail_enclosure_row_1062 : checkTailEnclosureParent 1062 = true := by decide +kernel

theorem tail_enclosure_row_1063 : checkTailEnclosureParent 1063 = true := by decide +kernel

theorem tail_enclosure_row_1064 : checkTailEnclosureParent 1064 = true := by decide +kernel

theorem tail_enclosure_row_1065 : checkTailEnclosureParent 1065 = true := by decide +kernel

theorem tail_enclosure_row_1066 : checkTailEnclosureParent 1066 = true := by decide +kernel

theorem tail_enclosure_row_1067 : checkTailEnclosureParent 1067 = true := by decide +kernel

theorem tail_enclosure_row_1068 : checkTailEnclosureParent 1068 = true := by decide +kernel

theorem tail_enclosure_row_1069 : checkTailEnclosureParent 1069 = true := by decide +kernel

theorem tail_enclosure_row_1070 : checkTailEnclosureParent 1070 = true := by decide +kernel

theorem tail_enclosure_row_1071 : checkTailEnclosureParent 1071 = true := by decide +kernel

theorem tail_enclosure_rows_1056_1071 :
    (List.range' 1056 16).all checkTailEnclosureParent = true := by
  change ([1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1056, tail_enclosure_row_1057, tail_enclosure_row_1058, tail_enclosure_row_1059, tail_enclosure_row_1060, tail_enclosure_row_1061, tail_enclosure_row_1062, tail_enclosure_row_1063, tail_enclosure_row_1064, tail_enclosure_row_1065, tail_enclosure_row_1066, tail_enclosure_row_1067, tail_enclosure_row_1068, tail_enclosure_row_1069, tail_enclosure_row_1070, tail_enclosure_row_1071,Bool.and_self]

end P161Formal
