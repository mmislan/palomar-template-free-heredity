module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1024 : checkTailEnclosureParent 1024 = true := by decide +kernel

theorem tail_enclosure_row_1025 : checkTailEnclosureParent 1025 = true := by decide +kernel

theorem tail_enclosure_row_1026 : checkTailEnclosureParent 1026 = true := by decide +kernel

theorem tail_enclosure_row_1027 : checkTailEnclosureParent 1027 = true := by decide +kernel

theorem tail_enclosure_row_1028 : checkTailEnclosureParent 1028 = true := by decide +kernel

theorem tail_enclosure_row_1029 : checkTailEnclosureParent 1029 = true := by decide +kernel

theorem tail_enclosure_row_1030 : checkTailEnclosureParent 1030 = true := by decide +kernel

theorem tail_enclosure_row_1031 : checkTailEnclosureParent 1031 = true := by decide +kernel

theorem tail_enclosure_row_1032 : checkTailEnclosureParent 1032 = true := by decide +kernel

theorem tail_enclosure_row_1033 : checkTailEnclosureParent 1033 = true := by decide +kernel

theorem tail_enclosure_row_1034 : checkTailEnclosureParent 1034 = true := by decide +kernel

theorem tail_enclosure_row_1035 : checkTailEnclosureParent 1035 = true := by decide +kernel

theorem tail_enclosure_row_1036 : checkTailEnclosureParent 1036 = true := by decide +kernel

theorem tail_enclosure_row_1037 : checkTailEnclosureParent 1037 = true := by decide +kernel

theorem tail_enclosure_row_1038 : checkTailEnclosureParent 1038 = true := by decide +kernel

theorem tail_enclosure_row_1039 : checkTailEnclosureParent 1039 = true := by decide +kernel

theorem tail_enclosure_rows_1024_1039 :
    (List.range' 1024 16).all checkTailEnclosureParent = true := by
  change ([1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1024, tail_enclosure_row_1025, tail_enclosure_row_1026, tail_enclosure_row_1027, tail_enclosure_row_1028, tail_enclosure_row_1029, tail_enclosure_row_1030, tail_enclosure_row_1031, tail_enclosure_row_1032, tail_enclosure_row_1033, tail_enclosure_row_1034, tail_enclosure_row_1035, tail_enclosure_row_1036, tail_enclosure_row_1037, tail_enclosure_row_1038, tail_enclosure_row_1039,Bool.and_self]

end P161Formal
