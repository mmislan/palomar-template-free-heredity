module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1040 : checkTailEnclosureParent 1040 = true := by decide +kernel

theorem tail_enclosure_row_1041 : checkTailEnclosureParent 1041 = true := by decide +kernel

theorem tail_enclosure_row_1042 : checkTailEnclosureParent 1042 = true := by decide +kernel

theorem tail_enclosure_row_1043 : checkTailEnclosureParent 1043 = true := by decide +kernel

theorem tail_enclosure_row_1044 : checkTailEnclosureParent 1044 = true := by decide +kernel

theorem tail_enclosure_row_1045 : checkTailEnclosureParent 1045 = true := by decide +kernel

theorem tail_enclosure_row_1046 : checkTailEnclosureParent 1046 = true := by decide +kernel

theorem tail_enclosure_row_1047 : checkTailEnclosureParent 1047 = true := by decide +kernel

theorem tail_enclosure_row_1048 : checkTailEnclosureParent 1048 = true := by decide +kernel

theorem tail_enclosure_row_1049 : checkTailEnclosureParent 1049 = true := by decide +kernel

theorem tail_enclosure_row_1050 : checkTailEnclosureParent 1050 = true := by decide +kernel

theorem tail_enclosure_row_1051 : checkTailEnclosureParent 1051 = true := by decide +kernel

theorem tail_enclosure_row_1052 : checkTailEnclosureParent 1052 = true := by decide +kernel

theorem tail_enclosure_row_1053 : checkTailEnclosureParent 1053 = true := by decide +kernel

theorem tail_enclosure_row_1054 : checkTailEnclosureParent 1054 = true := by decide +kernel

theorem tail_enclosure_row_1055 : checkTailEnclosureParent 1055 = true := by decide +kernel

theorem tail_enclosure_rows_1040_1055 :
    (List.range' 1040 16).all checkTailEnclosureParent = true := by
  change ([1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1040, tail_enclosure_row_1041, tail_enclosure_row_1042, tail_enclosure_row_1043, tail_enclosure_row_1044, tail_enclosure_row_1045, tail_enclosure_row_1046, tail_enclosure_row_1047, tail_enclosure_row_1048, tail_enclosure_row_1049, tail_enclosure_row_1050, tail_enclosure_row_1051, tail_enclosure_row_1052, tail_enclosure_row_1053, tail_enclosure_row_1054, tail_enclosure_row_1055,Bool.and_self]

end P161Formal
