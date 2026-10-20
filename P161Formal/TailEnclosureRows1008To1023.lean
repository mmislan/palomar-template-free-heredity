module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_1008 : checkTailEnclosureParent 1008 = true := by decide +kernel

theorem tail_enclosure_row_1009 : checkTailEnclosureParent 1009 = true := by decide +kernel

theorem tail_enclosure_row_1010 : checkTailEnclosureParent 1010 = true := by decide +kernel

theorem tail_enclosure_row_1011 : checkTailEnclosureParent 1011 = true := by decide +kernel

theorem tail_enclosure_row_1012 : checkTailEnclosureParent 1012 = true := by decide +kernel

theorem tail_enclosure_row_1013 : checkTailEnclosureParent 1013 = true := by decide +kernel

theorem tail_enclosure_row_1014 : checkTailEnclosureParent 1014 = true := by decide +kernel

theorem tail_enclosure_row_1015 : checkTailEnclosureParent 1015 = true := by decide +kernel

theorem tail_enclosure_row_1016 : checkTailEnclosureParent 1016 = true := by decide +kernel

theorem tail_enclosure_row_1017 : checkTailEnclosureParent 1017 = true := by decide +kernel

theorem tail_enclosure_row_1018 : checkTailEnclosureParent 1018 = true := by decide +kernel

theorem tail_enclosure_row_1019 : checkTailEnclosureParent 1019 = true := by decide +kernel

theorem tail_enclosure_row_1020 : checkTailEnclosureParent 1020 = true := by decide +kernel

theorem tail_enclosure_row_1021 : checkTailEnclosureParent 1021 = true := by decide +kernel

theorem tail_enclosure_row_1022 : checkTailEnclosureParent 1022 = true := by decide +kernel

theorem tail_enclosure_row_1023 : checkTailEnclosureParent 1023 = true := by decide +kernel

theorem tail_enclosure_rows_1008_1023 :
    (List.range' 1008 16).all checkTailEnclosureParent = true := by
  change ([1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_1008, tail_enclosure_row_1009, tail_enclosure_row_1010, tail_enclosure_row_1011, tail_enclosure_row_1012, tail_enclosure_row_1013, tail_enclosure_row_1014, tail_enclosure_row_1015, tail_enclosure_row_1016, tail_enclosure_row_1017, tail_enclosure_row_1018, tail_enclosure_row_1019, tail_enclosure_row_1020, tail_enclosure_row_1021, tail_enclosure_row_1022, tail_enclosure_row_1023,Bool.and_self]

end P161Formal
