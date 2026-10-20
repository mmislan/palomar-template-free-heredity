module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_960 : checkTailEnclosureParent 960 = true := by decide +kernel

theorem tail_enclosure_row_961 : checkTailEnclosureParent 961 = true := by decide +kernel

theorem tail_enclosure_row_962 : checkTailEnclosureParent 962 = true := by decide +kernel

theorem tail_enclosure_row_963 : checkTailEnclosureParent 963 = true := by decide +kernel

theorem tail_enclosure_row_964 : checkTailEnclosureParent 964 = true := by decide +kernel

theorem tail_enclosure_row_965 : checkTailEnclosureParent 965 = true := by decide +kernel

theorem tail_enclosure_row_966 : checkTailEnclosureParent 966 = true := by decide +kernel

theorem tail_enclosure_row_967 : checkTailEnclosureParent 967 = true := by decide +kernel

theorem tail_enclosure_row_968 : checkTailEnclosureParent 968 = true := by decide +kernel

theorem tail_enclosure_row_969 : checkTailEnclosureParent 969 = true := by decide +kernel

theorem tail_enclosure_row_970 : checkTailEnclosureParent 970 = true := by decide +kernel

theorem tail_enclosure_row_971 : checkTailEnclosureParent 971 = true := by decide +kernel

theorem tail_enclosure_row_972 : checkTailEnclosureParent 972 = true := by decide +kernel

theorem tail_enclosure_row_973 : checkTailEnclosureParent 973 = true := by decide +kernel

theorem tail_enclosure_row_974 : checkTailEnclosureParent 974 = true := by decide +kernel

theorem tail_enclosure_row_975 : checkTailEnclosureParent 975 = true := by decide +kernel

theorem tail_enclosure_rows_960_975 :
    (List.range' 960 16).all checkTailEnclosureParent = true := by
  change ([960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_960, tail_enclosure_row_961, tail_enclosure_row_962, tail_enclosure_row_963, tail_enclosure_row_964, tail_enclosure_row_965, tail_enclosure_row_966, tail_enclosure_row_967, tail_enclosure_row_968, tail_enclosure_row_969, tail_enclosure_row_970, tail_enclosure_row_971, tail_enclosure_row_972, tail_enclosure_row_973, tail_enclosure_row_974, tail_enclosure_row_975,Bool.and_self]

end P161Formal
