module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_944 : checkTailEnclosureParent 944 = true := by decide +kernel

theorem tail_enclosure_row_945 : checkTailEnclosureParent 945 = true := by decide +kernel

theorem tail_enclosure_row_946 : checkTailEnclosureParent 946 = true := by decide +kernel

theorem tail_enclosure_row_947 : checkTailEnclosureParent 947 = true := by decide +kernel

theorem tail_enclosure_row_948 : checkTailEnclosureParent 948 = true := by decide +kernel

theorem tail_enclosure_row_949 : checkTailEnclosureParent 949 = true := by decide +kernel

theorem tail_enclosure_row_950 : checkTailEnclosureParent 950 = true := by decide +kernel

theorem tail_enclosure_row_951 : checkTailEnclosureParent 951 = true := by decide +kernel

theorem tail_enclosure_row_952 : checkTailEnclosureParent 952 = true := by decide +kernel

theorem tail_enclosure_row_953 : checkTailEnclosureParent 953 = true := by decide +kernel

theorem tail_enclosure_row_954 : checkTailEnclosureParent 954 = true := by decide +kernel

theorem tail_enclosure_row_955 : checkTailEnclosureParent 955 = true := by decide +kernel

theorem tail_enclosure_row_956 : checkTailEnclosureParent 956 = true := by decide +kernel

theorem tail_enclosure_row_957 : checkTailEnclosureParent 957 = true := by decide +kernel

theorem tail_enclosure_row_958 : checkTailEnclosureParent 958 = true := by decide +kernel

theorem tail_enclosure_row_959 : checkTailEnclosureParent 959 = true := by decide +kernel

theorem tail_enclosure_rows_944_959 :
    (List.range' 944 16).all checkTailEnclosureParent = true := by
  change ([944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_944, tail_enclosure_row_945, tail_enclosure_row_946, tail_enclosure_row_947, tail_enclosure_row_948, tail_enclosure_row_949, tail_enclosure_row_950, tail_enclosure_row_951, tail_enclosure_row_952, tail_enclosure_row_953, tail_enclosure_row_954, tail_enclosure_row_955, tail_enclosure_row_956, tail_enclosure_row_957, tail_enclosure_row_958, tail_enclosure_row_959,Bool.and_self]

end P161Formal
