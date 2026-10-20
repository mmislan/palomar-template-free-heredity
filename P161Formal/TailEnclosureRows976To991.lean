module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_976 : checkTailEnclosureParent 976 = true := by decide +kernel

theorem tail_enclosure_row_977 : checkTailEnclosureParent 977 = true := by decide +kernel

theorem tail_enclosure_row_978 : checkTailEnclosureParent 978 = true := by decide +kernel

theorem tail_enclosure_row_979 : checkTailEnclosureParent 979 = true := by decide +kernel

theorem tail_enclosure_row_980 : checkTailEnclosureParent 980 = true := by decide +kernel

theorem tail_enclosure_row_981 : checkTailEnclosureParent 981 = true := by decide +kernel

theorem tail_enclosure_row_982 : checkTailEnclosureParent 982 = true := by decide +kernel

theorem tail_enclosure_row_983 : checkTailEnclosureParent 983 = true := by decide +kernel

theorem tail_enclosure_row_984 : checkTailEnclosureParent 984 = true := by decide +kernel

theorem tail_enclosure_row_985 : checkTailEnclosureParent 985 = true := by decide +kernel

theorem tail_enclosure_row_986 : checkTailEnclosureParent 986 = true := by decide +kernel

theorem tail_enclosure_row_987 : checkTailEnclosureParent 987 = true := by decide +kernel

theorem tail_enclosure_row_988 : checkTailEnclosureParent 988 = true := by decide +kernel

theorem tail_enclosure_row_989 : checkTailEnclosureParent 989 = true := by decide +kernel

theorem tail_enclosure_row_990 : checkTailEnclosureParent 990 = true := by decide +kernel

theorem tail_enclosure_row_991 : checkTailEnclosureParent 991 = true := by decide +kernel

theorem tail_enclosure_rows_976_991 :
    (List.range' 976 16).all checkTailEnclosureParent = true := by
  change ([976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_976, tail_enclosure_row_977, tail_enclosure_row_978, tail_enclosure_row_979, tail_enclosure_row_980, tail_enclosure_row_981, tail_enclosure_row_982, tail_enclosure_row_983, tail_enclosure_row_984, tail_enclosure_row_985, tail_enclosure_row_986, tail_enclosure_row_987, tail_enclosure_row_988, tail_enclosure_row_989, tail_enclosure_row_990, tail_enclosure_row_991,Bool.and_self]

end P161Formal
