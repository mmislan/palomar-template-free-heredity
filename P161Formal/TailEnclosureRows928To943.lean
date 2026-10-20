module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_928 : checkTailEnclosureParent 928 = true := by decide +kernel

theorem tail_enclosure_row_929 : checkTailEnclosureParent 929 = true := by decide +kernel

theorem tail_enclosure_row_930 : checkTailEnclosureParent 930 = true := by decide +kernel

theorem tail_enclosure_row_931 : checkTailEnclosureParent 931 = true := by decide +kernel

theorem tail_enclosure_row_932 : checkTailEnclosureParent 932 = true := by decide +kernel

theorem tail_enclosure_row_933 : checkTailEnclosureParent 933 = true := by decide +kernel

theorem tail_enclosure_row_934 : checkTailEnclosureParent 934 = true := by decide +kernel

theorem tail_enclosure_row_935 : checkTailEnclosureParent 935 = true := by decide +kernel

theorem tail_enclosure_row_936 : checkTailEnclosureParent 936 = true := by decide +kernel

theorem tail_enclosure_row_937 : checkTailEnclosureParent 937 = true := by decide +kernel

theorem tail_enclosure_row_938 : checkTailEnclosureParent 938 = true := by decide +kernel

theorem tail_enclosure_row_939 : checkTailEnclosureParent 939 = true := by decide +kernel

theorem tail_enclosure_row_940 : checkTailEnclosureParent 940 = true := by decide +kernel

theorem tail_enclosure_row_941 : checkTailEnclosureParent 941 = true := by decide +kernel

theorem tail_enclosure_row_942 : checkTailEnclosureParent 942 = true := by decide +kernel

theorem tail_enclosure_row_943 : checkTailEnclosureParent 943 = true := by decide +kernel

theorem tail_enclosure_rows_928_943 :
    (List.range' 928 16).all checkTailEnclosureParent = true := by
  change ([928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_928, tail_enclosure_row_929, tail_enclosure_row_930, tail_enclosure_row_931, tail_enclosure_row_932, tail_enclosure_row_933, tail_enclosure_row_934, tail_enclosure_row_935, tail_enclosure_row_936, tail_enclosure_row_937, tail_enclosure_row_938, tail_enclosure_row_939, tail_enclosure_row_940, tail_enclosure_row_941, tail_enclosure_row_942, tail_enclosure_row_943,Bool.and_self]

end P161Formal
