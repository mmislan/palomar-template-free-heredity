module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_896 : checkTailEnclosureParent 896 = true := by decide +kernel

theorem tail_enclosure_row_897 : checkTailEnclosureParent 897 = true := by decide +kernel

theorem tail_enclosure_row_898 : checkTailEnclosureParent 898 = true := by decide +kernel

theorem tail_enclosure_row_899 : checkTailEnclosureParent 899 = true := by decide +kernel

theorem tail_enclosure_row_900 : checkTailEnclosureParent 900 = true := by decide +kernel

theorem tail_enclosure_row_901 : checkTailEnclosureParent 901 = true := by decide +kernel

theorem tail_enclosure_row_902 : checkTailEnclosureParent 902 = true := by decide +kernel

theorem tail_enclosure_row_903 : checkTailEnclosureParent 903 = true := by decide +kernel

theorem tail_enclosure_row_904 : checkTailEnclosureParent 904 = true := by decide +kernel

theorem tail_enclosure_row_905 : checkTailEnclosureParent 905 = true := by decide +kernel

theorem tail_enclosure_row_906 : checkTailEnclosureParent 906 = true := by decide +kernel

theorem tail_enclosure_row_907 : checkTailEnclosureParent 907 = true := by decide +kernel

theorem tail_enclosure_row_908 : checkTailEnclosureParent 908 = true := by decide +kernel

theorem tail_enclosure_row_909 : checkTailEnclosureParent 909 = true := by decide +kernel

theorem tail_enclosure_row_910 : checkTailEnclosureParent 910 = true := by decide +kernel

theorem tail_enclosure_row_911 : checkTailEnclosureParent 911 = true := by decide +kernel

theorem tail_enclosure_rows_896_911 :
    (List.range' 896 16).all checkTailEnclosureParent = true := by
  change ([896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_896, tail_enclosure_row_897, tail_enclosure_row_898, tail_enclosure_row_899, tail_enclosure_row_900, tail_enclosure_row_901, tail_enclosure_row_902, tail_enclosure_row_903, tail_enclosure_row_904, tail_enclosure_row_905, tail_enclosure_row_906, tail_enclosure_row_907, tail_enclosure_row_908, tail_enclosure_row_909, tail_enclosure_row_910, tail_enclosure_row_911,Bool.and_self]

end P161Formal
