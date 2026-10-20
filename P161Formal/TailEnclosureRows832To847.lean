module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_832 : checkTailEnclosureParent 832 = true := by decide +kernel

theorem tail_enclosure_row_833 : checkTailEnclosureParent 833 = true := by decide +kernel

theorem tail_enclosure_row_834 : checkTailEnclosureParent 834 = true := by decide +kernel

theorem tail_enclosure_row_835 : checkTailEnclosureParent 835 = true := by decide +kernel

theorem tail_enclosure_row_836 : checkTailEnclosureParent 836 = true := by decide +kernel

theorem tail_enclosure_row_837 : checkTailEnclosureParent 837 = true := by decide +kernel

theorem tail_enclosure_row_838 : checkTailEnclosureParent 838 = true := by decide +kernel

theorem tail_enclosure_row_839 : checkTailEnclosureParent 839 = true := by decide +kernel

theorem tail_enclosure_row_840 : checkTailEnclosureParent 840 = true := by decide +kernel

theorem tail_enclosure_row_841 : checkTailEnclosureParent 841 = true := by decide +kernel

theorem tail_enclosure_row_842 : checkTailEnclosureParent 842 = true := by decide +kernel

theorem tail_enclosure_row_843 : checkTailEnclosureParent 843 = true := by decide +kernel

theorem tail_enclosure_row_844 : checkTailEnclosureParent 844 = true := by decide +kernel

theorem tail_enclosure_row_845 : checkTailEnclosureParent 845 = true := by decide +kernel

theorem tail_enclosure_row_846 : checkTailEnclosureParent 846 = true := by decide +kernel

theorem tail_enclosure_row_847 : checkTailEnclosureParent 847 = true := by decide +kernel

theorem tail_enclosure_rows_832_847 :
    (List.range' 832 16).all checkTailEnclosureParent = true := by
  change ([832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_832, tail_enclosure_row_833, tail_enclosure_row_834, tail_enclosure_row_835, tail_enclosure_row_836, tail_enclosure_row_837, tail_enclosure_row_838, tail_enclosure_row_839, tail_enclosure_row_840, tail_enclosure_row_841, tail_enclosure_row_842, tail_enclosure_row_843, tail_enclosure_row_844, tail_enclosure_row_845, tail_enclosure_row_846, tail_enclosure_row_847,Bool.and_self]

end P161Formal
