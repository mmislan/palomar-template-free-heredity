module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_864 : checkTailEnclosureParent 864 = true := by decide +kernel

theorem tail_enclosure_row_865 : checkTailEnclosureParent 865 = true := by decide +kernel

theorem tail_enclosure_row_866 : checkTailEnclosureParent 866 = true := by decide +kernel

theorem tail_enclosure_row_867 : checkTailEnclosureParent 867 = true := by decide +kernel

theorem tail_enclosure_row_868 : checkTailEnclosureParent 868 = true := by decide +kernel

theorem tail_enclosure_row_869 : checkTailEnclosureParent 869 = true := by decide +kernel

theorem tail_enclosure_row_870 : checkTailEnclosureParent 870 = true := by decide +kernel

theorem tail_enclosure_row_871 : checkTailEnclosureParent 871 = true := by decide +kernel

theorem tail_enclosure_row_872 : checkTailEnclosureParent 872 = true := by decide +kernel

theorem tail_enclosure_row_873 : checkTailEnclosureParent 873 = true := by decide +kernel

theorem tail_enclosure_row_874 : checkTailEnclosureParent 874 = true := by decide +kernel

theorem tail_enclosure_row_875 : checkTailEnclosureParent 875 = true := by decide +kernel

theorem tail_enclosure_row_876 : checkTailEnclosureParent 876 = true := by decide +kernel

theorem tail_enclosure_row_877 : checkTailEnclosureParent 877 = true := by decide +kernel

theorem tail_enclosure_row_878 : checkTailEnclosureParent 878 = true := by decide +kernel

theorem tail_enclosure_row_879 : checkTailEnclosureParent 879 = true := by decide +kernel

theorem tail_enclosure_rows_864_879 :
    (List.range' 864 16).all checkTailEnclosureParent = true := by
  change ([864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_864, tail_enclosure_row_865, tail_enclosure_row_866, tail_enclosure_row_867, tail_enclosure_row_868, tail_enclosure_row_869, tail_enclosure_row_870, tail_enclosure_row_871, tail_enclosure_row_872, tail_enclosure_row_873, tail_enclosure_row_874, tail_enclosure_row_875, tail_enclosure_row_876, tail_enclosure_row_877, tail_enclosure_row_878, tail_enclosure_row_879,Bool.and_self]

end P161Formal
