module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_848 : checkTailEnclosureParent 848 = true := by decide +kernel

theorem tail_enclosure_row_849 : checkTailEnclosureParent 849 = true := by decide +kernel

theorem tail_enclosure_row_850 : checkTailEnclosureParent 850 = true := by decide +kernel

theorem tail_enclosure_row_851 : checkTailEnclosureParent 851 = true := by decide +kernel

theorem tail_enclosure_row_852 : checkTailEnclosureParent 852 = true := by decide +kernel

theorem tail_enclosure_row_853 : checkTailEnclosureParent 853 = true := by decide +kernel

theorem tail_enclosure_row_854 : checkTailEnclosureParent 854 = true := by decide +kernel

theorem tail_enclosure_row_855 : checkTailEnclosureParent 855 = true := by decide +kernel

theorem tail_enclosure_row_856 : checkTailEnclosureParent 856 = true := by decide +kernel

theorem tail_enclosure_row_857 : checkTailEnclosureParent 857 = true := by decide +kernel

theorem tail_enclosure_row_858 : checkTailEnclosureParent 858 = true := by decide +kernel

theorem tail_enclosure_row_859 : checkTailEnclosureParent 859 = true := by decide +kernel

theorem tail_enclosure_row_860 : checkTailEnclosureParent 860 = true := by decide +kernel

theorem tail_enclosure_row_861 : checkTailEnclosureParent 861 = true := by decide +kernel

theorem tail_enclosure_row_862 : checkTailEnclosureParent 862 = true := by decide +kernel

theorem tail_enclosure_row_863 : checkTailEnclosureParent 863 = true := by decide +kernel

theorem tail_enclosure_rows_848_863 :
    (List.range' 848 16).all checkTailEnclosureParent = true := by
  change ([848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_848, tail_enclosure_row_849, tail_enclosure_row_850, tail_enclosure_row_851, tail_enclosure_row_852, tail_enclosure_row_853, tail_enclosure_row_854, tail_enclosure_row_855, tail_enclosure_row_856, tail_enclosure_row_857, tail_enclosure_row_858, tail_enclosure_row_859, tail_enclosure_row_860, tail_enclosure_row_861, tail_enclosure_row_862, tail_enclosure_row_863,Bool.and_self]

end P161Formal
