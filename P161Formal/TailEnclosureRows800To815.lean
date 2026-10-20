module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_800 : checkTailEnclosureParent 800 = true := by decide +kernel

theorem tail_enclosure_row_801 : checkTailEnclosureParent 801 = true := by decide +kernel

theorem tail_enclosure_row_802 : checkTailEnclosureParent 802 = true := by decide +kernel

theorem tail_enclosure_row_803 : checkTailEnclosureParent 803 = true := by decide +kernel

theorem tail_enclosure_row_804 : checkTailEnclosureParent 804 = true := by decide +kernel

theorem tail_enclosure_row_805 : checkTailEnclosureParent 805 = true := by decide +kernel

theorem tail_enclosure_row_806 : checkTailEnclosureParent 806 = true := by decide +kernel

theorem tail_enclosure_row_807 : checkTailEnclosureParent 807 = true := by decide +kernel

theorem tail_enclosure_row_808 : checkTailEnclosureParent 808 = true := by decide +kernel

theorem tail_enclosure_row_809 : checkTailEnclosureParent 809 = true := by decide +kernel

theorem tail_enclosure_row_810 : checkTailEnclosureParent 810 = true := by decide +kernel

theorem tail_enclosure_row_811 : checkTailEnclosureParent 811 = true := by decide +kernel

theorem tail_enclosure_row_812 : checkTailEnclosureParent 812 = true := by decide +kernel

theorem tail_enclosure_row_813 : checkTailEnclosureParent 813 = true := by decide +kernel

theorem tail_enclosure_row_814 : checkTailEnclosureParent 814 = true := by decide +kernel

theorem tail_enclosure_row_815 : checkTailEnclosureParent 815 = true := by decide +kernel

theorem tail_enclosure_rows_800_815 :
    (List.range' 800 16).all checkTailEnclosureParent = true := by
  change ([800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_800, tail_enclosure_row_801, tail_enclosure_row_802, tail_enclosure_row_803, tail_enclosure_row_804, tail_enclosure_row_805, tail_enclosure_row_806, tail_enclosure_row_807, tail_enclosure_row_808, tail_enclosure_row_809, tail_enclosure_row_810, tail_enclosure_row_811, tail_enclosure_row_812, tail_enclosure_row_813, tail_enclosure_row_814, tail_enclosure_row_815,Bool.and_self]

end P161Formal
