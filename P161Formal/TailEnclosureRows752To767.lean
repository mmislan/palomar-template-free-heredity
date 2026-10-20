module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_752 : checkTailEnclosureParent 752 = true := by decide +kernel

theorem tail_enclosure_row_753 : checkTailEnclosureParent 753 = true := by decide +kernel

theorem tail_enclosure_row_754 : checkTailEnclosureParent 754 = true := by decide +kernel

theorem tail_enclosure_row_755 : checkTailEnclosureParent 755 = true := by decide +kernel

theorem tail_enclosure_row_756 : checkTailEnclosureParent 756 = true := by decide +kernel

theorem tail_enclosure_row_757 : checkTailEnclosureParent 757 = true := by decide +kernel

theorem tail_enclosure_row_758 : checkTailEnclosureParent 758 = true := by decide +kernel

theorem tail_enclosure_row_759 : checkTailEnclosureParent 759 = true := by decide +kernel

theorem tail_enclosure_row_760 : checkTailEnclosureParent 760 = true := by decide +kernel

theorem tail_enclosure_row_761 : checkTailEnclosureParent 761 = true := by decide +kernel

theorem tail_enclosure_row_762 : checkTailEnclosureParent 762 = true := by decide +kernel

theorem tail_enclosure_row_763 : checkTailEnclosureParent 763 = true := by decide +kernel

theorem tail_enclosure_row_764 : checkTailEnclosureParent 764 = true := by decide +kernel

theorem tail_enclosure_row_765 : checkTailEnclosureParent 765 = true := by decide +kernel

theorem tail_enclosure_row_766 : checkTailEnclosureParent 766 = true := by decide +kernel

theorem tail_enclosure_row_767 : checkTailEnclosureParent 767 = true := by decide +kernel

theorem tail_enclosure_rows_752_767 :
    (List.range' 752 16).all checkTailEnclosureParent = true := by
  change ([752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_752, tail_enclosure_row_753, tail_enclosure_row_754, tail_enclosure_row_755, tail_enclosure_row_756, tail_enclosure_row_757, tail_enclosure_row_758, tail_enclosure_row_759, tail_enclosure_row_760, tail_enclosure_row_761, tail_enclosure_row_762, tail_enclosure_row_763, tail_enclosure_row_764, tail_enclosure_row_765, tail_enclosure_row_766, tail_enclosure_row_767,Bool.and_self]

end P161Formal
