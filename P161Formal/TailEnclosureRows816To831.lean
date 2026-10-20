module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_816 : checkTailEnclosureParent 816 = true := by decide +kernel

theorem tail_enclosure_row_817 : checkTailEnclosureParent 817 = true := by decide +kernel

theorem tail_enclosure_row_818 : checkTailEnclosureParent 818 = true := by decide +kernel

theorem tail_enclosure_row_819 : checkTailEnclosureParent 819 = true := by decide +kernel

theorem tail_enclosure_row_820 : checkTailEnclosureParent 820 = true := by decide +kernel

theorem tail_enclosure_row_821 : checkTailEnclosureParent 821 = true := by decide +kernel

theorem tail_enclosure_row_822 : checkTailEnclosureParent 822 = true := by decide +kernel

theorem tail_enclosure_row_823 : checkTailEnclosureParent 823 = true := by decide +kernel

theorem tail_enclosure_row_824 : checkTailEnclosureParent 824 = true := by decide +kernel

theorem tail_enclosure_row_825 : checkTailEnclosureParent 825 = true := by decide +kernel

theorem tail_enclosure_row_826 : checkTailEnclosureParent 826 = true := by decide +kernel

theorem tail_enclosure_row_827 : checkTailEnclosureParent 827 = true := by decide +kernel

theorem tail_enclosure_row_828 : checkTailEnclosureParent 828 = true := by decide +kernel

theorem tail_enclosure_row_829 : checkTailEnclosureParent 829 = true := by decide +kernel

theorem tail_enclosure_row_830 : checkTailEnclosureParent 830 = true := by decide +kernel

theorem tail_enclosure_row_831 : checkTailEnclosureParent 831 = true := by decide +kernel

theorem tail_enclosure_rows_816_831 :
    (List.range' 816 16).all checkTailEnclosureParent = true := by
  change ([816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_816, tail_enclosure_row_817, tail_enclosure_row_818, tail_enclosure_row_819, tail_enclosure_row_820, tail_enclosure_row_821, tail_enclosure_row_822, tail_enclosure_row_823, tail_enclosure_row_824, tail_enclosure_row_825, tail_enclosure_row_826, tail_enclosure_row_827, tail_enclosure_row_828, tail_enclosure_row_829, tail_enclosure_row_830, tail_enclosure_row_831,Bool.and_self]

end P161Formal
