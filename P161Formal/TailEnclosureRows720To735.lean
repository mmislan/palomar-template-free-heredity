module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_720 : checkTailEnclosureParent 720 = true := by decide +kernel

theorem tail_enclosure_row_721 : checkTailEnclosureParent 721 = true := by decide +kernel

theorem tail_enclosure_row_722 : checkTailEnclosureParent 722 = true := by decide +kernel

theorem tail_enclosure_row_723 : checkTailEnclosureParent 723 = true := by decide +kernel

theorem tail_enclosure_row_724 : checkTailEnclosureParent 724 = true := by decide +kernel

theorem tail_enclosure_row_725 : checkTailEnclosureParent 725 = true := by decide +kernel

theorem tail_enclosure_row_726 : checkTailEnclosureParent 726 = true := by decide +kernel

theorem tail_enclosure_row_727 : checkTailEnclosureParent 727 = true := by decide +kernel

theorem tail_enclosure_row_728 : checkTailEnclosureParent 728 = true := by decide +kernel

theorem tail_enclosure_row_729 : checkTailEnclosureParent 729 = true := by decide +kernel

theorem tail_enclosure_row_730 : checkTailEnclosureParent 730 = true := by decide +kernel

theorem tail_enclosure_row_731 : checkTailEnclosureParent 731 = true := by decide +kernel

theorem tail_enclosure_row_732 : checkTailEnclosureParent 732 = true := by decide +kernel

theorem tail_enclosure_row_733 : checkTailEnclosureParent 733 = true := by decide +kernel

theorem tail_enclosure_row_734 : checkTailEnclosureParent 734 = true := by decide +kernel

theorem tail_enclosure_row_735 : checkTailEnclosureParent 735 = true := by decide +kernel

theorem tail_enclosure_rows_720_735 :
    (List.range' 720 16).all checkTailEnclosureParent = true := by
  change ([720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_720, tail_enclosure_row_721, tail_enclosure_row_722, tail_enclosure_row_723, tail_enclosure_row_724, tail_enclosure_row_725, tail_enclosure_row_726, tail_enclosure_row_727, tail_enclosure_row_728, tail_enclosure_row_729, tail_enclosure_row_730, tail_enclosure_row_731, tail_enclosure_row_732, tail_enclosure_row_733, tail_enclosure_row_734, tail_enclosure_row_735,Bool.and_self]

end P161Formal
