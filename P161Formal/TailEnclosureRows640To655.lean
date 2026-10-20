module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_640 : checkTailEnclosureParent 640 = true := by decide +kernel

theorem tail_enclosure_row_641 : checkTailEnclosureParent 641 = true := by decide +kernel

theorem tail_enclosure_row_642 : checkTailEnclosureParent 642 = true := by decide +kernel

theorem tail_enclosure_row_643 : checkTailEnclosureParent 643 = true := by decide +kernel

theorem tail_enclosure_row_644 : checkTailEnclosureParent 644 = true := by decide +kernel

theorem tail_enclosure_row_645 : checkTailEnclosureParent 645 = true := by decide +kernel

theorem tail_enclosure_row_646 : checkTailEnclosureParent 646 = true := by decide +kernel

theorem tail_enclosure_row_647 : checkTailEnclosureParent 647 = true := by decide +kernel

theorem tail_enclosure_row_648 : checkTailEnclosureParent 648 = true := by decide +kernel

theorem tail_enclosure_row_649 : checkTailEnclosureParent 649 = true := by decide +kernel

theorem tail_enclosure_row_650 : checkTailEnclosureParent 650 = true := by decide +kernel

theorem tail_enclosure_row_651 : checkTailEnclosureParent 651 = true := by decide +kernel

theorem tail_enclosure_row_652 : checkTailEnclosureParent 652 = true := by decide +kernel

theorem tail_enclosure_row_653 : checkTailEnclosureParent 653 = true := by decide +kernel

theorem tail_enclosure_row_654 : checkTailEnclosureParent 654 = true := by decide +kernel

theorem tail_enclosure_row_655 : checkTailEnclosureParent 655 = true := by decide +kernel

theorem tail_enclosure_rows_640_655 :
    (List.range' 640 16).all checkTailEnclosureParent = true := by
  change ([640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_640, tail_enclosure_row_641, tail_enclosure_row_642, tail_enclosure_row_643, tail_enclosure_row_644, tail_enclosure_row_645, tail_enclosure_row_646, tail_enclosure_row_647, tail_enclosure_row_648, tail_enclosure_row_649, tail_enclosure_row_650, tail_enclosure_row_651, tail_enclosure_row_652, tail_enclosure_row_653, tail_enclosure_row_654, tail_enclosure_row_655,Bool.and_self]

end P161Formal
