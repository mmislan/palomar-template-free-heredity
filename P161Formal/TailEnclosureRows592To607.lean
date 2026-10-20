module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_592 : checkTailEnclosureParent 592 = true := by decide +kernel

theorem tail_enclosure_row_593 : checkTailEnclosureParent 593 = true := by decide +kernel

theorem tail_enclosure_row_594 : checkTailEnclosureParent 594 = true := by decide +kernel

theorem tail_enclosure_row_595 : checkTailEnclosureParent 595 = true := by decide +kernel

theorem tail_enclosure_row_596 : checkTailEnclosureParent 596 = true := by decide +kernel

theorem tail_enclosure_row_597 : checkTailEnclosureParent 597 = true := by decide +kernel

theorem tail_enclosure_row_598 : checkTailEnclosureParent 598 = true := by decide +kernel

theorem tail_enclosure_row_599 : checkTailEnclosureParent 599 = true := by decide +kernel

theorem tail_enclosure_row_600 : checkTailEnclosureParent 600 = true := by decide +kernel

theorem tail_enclosure_row_601 : checkTailEnclosureParent 601 = true := by decide +kernel

theorem tail_enclosure_row_602 : checkTailEnclosureParent 602 = true := by decide +kernel

theorem tail_enclosure_row_603 : checkTailEnclosureParent 603 = true := by decide +kernel

theorem tail_enclosure_row_604 : checkTailEnclosureParent 604 = true := by decide +kernel

theorem tail_enclosure_row_605 : checkTailEnclosureParent 605 = true := by decide +kernel

theorem tail_enclosure_row_606 : checkTailEnclosureParent 606 = true := by decide +kernel

theorem tail_enclosure_row_607 : checkTailEnclosureParent 607 = true := by decide +kernel

theorem tail_enclosure_rows_592_607 :
    (List.range' 592 16).all checkTailEnclosureParent = true := by
  change ([592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_592, tail_enclosure_row_593, tail_enclosure_row_594, tail_enclosure_row_595, tail_enclosure_row_596, tail_enclosure_row_597, tail_enclosure_row_598, tail_enclosure_row_599, tail_enclosure_row_600, tail_enclosure_row_601, tail_enclosure_row_602, tail_enclosure_row_603, tail_enclosure_row_604, tail_enclosure_row_605, tail_enclosure_row_606, tail_enclosure_row_607,Bool.and_self]

end P161Formal
