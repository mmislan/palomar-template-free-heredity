module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_560 : checkTailEnclosureParent 560 = true := by decide +kernel

theorem tail_enclosure_row_561 : checkTailEnclosureParent 561 = true := by decide +kernel

theorem tail_enclosure_row_562 : checkTailEnclosureParent 562 = true := by decide +kernel

theorem tail_enclosure_row_563 : checkTailEnclosureParent 563 = true := by decide +kernel

theorem tail_enclosure_row_564 : checkTailEnclosureParent 564 = true := by decide +kernel

theorem tail_enclosure_row_565 : checkTailEnclosureParent 565 = true := by decide +kernel

theorem tail_enclosure_row_566 : checkTailEnclosureParent 566 = true := by decide +kernel

theorem tail_enclosure_row_567 : checkTailEnclosureParent 567 = true := by decide +kernel

theorem tail_enclosure_row_568 : checkTailEnclosureParent 568 = true := by decide +kernel

theorem tail_enclosure_row_569 : checkTailEnclosureParent 569 = true := by decide +kernel

theorem tail_enclosure_row_570 : checkTailEnclosureParent 570 = true := by decide +kernel

theorem tail_enclosure_row_571 : checkTailEnclosureParent 571 = true := by decide +kernel

theorem tail_enclosure_row_572 : checkTailEnclosureParent 572 = true := by decide +kernel

theorem tail_enclosure_row_573 : checkTailEnclosureParent 573 = true := by decide +kernel

theorem tail_enclosure_row_574 : checkTailEnclosureParent 574 = true := by decide +kernel

theorem tail_enclosure_row_575 : checkTailEnclosureParent 575 = true := by decide +kernel

theorem tail_enclosure_rows_560_575 :
    (List.range' 560 16).all checkTailEnclosureParent = true := by
  change ([560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_560, tail_enclosure_row_561, tail_enclosure_row_562, tail_enclosure_row_563, tail_enclosure_row_564, tail_enclosure_row_565, tail_enclosure_row_566, tail_enclosure_row_567, tail_enclosure_row_568, tail_enclosure_row_569, tail_enclosure_row_570, tail_enclosure_row_571, tail_enclosure_row_572, tail_enclosure_row_573, tail_enclosure_row_574, tail_enclosure_row_575,Bool.and_self]

end P161Formal
