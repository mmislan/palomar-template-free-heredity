module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_544 : checkTailEnclosureParent 544 = true := by decide +kernel

theorem tail_enclosure_row_545 : checkTailEnclosureParent 545 = true := by decide +kernel

theorem tail_enclosure_row_546 : checkTailEnclosureParent 546 = true := by decide +kernel

theorem tail_enclosure_row_547 : checkTailEnclosureParent 547 = true := by decide +kernel

theorem tail_enclosure_row_548 : checkTailEnclosureParent 548 = true := by decide +kernel

theorem tail_enclosure_row_549 : checkTailEnclosureParent 549 = true := by decide +kernel

theorem tail_enclosure_row_550 : checkTailEnclosureParent 550 = true := by decide +kernel

theorem tail_enclosure_row_551 : checkTailEnclosureParent 551 = true := by decide +kernel

theorem tail_enclosure_row_552 : checkTailEnclosureParent 552 = true := by decide +kernel

theorem tail_enclosure_row_553 : checkTailEnclosureParent 553 = true := by decide +kernel

theorem tail_enclosure_row_554 : checkTailEnclosureParent 554 = true := by decide +kernel

theorem tail_enclosure_row_555 : checkTailEnclosureParent 555 = true := by decide +kernel

theorem tail_enclosure_row_556 : checkTailEnclosureParent 556 = true := by decide +kernel

theorem tail_enclosure_row_557 : checkTailEnclosureParent 557 = true := by decide +kernel

theorem tail_enclosure_row_558 : checkTailEnclosureParent 558 = true := by decide +kernel

theorem tail_enclosure_row_559 : checkTailEnclosureParent 559 = true := by decide +kernel

theorem tail_enclosure_rows_544_559 :
    (List.range' 544 16).all checkTailEnclosureParent = true := by
  change ([544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_544, tail_enclosure_row_545, tail_enclosure_row_546, tail_enclosure_row_547, tail_enclosure_row_548, tail_enclosure_row_549, tail_enclosure_row_550, tail_enclosure_row_551, tail_enclosure_row_552, tail_enclosure_row_553, tail_enclosure_row_554, tail_enclosure_row_555, tail_enclosure_row_556, tail_enclosure_row_557, tail_enclosure_row_558, tail_enclosure_row_559,Bool.and_self]

end P161Formal
