module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_528 : checkTailEnclosureParent 528 = true := by decide +kernel

theorem tail_enclosure_row_529 : checkTailEnclosureParent 529 = true := by decide +kernel

theorem tail_enclosure_row_530 : checkTailEnclosureParent 530 = true := by decide +kernel

theorem tail_enclosure_row_531 : checkTailEnclosureParent 531 = true := by decide +kernel

theorem tail_enclosure_row_532 : checkTailEnclosureParent 532 = true := by decide +kernel

theorem tail_enclosure_row_533 : checkTailEnclosureParent 533 = true := by decide +kernel

theorem tail_enclosure_row_534 : checkTailEnclosureParent 534 = true := by decide +kernel

theorem tail_enclosure_row_535 : checkTailEnclosureParent 535 = true := by decide +kernel

theorem tail_enclosure_row_536 : checkTailEnclosureParent 536 = true := by decide +kernel

theorem tail_enclosure_row_537 : checkTailEnclosureParent 537 = true := by decide +kernel

theorem tail_enclosure_row_538 : checkTailEnclosureParent 538 = true := by decide +kernel

theorem tail_enclosure_row_539 : checkTailEnclosureParent 539 = true := by decide +kernel

theorem tail_enclosure_row_540 : checkTailEnclosureParent 540 = true := by decide +kernel

theorem tail_enclosure_row_541 : checkTailEnclosureParent 541 = true := by decide +kernel

theorem tail_enclosure_row_542 : checkTailEnclosureParent 542 = true := by decide +kernel

theorem tail_enclosure_row_543 : checkTailEnclosureParent 543 = true := by decide +kernel

theorem tail_enclosure_rows_528_543 :
    (List.range' 528 16).all checkTailEnclosureParent = true := by
  change ([528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_528, tail_enclosure_row_529, tail_enclosure_row_530, tail_enclosure_row_531, tail_enclosure_row_532, tail_enclosure_row_533, tail_enclosure_row_534, tail_enclosure_row_535, tail_enclosure_row_536, tail_enclosure_row_537, tail_enclosure_row_538, tail_enclosure_row_539, tail_enclosure_row_540, tail_enclosure_row_541, tail_enclosure_row_542, tail_enclosure_row_543,Bool.and_self]

end P161Formal
