module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_576 : checkTailEnclosureParent 576 = true := by decide +kernel

theorem tail_enclosure_row_577 : checkTailEnclosureParent 577 = true := by decide +kernel

theorem tail_enclosure_row_578 : checkTailEnclosureParent 578 = true := by decide +kernel

theorem tail_enclosure_row_579 : checkTailEnclosureParent 579 = true := by decide +kernel

theorem tail_enclosure_row_580 : checkTailEnclosureParent 580 = true := by decide +kernel

theorem tail_enclosure_row_581 : checkTailEnclosureParent 581 = true := by decide +kernel

theorem tail_enclosure_row_582 : checkTailEnclosureParent 582 = true := by decide +kernel

theorem tail_enclosure_row_583 : checkTailEnclosureParent 583 = true := by decide +kernel

theorem tail_enclosure_row_584 : checkTailEnclosureParent 584 = true := by decide +kernel

theorem tail_enclosure_row_585 : checkTailEnclosureParent 585 = true := by decide +kernel

theorem tail_enclosure_row_586 : checkTailEnclosureParent 586 = true := by decide +kernel

theorem tail_enclosure_row_587 : checkTailEnclosureParent 587 = true := by decide +kernel

theorem tail_enclosure_row_588 : checkTailEnclosureParent 588 = true := by decide +kernel

theorem tail_enclosure_row_589 : checkTailEnclosureParent 589 = true := by decide +kernel

theorem tail_enclosure_row_590 : checkTailEnclosureParent 590 = true := by decide +kernel

theorem tail_enclosure_row_591 : checkTailEnclosureParent 591 = true := by decide +kernel

theorem tail_enclosure_rows_576_591 :
    (List.range' 576 16).all checkTailEnclosureParent = true := by
  change ([576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_576, tail_enclosure_row_577, tail_enclosure_row_578, tail_enclosure_row_579, tail_enclosure_row_580, tail_enclosure_row_581, tail_enclosure_row_582, tail_enclosure_row_583, tail_enclosure_row_584, tail_enclosure_row_585, tail_enclosure_row_586, tail_enclosure_row_587, tail_enclosure_row_588, tail_enclosure_row_589, tail_enclosure_row_590, tail_enclosure_row_591,Bool.and_self]

end P161Formal
