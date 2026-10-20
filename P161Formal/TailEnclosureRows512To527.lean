module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_512 : checkTailEnclosureParent 512 = true := by decide +kernel

theorem tail_enclosure_row_513 : checkTailEnclosureParent 513 = true := by decide +kernel

theorem tail_enclosure_row_514 : checkTailEnclosureParent 514 = true := by decide +kernel

theorem tail_enclosure_row_515 : checkTailEnclosureParent 515 = true := by decide +kernel

theorem tail_enclosure_row_516 : checkTailEnclosureParent 516 = true := by decide +kernel

theorem tail_enclosure_row_517 : checkTailEnclosureParent 517 = true := by decide +kernel

theorem tail_enclosure_row_518 : checkTailEnclosureParent 518 = true := by decide +kernel

theorem tail_enclosure_row_519 : checkTailEnclosureParent 519 = true := by decide +kernel

theorem tail_enclosure_row_520 : checkTailEnclosureParent 520 = true := by decide +kernel

theorem tail_enclosure_row_521 : checkTailEnclosureParent 521 = true := by decide +kernel

theorem tail_enclosure_row_522 : checkTailEnclosureParent 522 = true := by decide +kernel

theorem tail_enclosure_row_523 : checkTailEnclosureParent 523 = true := by decide +kernel

theorem tail_enclosure_row_524 : checkTailEnclosureParent 524 = true := by decide +kernel

theorem tail_enclosure_row_525 : checkTailEnclosureParent 525 = true := by decide +kernel

theorem tail_enclosure_row_526 : checkTailEnclosureParent 526 = true := by decide +kernel

theorem tail_enclosure_row_527 : checkTailEnclosureParent 527 = true := by decide +kernel

theorem tail_enclosure_rows_512_527 :
    (List.range' 512 16).all checkTailEnclosureParent = true := by
  change ([512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_512, tail_enclosure_row_513, tail_enclosure_row_514, tail_enclosure_row_515, tail_enclosure_row_516, tail_enclosure_row_517, tail_enclosure_row_518, tail_enclosure_row_519, tail_enclosure_row_520, tail_enclosure_row_521, tail_enclosure_row_522, tail_enclosure_row_523, tail_enclosure_row_524, tail_enclosure_row_525, tail_enclosure_row_526, tail_enclosure_row_527,Bool.and_self]

end P161Formal
