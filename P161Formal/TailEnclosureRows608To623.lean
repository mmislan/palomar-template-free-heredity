module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_608 : checkTailEnclosureParent 608 = true := by decide +kernel

theorem tail_enclosure_row_609 : checkTailEnclosureParent 609 = true := by decide +kernel

theorem tail_enclosure_row_610 : checkTailEnclosureParent 610 = true := by decide +kernel

theorem tail_enclosure_row_611 : checkTailEnclosureParent 611 = true := by decide +kernel

theorem tail_enclosure_row_612 : checkTailEnclosureParent 612 = true := by decide +kernel

theorem tail_enclosure_row_613 : checkTailEnclosureParent 613 = true := by decide +kernel

theorem tail_enclosure_row_614 : checkTailEnclosureParent 614 = true := by decide +kernel

theorem tail_enclosure_row_615 : checkTailEnclosureParent 615 = true := by decide +kernel

theorem tail_enclosure_row_616 : checkTailEnclosureParent 616 = true := by decide +kernel

theorem tail_enclosure_row_617 : checkTailEnclosureParent 617 = true := by decide +kernel

theorem tail_enclosure_row_618 : checkTailEnclosureParent 618 = true := by decide +kernel

theorem tail_enclosure_row_619 : checkTailEnclosureParent 619 = true := by decide +kernel

theorem tail_enclosure_row_620 : checkTailEnclosureParent 620 = true := by decide +kernel

theorem tail_enclosure_row_621 : checkTailEnclosureParent 621 = true := by decide +kernel

theorem tail_enclosure_row_622 : checkTailEnclosureParent 622 = true := by decide +kernel

theorem tail_enclosure_row_623 : checkTailEnclosureParent 623 = true := by decide +kernel

theorem tail_enclosure_rows_608_623 :
    (List.range' 608 16).all checkTailEnclosureParent = true := by
  change ([608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_608, tail_enclosure_row_609, tail_enclosure_row_610, tail_enclosure_row_611, tail_enclosure_row_612, tail_enclosure_row_613, tail_enclosure_row_614, tail_enclosure_row_615, tail_enclosure_row_616, tail_enclosure_row_617, tail_enclosure_row_618, tail_enclosure_row_619, tail_enclosure_row_620, tail_enclosure_row_621, tail_enclosure_row_622, tail_enclosure_row_623,Bool.and_self]

end P161Formal
