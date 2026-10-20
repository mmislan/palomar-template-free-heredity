module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_624 : checkTailEnclosureParent 624 = true := by decide +kernel

theorem tail_enclosure_row_625 : checkTailEnclosureParent 625 = true := by decide +kernel

theorem tail_enclosure_row_626 : checkTailEnclosureParent 626 = true := by decide +kernel

theorem tail_enclosure_row_627 : checkTailEnclosureParent 627 = true := by decide +kernel

theorem tail_enclosure_row_628 : checkTailEnclosureParent 628 = true := by decide +kernel

theorem tail_enclosure_row_629 : checkTailEnclosureParent 629 = true := by decide +kernel

theorem tail_enclosure_row_630 : checkTailEnclosureParent 630 = true := by decide +kernel

theorem tail_enclosure_row_631 : checkTailEnclosureParent 631 = true := by decide +kernel

theorem tail_enclosure_row_632 : checkTailEnclosureParent 632 = true := by decide +kernel

theorem tail_enclosure_row_633 : checkTailEnclosureParent 633 = true := by decide +kernel

theorem tail_enclosure_row_634 : checkTailEnclosureParent 634 = true := by decide +kernel

theorem tail_enclosure_row_635 : checkTailEnclosureParent 635 = true := by decide +kernel

theorem tail_enclosure_row_636 : checkTailEnclosureParent 636 = true := by decide +kernel

theorem tail_enclosure_row_637 : checkTailEnclosureParent 637 = true := by decide +kernel

theorem tail_enclosure_row_638 : checkTailEnclosureParent 638 = true := by decide +kernel

theorem tail_enclosure_row_639 : checkTailEnclosureParent 639 = true := by decide +kernel

theorem tail_enclosure_rows_624_639 :
    (List.range' 624 16).all checkTailEnclosureParent = true := by
  change ([624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_624, tail_enclosure_row_625, tail_enclosure_row_626, tail_enclosure_row_627, tail_enclosure_row_628, tail_enclosure_row_629, tail_enclosure_row_630, tail_enclosure_row_631, tail_enclosure_row_632, tail_enclosure_row_633, tail_enclosure_row_634, tail_enclosure_row_635, tail_enclosure_row_636, tail_enclosure_row_637, tail_enclosure_row_638, tail_enclosure_row_639,Bool.and_self]

end P161Formal
