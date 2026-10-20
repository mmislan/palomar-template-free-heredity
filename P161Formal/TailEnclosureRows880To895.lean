module

public import P161Formal.TailEnclosureInterface

/-! Literal table enclosure decisions for the displayed high-count interval.
Each decision uses ordinary Lean kernel reduction, with no native evaluator. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem tail_enclosure_row_880 : checkTailEnclosureParent 880 = true := by decide +kernel

theorem tail_enclosure_row_881 : checkTailEnclosureParent 881 = true := by decide +kernel

theorem tail_enclosure_row_882 : checkTailEnclosureParent 882 = true := by decide +kernel

theorem tail_enclosure_row_883 : checkTailEnclosureParent 883 = true := by decide +kernel

theorem tail_enclosure_row_884 : checkTailEnclosureParent 884 = true := by decide +kernel

theorem tail_enclosure_row_885 : checkTailEnclosureParent 885 = true := by decide +kernel

theorem tail_enclosure_row_886 : checkTailEnclosureParent 886 = true := by decide +kernel

theorem tail_enclosure_row_887 : checkTailEnclosureParent 887 = true := by decide +kernel

theorem tail_enclosure_row_888 : checkTailEnclosureParent 888 = true := by decide +kernel

theorem tail_enclosure_row_889 : checkTailEnclosureParent 889 = true := by decide +kernel

theorem tail_enclosure_row_890 : checkTailEnclosureParent 890 = true := by decide +kernel

theorem tail_enclosure_row_891 : checkTailEnclosureParent 891 = true := by decide +kernel

theorem tail_enclosure_row_892 : checkTailEnclosureParent 892 = true := by decide +kernel

theorem tail_enclosure_row_893 : checkTailEnclosureParent 893 = true := by decide +kernel

theorem tail_enclosure_row_894 : checkTailEnclosureParent 894 = true := by decide +kernel

theorem tail_enclosure_row_895 : checkTailEnclosureParent 895 = true := by decide +kernel

theorem tail_enclosure_rows_880_895 :
    (List.range' 880 16).all checkTailEnclosureParent = true := by
  change ([880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895].all checkTailEnclosureParent) = true
  simp only [List.all_cons,List.all_nil,tail_enclosure_row_880, tail_enclosure_row_881, tail_enclosure_row_882, tail_enclosure_row_883, tail_enclosure_row_884, tail_enclosure_row_885, tail_enclosure_row_886, tail_enclosure_row_887, tail_enclosure_row_888, tail_enclosure_row_889, tail_enclosure_row_890, tail_enclosure_row_891, tail_enclosure_row_892, tail_enclosure_row_893, tail_enclosure_row_894, tail_enclosure_row_895,Bool.and_self]

end P161Formal
