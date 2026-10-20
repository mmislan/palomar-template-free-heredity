module

public import P161Formal.TailEnclosureRows512To527
public import P161Formal.TailEnclosureRows528To543
public import P161Formal.TailEnclosureRows544To559
public import P161Formal.TailEnclosureRows560To575
public import P161Formal.TailEnclosureRows576To591
public import P161Formal.TailEnclosureRows592To607
public import P161Formal.TailEnclosureRows608To623
public import P161Formal.TailEnclosureRows624To639
public import P161Formal.TailEnclosureRows640To655
public import P161Formal.TailEnclosureRows656To671
public import P161Formal.TailEnclosureRows672To687
public import P161Formal.TailEnclosureRows688To703
public import P161Formal.TailEnclosureRows704To719
public import P161Formal.TailEnclosureRows720To735
public import P161Formal.TailEnclosureRows736To751
public import P161Formal.TailEnclosureRows752To767
public import P161Formal.TailEnclosureRows768To783
public import P161Formal.TailEnclosureRows784To799
public import P161Formal.TailEnclosureRows800To815
public import P161Formal.TailEnclosureRows816To831
public import P161Formal.TailEnclosureRows832To847
public import P161Formal.TailEnclosureRows848To863
public import P161Formal.TailEnclosureRows864To879
public import P161Formal.TailEnclosureRows880To895
public import P161Formal.TailEnclosureRows896To911
public import P161Formal.TailEnclosureRows912To927
public import P161Formal.TailEnclosureRows928To943
public import P161Formal.TailEnclosureRows944To959
public import P161Formal.TailEnclosureRows960To975
public import P161Formal.TailEnclosureRows976To991
public import P161Formal.TailEnclosureRows992To1007
public import P161Formal.TailEnclosureRows1008To1023
public import P161Formal.TailEnclosureRows1024To1039
public import P161Formal.TailEnclosureRows1040To1055
public import P161Formal.TailEnclosureRows1056To1071
public import P161Formal.TailEnclosureRows1072To1087
public import P161Formal.TailEnclosureRows1088To1103
public import P161Formal.TailEnclosureRows1104To1119
public import P161Formal.TailEnclosureRows1120To1135
public import P161Formal.TailEnclosureRows1136To1151
public import P161Formal.TailEnclosureRows1152To1165
public import P161Formal.CubicRecoveryTail
public import P161Formal.StrongRecoveryProfile

/-! Complete C10a literal high enclosure and the selected15/8 fuel comparison.
The source complete-reset operator and stopped probability law are separate. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def allTailEnclosureParents : List ℕ :=
  List.range' 512 16 ++ List.range' 528 16 ++ List.range' 544 16 ++ List.range' 560 16 ++ List.range' 576 16 ++ List.range' 592 16 ++ List.range' 608 16 ++ List.range' 624 16 ++ List.range' 640 16 ++ List.range' 656 16 ++ List.range' 672 16 ++ List.range' 688 16 ++ List.range' 704 16 ++ List.range' 720 16 ++ List.range' 736 16 ++ List.range' 752 16 ++ List.range' 768 16 ++ List.range' 784 16 ++ List.range' 800 16 ++ List.range' 816 16 ++ List.range' 832 16 ++ List.range' 848 16 ++ List.range' 864 16 ++ List.range' 880 16 ++ List.range' 896 16 ++ List.range' 912 16 ++ List.range' 928 16 ++ List.range' 944 16 ++ List.range' 960 16 ++ List.range' 976 16 ++ List.range' 992 16 ++ List.range' 1008 16 ++ List.range' 1024 16 ++ List.range' 1040 16 ++ List.range' 1056 16 ++ List.range' 1072 16 ++ List.range' 1088 16 ++ List.range' 1104 16 ++ List.range' 1120 16 ++ List.range' 1136 16 ++ List.range' 1152 14

theorem tail_enclosure_coverage : allTailEnclosureParents = List.range' 512 654 := by decide

theorem tail_enclosure_finite_checked : allTailEnclosureParents.all checkTailEnclosureParent = true := by
  simp only [allTailEnclosureParents,List.all_append,tail_enclosure_rows_512_527, tail_enclosure_rows_528_543, tail_enclosure_rows_544_559, tail_enclosure_rows_560_575, tail_enclosure_rows_576_591, tail_enclosure_rows_592_607, tail_enclosure_rows_608_623, tail_enclosure_rows_624_639, tail_enclosure_rows_640_655, tail_enclosure_rows_656_671, tail_enclosure_rows_672_687, tail_enclosure_rows_688_703, tail_enclosure_rows_704_719, tail_enclosure_rows_720_735, tail_enclosure_rows_736_751, tail_enclosure_rows_752_767, tail_enclosure_rows_768_783, tail_enclosure_rows_784_799, tail_enclosure_rows_800_815, tail_enclosure_rows_816_831, tail_enclosure_rows_832_847, tail_enclosure_rows_848_863, tail_enclosure_rows_864_879, tail_enclosure_rows_880_895, tail_enclosure_rows_896_911, tail_enclosure_rows_912_927, tail_enclosure_rows_928_943, tail_enclosure_rows_944_959, tail_enclosure_rows_960_975, tail_enclosure_rows_976_991, tail_enclosure_rows_992_1007, tail_enclosure_rows_1008_1023, tail_enclosure_rows_1024_1039, tail_enclosure_rows_1040_1055, tail_enclosure_rows_1056_1071, tail_enclosure_rows_1072_1087, tail_enclosure_rows_1088_1103, tail_enclosure_rows_1104_1119, tail_enclosure_rows_1120_1135, tail_enclosure_rows_1136_1151, tail_enclosure_rows_1152_1165,Bool.true_and]

theorem tail_enclosure_finite_parent (a : ℕ) (ha : 512 ≤ a) (hb : a ≤ 1165) :
    checkTailEnclosureParent a = true := by
  have hm : a ∈ allTailEnclosureParents := by
    rw [tail_enclosure_coverage]
    simp only [List.mem_range'_1]
    omega
  exact List.all_eq_true.mp tail_enclosure_finite_checked a hm

theorem all_high_tail_enclosures (a : ℕ) (fuel : Bool) (ha : 512 ≤ a) (hb : a ≤ 2048) :
    checkTailEnclosure a fuel = true := by
  by_cases h : a ≤ 1165
  · have hp := tail_enclosure_finite_parent a ha h
    cases fuel
    · exact checked_tail_enclosure_false a hp
    · exact checked_tail_enclosure_true a hp
  · exact recovery_tail_enclosure_above_cut a fuel (by omega) hb

theorem all_high_relative_gap (a : ℕ) (ha : 512 ≤ a) (hb : a ≤ 2048) :
    0 ≤ recoveryTailDeltaQ a ∧ recoveryTailDeltaQ a ≤ recoveryTailAQ a/10000 := by
  by_cases h : a < 768
  · exact checked_cubic_gap a h (tail_enclosure_finite_parent a ha (by omega))
  · obtain ⟨hc0,hc1⟩ := recovery_tail_coefficient_bounds a (by omega) hb
    have hA := recovery_tail_positive a ha
    rw [recovery_tail_delta_factor]
    constructor
    · exact mul_nonneg (le_of_lt hA) (le_of_lt hc0)
    · nlinarith

theorem high_tail_enclosure_inequality (a : ℕ) (fuel : Bool) (ha : 512 ≤ a) (hb : a ≤ 2048) :
    profileEntryQ a fuel-1/10^18 ≤ recoveryBaseQ a fuel ∧
      recoveryBaseQ a fuel ≤ profileEntryQ a fuel := by
  simpa only [checkTailEnclosure,decide_eq_true_eq] using all_high_tail_enclosures a fuel ha hb

theorem strong_high_table_comparison (a : ℕ) (fuel : Bool) (ha : 512 ≤ a) (hb : a ≤ 2048) :
    (9993/10000 : ℚ)*max 0 (profileEntryQ a fuel-1/10^18) ≤ strongRecoveryWitnessQ a fuel ∧
      strongRecoveryWitnessQ a fuel ≤ profileEntryQ a false := by
  have hA := recovery_tail_positive a ha
  obtain ⟨hD0,hD1⟩ := all_high_relative_gap a ha hb
  have hen := high_tail_enclosure_inequality a fuel ha hb
  have hupper := (high_tail_enclosure_inequality a false ha hb).2
  have hn : ¬a < 512 := by omega
  cases fuel
  · simp only [recoveryBaseQ,Bool.false_eq_true,ite_false,sub_zero] at hen hupper
    have hm : max 0 (profileEntryQ a false-1/10^18) ≤ recoveryTailAQ a :=
      max_le (le_of_lt hA) hen.1
    simp only [strongRecoveryWitnessQ,recoveryAQ,ite_eq_right hn,Bool.false_eq_true,
      ite_false,sub_zero]
    exact ⟨by nlinarith, hupper⟩
  · simp only [recoveryBaseQ,ite_true] at hen
    simp only [recoveryBaseQ,Bool.false_eq_true,ite_false,sub_zero] at hupper
    have hbase : 0 ≤ recoveryTailAQ a-recoveryTailDeltaQ a := by nlinarith
    have hm : max 0 (profileEntryQ a true-1/10^18) ≤ recoveryTailAQ a-recoveryTailDeltaQ a :=
      max_le hbase hen.1
    simp only [strongRecoveryWitnessQ,recoveryAQ,recoveryGapQ,ite_eq_right hn,ite_true]
    constructor <;> nlinarith

end P161Formal
