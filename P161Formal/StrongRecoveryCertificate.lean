module

public import P161Formal.StrongRecoveryRows16To31
public import P161Formal.StrongRecoveryRows32To47
public import P161Formal.StrongRecoveryRows48To63
public import P161Formal.StrongRecoveryRows64To79
public import P161Formal.StrongRecoveryRows80To95
public import P161Formal.StrongRecoveryRows96To111
public import P161Formal.StrongRecoveryRows112To127
public import P161Formal.StrongRecoveryRows128To143
public import P161Formal.StrongRecoveryRows144To159
public import P161Formal.StrongRecoveryRows160To175
public import P161Formal.StrongRecoveryRows176To191
public import P161Formal.StrongRecoveryRows192To207
public import P161Formal.StrongRecoveryRows208To223
public import P161Formal.StrongRecoveryRows224To239
public import P161Formal.StrongRecoveryRows240To255
public import P161Formal.StrongRecoveryRows256To271
public import P161Formal.StrongRecoveryRows272To287
public import P161Formal.StrongRecoveryRows288To303
public import P161Formal.StrongRecoveryRows304To319
public import P161Formal.StrongRecoveryRows320To335
public import P161Formal.StrongRecoveryRows336To351
public import P161Formal.StrongRecoveryRows352To367
public import P161Formal.StrongRecoveryRows368To383
public import P161Formal.StrongRecoveryRows384To399
public import P161Formal.StrongRecoveryRows400To415
public import P161Formal.StrongRecoveryRows416To431
public import P161Formal.StrongRecoveryRows432To447
public import P161Formal.StrongRecoveryRows448To463
public import P161Formal.StrongRecoveryRows464To479
public import P161Formal.StrongRecoveryRows480To495
public import P161Formal.StrongRecoveryRows496To511
public import P161Formal.StrongRecoveryRows512To527
public import P161Formal.StrongRecoveryRows528To543
public import P161Formal.StrongRecoveryRows544To559
public import P161Formal.StrongRecoveryRows560To575
public import P161Formal.StrongRecoveryRows576To591
public import P161Formal.StrongRecoveryRows592To607
public import P161Formal.StrongRecoveryRows608To623
public import P161Formal.StrongRecoveryRows624To639
public import P161Formal.StrongRecoveryRows640To655
public import P161Formal.StrongRecoveryRows656To671
public import P161Formal.StrongRecoveryRows672To687
public import P161Formal.StrongRecoveryRows688To703
public import P161Formal.StrongRecoveryRows704To719
public import P161Formal.StrongRecoveryRows720To735
public import P161Formal.StrongRecoveryRows736To751
public import P161Formal.StrongRecoveryRows752To767
public import P161Formal.StrongRecoveryRows768To768
public import P161Formal.StrongGeometricChemistry
public import P161Formal.StrongRecoveryProperties

/-! Full selected-witness shape and seed-free reference-chemical certificate.
The physical source comparison, reset-gain bridge and stopped probability
theorems are separate obligations. No desired stochastic law is assumed. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def allStrongFiniteParents : List ℕ :=
  List.range' 16 16 ++ List.range' 32 16 ++ List.range' 48 16 ++ List.range' 64 16 ++ List.range' 80 16 ++ List.range' 96 16 ++ List.range' 112 16 ++ List.range' 128 16 ++ List.range' 144 16 ++ List.range' 160 16 ++ List.range' 176 16 ++ List.range' 192 16 ++ List.range' 208 16 ++ List.range' 224 16 ++ List.range' 240 16 ++ List.range' 256 16 ++ List.range' 272 16 ++ List.range' 288 16 ++ List.range' 304 16 ++ List.range' 320 16 ++ List.range' 336 16 ++ List.range' 352 16 ++ List.range' 368 16 ++ List.range' 384 16 ++ List.range' 400 16 ++ List.range' 416 16 ++ List.range' 432 16 ++ List.range' 448 16 ++ List.range' 464 16 ++ List.range' 480 16 ++ List.range' 496 16 ++ List.range' 512 16 ++ List.range' 528 16 ++ List.range' 544 16 ++ List.range' 560 16 ++ List.range' 576 16 ++ List.range' 592 16 ++ List.range' 608 16 ++ List.range' 624 16 ++ List.range' 640 16 ++ List.range' 656 16 ++ List.range' 672 16 ++ List.range' 688 16 ++ List.range' 704 16 ++ List.range' 720 16 ++ List.range' 736 16 ++ List.range' 752 16 ++ List.range' 768 1

theorem strong_finite_coverage : allStrongFiniteParents = List.range' 16 753 := by decide

theorem strong_finite_checked :
    allStrongFiniteParents.all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  simp only [allStrongFiniteParents, List.all_append, strong_recovery_rows_16_31, strong_recovery_rows_32_47, strong_recovery_rows_48_63, strong_recovery_rows_64_79, strong_recovery_rows_80_95, strong_recovery_rows_96_111, strong_recovery_rows_112_127, strong_recovery_rows_128_143, strong_recovery_rows_144_159, strong_recovery_rows_160_175, strong_recovery_rows_176_191, strong_recovery_rows_192_207, strong_recovery_rows_208_223, strong_recovery_rows_224_239, strong_recovery_rows_240_255, strong_recovery_rows_256_271, strong_recovery_rows_272_287, strong_recovery_rows_288_303, strong_recovery_rows_304_319, strong_recovery_rows_320_335, strong_recovery_rows_336_351, strong_recovery_rows_352_367, strong_recovery_rows_368_383, strong_recovery_rows_384_399, strong_recovery_rows_400_415, strong_recovery_rows_416_431, strong_recovery_rows_432_447, strong_recovery_rows_448_463, strong_recovery_rows_464_479, strong_recovery_rows_480_495, strong_recovery_rows_496_511, strong_recovery_rows_512_527, strong_recovery_rows_528_543, strong_recovery_rows_544_559, strong_recovery_rows_560_575, strong_recovery_rows_576_591, strong_recovery_rows_592_607, strong_recovery_rows_608_623, strong_recovery_rows_624_639, strong_recovery_rows_640_655, strong_recovery_rows_656_671, strong_recovery_rows_672_687, strong_recovery_rows_688_703, strong_recovery_rows_704_719, strong_recovery_rows_720_735, strong_recovery_rows_736_751, strong_recovery_rows_752_767, strong_recovery_rows_768_768, Bool.true_and]

theorem strong_finite_rows (a : ℕ) (ha : 16 ≤ a) (hb : a ≤ 768) :
    checkStrongRecoveryChemical a false = true ∧ checkStrongRecoveryChemical a true = true ∧
      checkStrongRecoveryShape a = true := by
  have hm : a ∈ allStrongFiniteParents := by
    rw [strong_finite_coverage]
    simp only [List.mem_range'_1]
    omega
  have h := List.all_eq_true.mp strong_finite_checked a hm
  simpa only [Bool.and_eq_true, and_assoc] using h

theorem strong_all_chemical_rows (a : ℕ) (fuel : Bool) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    checkStrongRecoveryChemical a fuel = true := by
  by_cases h : a ≤ 768
  · have hrow := strong_finite_rows a ha h
    cases fuel
    · exact hrow.1
    · exact hrow.2.1
  · exact strong_geometric_chemical_rows a fuel (by omega) hb

theorem strong_all_shape_rows (a : ℕ) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    checkStrongRecoveryShape a = true := by
  by_cases h : a ≤ 768
  · exact (strong_finite_rows a ha h).2.2
  · exact strong_geometric_shape a (by omega) hb

theorem strong_reference_chemical_bound (a : ℕ) (fuel : Bool) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    chemicalReferenceForQ strongRecoveryWitnessQ a fuel + 220 * strongRecoveryWitnessQ a fuel ≤
      if a < 512 then 0 else 1/4700 := by
  simpa only [checkStrongRecoveryChemical, decide_eq_true_eq] using
    strong_all_chemical_rows a fuel ha hb

theorem strong_witness_shape (a : ℕ) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    0 < strongRecoveryWitnessQ a true ∧
    strongRecoveryWitnessQ a true ≤ strongRecoveryWitnessQ a false ∧
    12 * strongRecoveryWitnessQ a false ≤ 338971453059/125000 ∧
    (if a < 512 then 1 ≤ strongRecoveryWitnessQ a true else True) := by
  simpa only [checkStrongRecoveryShape, decide_eq_true_eq] using strong_all_shape_rows a ha hb

end P161Formal
