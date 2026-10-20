module

public import P161Formal.GeometricRecoveryTail
public import P161Formal.StrongRecoveryProfile

/-!
Structural seed-free chemical bound for the selected15/8,220 witness.
On769..2048 a linear/cubic factorization and15 interval envelopes replace2560
individual rows. All identities and endpoint signs must pass Lean checking.
-/

@[expose] public section
namespace P161Formal

set_option exponentiation.threshold 2048

def strong_linearRecoveryFuelGap (x : ℚ) : ℚ := 531 / 8800000 + 16941 * x / 720896000000
def strong_unfueledRecoveryPolynomial (x : ℚ) : ℚ := -235 / 11 + 5407 * x / 901120
def strong_fueledRecoveryPolynomial (x : ℚ) : ℚ :=
  458893679 / 440000 - 231526708999369 * x / 7208960000000 +
    1025456935861 * x^2 / 28835840000000 - 16941 * x^3 / 1845493760000

theorem strong_geometric_linear_fuel_gap (a : ℕ) (ha : 768 ≤ a) :
    (15 / 8) * recoveryTailDeltaQ a = recoveryTailAQ a * strong_linearRecoveryFuelGap a := by
  simp only [recoveryTailDeltaQ, recoveryTailKQ,
    ite_eq_right (show ¬a < 768 by omega), strong_linearRecoveryFuelGap]
  ring

theorem strong_geometric_witness_false (a : ℕ) (ha : 768 ≤ a) :
    strongRecoveryWitnessQ a false = recoveryTailAQ a := by
  simp [strongRecoveryWitnessQ, recoveryAQ, show ¬a < 512 by omega]

theorem strong_geometric_witness_true (a : ℕ) (ha : 768 ≤ a) :
    strongRecoveryWitnessQ a true = recoveryTailAQ a * (1 - strong_linearRecoveryFuelGap a) := by
  simp only [strongRecoveryWitnessQ, recoveryAQ, recoveryGapQ,
    ite_eq_right (show ¬a < 512 by omega), ite_true]
  rw [strong_geometric_linear_fuel_gap a ha]
  ring

theorem strong_geometric_next_ratio (a : ℕ) (ha : 768 ≤ a) :
    recoveryTailAQ (a + 1) = recoveryTailAQ a * (10 / 11 : ℚ) := by
  have he : a + 1 - 768 = a - 768 + 1 := by omega
  rw [recovery_tail_geometric (a + 1) (by omega), recovery_tail_geometric a ha,
    he, pow_add, pow_one]
  ring

theorem strong_geometric_previous_ratio (a : ℕ) (ha : 769 ≤ a) :
    recoveryTailAQ (a - 1) = recoveryTailAQ a * (11 / 10 : ℚ) := by
  have h := strong_geometric_next_ratio (a - 1) (by omega)
  have he : a - 1 + 1 = a := by omega
  rw [he] at h
  nlinarith

theorem strong_geometric_unfueled_identity (a : ℕ) (ha : 769 ≤ a) :
    chemicalReferenceForQ strongRecoveryWitnessQ a false + 220 * strongRecoveryWitnessQ a false =
      recoveryTailAQ a * strong_unfueledRecoveryPolynomial a := by
  change (a : ℚ) * (strongRecoveryWitnessQ (a - 1) false - strongRecoveryWitnessQ a false) +
    4000000 * (strongRecoveryWitnessQ a true - strongRecoveryWitnessQ a false) +
    220 * strongRecoveryWitnessQ a false = _
  simp only [strong_geometric_witness_false (a - 1) (by omega),
    strong_geometric_witness_false a (by omega), strong_geometric_witness_true a (by omega),
    strong_geometric_previous_ratio a ha, strong_linearRecoveryFuelGap, strong_unfueledRecoveryPolynomial]
  ring

theorem strong_geometric_fueled_identity (a : ℕ) (ha : 769 ≤ a) :
    chemicalReferenceForQ strongRecoveryWitnessQ a true + 220 * strongRecoveryWitnessQ a true =
      recoveryTailAQ a * strong_fueledRecoveryPolynomial a := by
  change (a : ℚ) * (strongRecoveryWitnessQ (a - 1) true - strongRecoveryWitnessQ a true) +
    800 * a * (1 - (a : ℚ) / 2048) *
      (strongRecoveryWitnessQ (a + 1) false - strongRecoveryWitnessQ a true) +
    400 * a * (strongRecoveryWitnessQ (a - 1) false - strongRecoveryWitnessQ a true) +
    (4000000 * (3 + (a : ℚ) / 2048) + 800 * 2048) *
      (strongRecoveryWitnessQ a false - strongRecoveryWitnessQ a true) +
    220 * strongRecoveryWitnessQ a true = _
  have hcast : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_one]
  simp only [strong_geometric_witness_false (a - 1) (by omega),
    strong_geometric_witness_false (a + 1) (by omega), strong_geometric_witness_false a (by omega),
    strong_geometric_witness_true (a - 1) (by omega), strong_geometric_witness_true a (by omega),
    strong_geometric_previous_ratio a ha, strong_geometric_next_ratio a (by omega),
    strong_linearRecoveryFuelGap, strong_fueledRecoveryPolynomial, hcast]
  ring

theorem strong_fueled_polynomial_difference_factor (x y : ℚ) :
    strong_fueledRecoveryPolynomial y - strong_fueledRecoveryPolynomial x =
      (y - x) * (-231526708999369 / 7208960000000 +
        (1025456935861 / 28835840000000) * (x + y) -
        (16941 / 1845493760000) * (x*x + x*y + y*y)) := by
  unfold strong_fueledRecoveryPolynomial
  ring

theorem strong_fueled_polynomial_monotone (x y : ℚ) (hx : 769 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 2048) : strong_fueledRecoveryPolynomial x ≤ strong_fueledRecoveryPolynomial y := by
  have hxU : x ≤ 2048 := le_trans hxy hy
  have hyL : 769 ≤ y := le_trans hx hxy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hx2 := mul_le_mul hxU hxU hx0 (by norm_num : (0 : ℚ) ≤ 2048)
  have hy2 := mul_le_mul hy hy hy0 (by norm_num : (0 : ℚ) ≤ 2048)
  have hprod := mul_le_mul hxU hy hy0 (by norm_num : (0 : ℚ) ≤ 2048)
  have hsum : x*x + x*y + y*y ≤ 3 * (2048 : ℚ)^2 := by nlinarith
  have hadd : 1538 ≤ x + y := by linarith
  have hq : 0 ≤ -231526708999369 / (7208960000000 : ℚ) +
      (1025456935861 / 28835840000000) * (x + y) -
      (16941 / 1845493760000) * (x*x + x*y + y*y) := by nlinarith
  apply sub_nonneg.mp
  rw [strong_fueled_polynomial_difference_factor]
  exact mul_nonneg (sub_nonneg.mpr hxy) hq

theorem strong_fueled_geometric_interval (a lo hi : ℕ) (B : ℚ)
    (hloMin : 769 ≤ lo) (hlo : lo ≤ a) (hhi : a ≤ hi) (hcap : hi ≤ 2048)
    (hB : 0 ≤ B) (hpoly : strong_fueledRecoveryPolynomial hi ≤ B)
    (henv : B * recoveryTailAQ lo ≤ (1 / 4700 : ℚ)) :
    recoveryTailAQ a * strong_fueledRecoveryPolynomial a ≤ (1 / 4700 : ℚ) := by
  have haR : (769 : ℚ) ≤ a := by exact_mod_cast (show 769 ≤ a by omega)
  have hahR : (a : ℚ) ≤ hi := by exact_mod_cast hhi
  have hcR : (hi : ℚ) ≤ 2048 := by exact_mod_cast hcap
  have hp := le_trans (strong_fueled_polynomial_monotone a hi haR hahR hcR) hpoly
  have hA := recovery_geometric_antitone lo a (by omega) hlo
  have hA0 := le_of_lt (recovery_geometric_tail_positive a (by omega))
  calc
    recoveryTailAQ a * strong_fueledRecoveryPolynomial a ≤ recoveryTailAQ a * B :=
      mul_le_mul_of_nonneg_left hp hA0
    _ ≤ recoveryTailAQ lo * B := mul_le_mul_of_nonneg_right hA hB
    _ ≤ 1 / 4700 := by simpa only [mul_comm] using henv

theorem strong_geometric_endpoint_0 :
    strong_fueledRecoveryPolynomial 869 ≤ 0 ∧
    (0 : ℚ) * recoveryTailAQ 769 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_1 :
    strong_fueledRecoveryPolynomial 873 ≤ 102 ∧
    (102 : ℚ) * recoveryTailAQ 870 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_2 :
    strong_fueledRecoveryPolynomial 875 ≤ 162 ∧
    (162 : ℚ) * recoveryTailAQ 874 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_3 :
    strong_fueledRecoveryPolynomial 877 ≤ 223 ∧
    (223 : ℚ) * recoveryTailAQ 876 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_4 :
    strong_fueledRecoveryPolynomial 878 ≤ 253 ∧
    (253 : ℚ) * recoveryTailAQ 878 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_5 :
    strong_fueledRecoveryPolynomial 879 ≤ 283 ∧
    (283 : ℚ) * recoveryTailAQ 879 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_6 :
    strong_fueledRecoveryPolynomial 880 ≤ 314 ∧
    (314 : ℚ) * recoveryTailAQ 880 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_7 :
    strong_fueledRecoveryPolynomial 881 ≤ 344 ∧
    (344 : ℚ) * recoveryTailAQ 881 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_8 :
    strong_fueledRecoveryPolynomial 883 ≤ 405 ∧
    (405 : ℚ) * recoveryTailAQ 882 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_9 :
    strong_fueledRecoveryPolynomial 885 ≤ 467 ∧
    (467 : ℚ) * recoveryTailAQ 884 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_10 :
    strong_fueledRecoveryPolynomial 889 ≤ 591 ∧
    (591 : ℚ) * recoveryTailAQ 886 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_11 :
    strong_fueledRecoveryPolynomial 898 ≤ 873 ∧
    (873 : ℚ) * recoveryTailAQ 890 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_12 :
    strong_fueledRecoveryPolynomial 934 ≤ 2062 ∧
    (2062 : ℚ) * recoveryTailAQ 899 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_13 :
    strong_fueledRecoveryPolynomial 950 ≤ 2619 ∧
    (2619 : ℚ) * recoveryTailAQ 935 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_endpoint_14 :
    strong_fueledRecoveryPolynomial 2048 ≤ 84347 ∧
    (84347 : ℚ) * recoveryTailAQ 951 ≤ (1 / 4700 : ℚ) := by
  constructor
  · norm_num [strong_fueledRecoveryPolynomial]
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem strong_geometric_fueled_chemical_bound (a : ℕ) (ha : 769 ≤ a) (hb : a ≤ 2048) :
    chemicalReferenceForQ strongRecoveryWitnessQ a true + 220 * strongRecoveryWitnessQ a true ≤ (1 / 4700 : ℚ) := by
  rw [strong_geometric_fueled_identity a ha]
  by_cases h0 : a ≤ 869
  · exact strong_fueled_geometric_interval a 769 869 0 (by decide) (by omega) h0
      (by decide) (by norm_num) strong_geometric_endpoint_0.1 strong_geometric_endpoint_0.2
  by_cases h1 : a ≤ 873
  · exact strong_fueled_geometric_interval a 870 873 102 (by decide) (by omega) h1
      (by decide) (by norm_num) strong_geometric_endpoint_1.1 strong_geometric_endpoint_1.2
  by_cases h2 : a ≤ 875
  · exact strong_fueled_geometric_interval a 874 875 162 (by decide) (by omega) h2
      (by decide) (by norm_num) strong_geometric_endpoint_2.1 strong_geometric_endpoint_2.2
  by_cases h3 : a ≤ 877
  · exact strong_fueled_geometric_interval a 876 877 223 (by decide) (by omega) h3
      (by decide) (by norm_num) strong_geometric_endpoint_3.1 strong_geometric_endpoint_3.2
  by_cases h4 : a ≤ 878
  · exact strong_fueled_geometric_interval a 878 878 253 (by decide) (by omega) h4
      (by decide) (by norm_num) strong_geometric_endpoint_4.1 strong_geometric_endpoint_4.2
  by_cases h5 : a ≤ 879
  · exact strong_fueled_geometric_interval a 879 879 283 (by decide) (by omega) h5
      (by decide) (by norm_num) strong_geometric_endpoint_5.1 strong_geometric_endpoint_5.2
  by_cases h6 : a ≤ 880
  · exact strong_fueled_geometric_interval a 880 880 314 (by decide) (by omega) h6
      (by decide) (by norm_num) strong_geometric_endpoint_6.1 strong_geometric_endpoint_6.2
  by_cases h7 : a ≤ 881
  · exact strong_fueled_geometric_interval a 881 881 344 (by decide) (by omega) h7
      (by decide) (by norm_num) strong_geometric_endpoint_7.1 strong_geometric_endpoint_7.2
  by_cases h8 : a ≤ 883
  · exact strong_fueled_geometric_interval a 882 883 405 (by decide) (by omega) h8
      (by decide) (by norm_num) strong_geometric_endpoint_8.1 strong_geometric_endpoint_8.2
  by_cases h9 : a ≤ 885
  · exact strong_fueled_geometric_interval a 884 885 467 (by decide) (by omega) h9
      (by decide) (by norm_num) strong_geometric_endpoint_9.1 strong_geometric_endpoint_9.2
  by_cases h10 : a ≤ 889
  · exact strong_fueled_geometric_interval a 886 889 591 (by decide) (by omega) h10
      (by decide) (by norm_num) strong_geometric_endpoint_10.1 strong_geometric_endpoint_10.2
  by_cases h11 : a ≤ 898
  · exact strong_fueled_geometric_interval a 890 898 873 (by decide) (by omega) h11
      (by decide) (by norm_num) strong_geometric_endpoint_11.1 strong_geometric_endpoint_11.2
  by_cases h12 : a ≤ 934
  · exact strong_fueled_geometric_interval a 899 934 2062 (by decide) (by omega) h12
      (by decide) (by norm_num) strong_geometric_endpoint_12.1 strong_geometric_endpoint_12.2
  by_cases h13 : a ≤ 950
  · exact strong_fueled_geometric_interval a 935 950 2619 (by decide) (by omega) h13
      (by decide) (by norm_num) strong_geometric_endpoint_13.1 strong_geometric_endpoint_13.2
  exact strong_fueled_geometric_interval a 951 2048 84347 (by decide) (by omega) hb
      (by decide) (by norm_num) strong_geometric_endpoint_14.1 strong_geometric_endpoint_14.2

theorem strong_geometric_unfueled_chemical_bound (a : ℕ) (ha : 769 ≤ a) (hb : a ≤ 2048) :
    chemicalReferenceForQ strongRecoveryWitnessQ a false + 220 * strongRecoveryWitnessQ a false ≤ (1 / 4700 : ℚ) := by
  rw [strong_geometric_unfueled_identity a ha]
  have hA0 := le_of_lt (recovery_geometric_tail_positive a (by omega))
  have haR : (a : ℚ) ≤ 2048 := by exact_mod_cast hb
  have hp : strong_unfueledRecoveryPolynomial a ≤ 0 := by
    unfold strong_unfueledRecoveryPolynomial
    nlinarith
  exact le_trans (mul_nonpos_of_nonneg_of_nonpos hA0 hp) (by norm_num)

theorem strong_geometric_chemical_rows (a : ℕ) (fuel : Bool) (ha : 769 ≤ a) (hb : a ≤ 2048) :
    checkStrongRecoveryChemical a fuel = true := by
  simp only [checkStrongRecoveryChemical, decide_eq_true_eq,
    ite_eq_right (show ¬a < 512 by omega)]
  cases fuel
  · exact strong_geometric_unfueled_chemical_bound a ha hb
  · exact strong_geometric_fueled_chemical_bound a ha hb

end P161Formal
