module

public import P161Formal.GeometricRecoveryTail
public import Mathlib.Algebra.Order.Field.Basic

/-! Uniform positivity and monotonicity of the printed cubic part, extending
the structural tail treatment. Pending strict verification in its own lane
boundary; this is not a numerical or full-mission certificate. -/

@[expose] public section
namespace P161Formal

theorem affine_fraction_antitone (C D x y : ℚ) (hCD : D < C)
    (hx : D < x) (hxy : x ≤ y) :
    (C - y) / (y - D) ≤ (C - x) / (x - D) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  have hprod := mul_nonneg (le_of_lt (sub_pos.mpr hCD)) (sub_nonneg.mpr hxy)
  nlinarith

theorem cubic_recovery_product (a : ℕ) : cubicRecoveryTailQ a =
    ((980 - (a : ℚ)) / (a - 10)) * ((981 - (a : ℚ)) / (a - 9)) *
      ((982 - (a : ℚ)) / (a - 8)) := by
  simp only [cubicRecoveryTailQ, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cubic_recovery_positive (a : ℕ) (ha : 11 ≤ a) (hb : a ≤ 979) :
    0 < cubicRecoveryTailQ a := by
  have har : (11 : ℚ) ≤ a := by exact_mod_cast ha
  have hbr : (a : ℚ) ≤ 979 := by exact_mod_cast hb
  unfold cubicRecoveryTailQ
  apply div_pos
  · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem cubic_recovery_antitone (a b : ℕ) (ha : 11 ≤ a) (hab : a ≤ b) (hb : b ≤ 979) :
    cubicRecoveryTailQ b ≤ cubicRecoveryTailQ a := by
  have har : (11 : ℚ) ≤ a := by exact_mod_cast ha
  have hbar : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hbr : (b : ℚ) ≤ 979 := by exact_mod_cast hb
  have h1 := affine_fraction_antitone 980 10 a b (by norm_num) (by linarith) hbar
  have h2 := affine_fraction_antitone 981 9 a b (by norm_num) (by linarith) hbar
  have h3 := affine_fraction_antitone 982 8 a b (by norm_num) (by linarith) hbar
  have h1a : 0 ≤ (980 - (a : ℚ)) / (a - 10) := div_nonneg (by linarith) (by linarith)
  have h2a : 0 ≤ (981 - (a : ℚ)) / (a - 9) := div_nonneg (by linarith) (by linarith)
  have h2b : 0 ≤ (981 - (b : ℚ)) / (b - 9) := div_nonneg (by linarith) (by linarith)
  have h3b : 0 ≤ (982 - (b : ℚ)) / (b - 8) := div_nonneg (by linarith) (by linarith)
  rw [cubic_recovery_product b, cubic_recovery_product a]
  exact mul_le_mul (mul_le_mul h1 h2 h2b h1a) h3 h3b (mul_nonneg h1a h2a)

theorem recovery_tail_positive (a : ℕ) (ha : 512 ≤ a) : 0 < recoveryTailAQ a := by
  by_cases hb : a ≤ 768
  · simp only [recoveryTailAQ, recoveryTailQ, ite_eq_left hb]
    exact div_pos (cubic_recovery_positive a (by omega) (by omega))
      (cubic_recovery_positive 512 (by decide) (by decide))
  · exact recovery_geometric_tail_positive a (by omega)

theorem recovery_tail_at_most_one (a : ℕ) (ha : 512 ≤ a) : recoveryTailAQ a ≤ 1 := by
  have h768 : recoveryTailAQ 768 ≤ 1 := by
    simp only [recoveryTailAQ, recoveryTailQ, Nat.le_refl, ite_true]
    exact (div_le_one (cubic_recovery_positive 512 (by decide) (by decide))).mpr
      (cubic_recovery_antitone 512 768 (by decide) (by decide) (by decide))
  by_cases hb : a ≤ 768
  · simp only [recoveryTailAQ, recoveryTailQ, ite_eq_left hb]
    exact (div_le_one (cubic_recovery_positive 512 (by decide) (by decide))).mpr
      (cubic_recovery_antitone 512 a (by decide) ha (by omega))
  · have hp : (10 / 11 : ℚ) ^ (a - 768) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [recovery_tail_geometric a (by omega)]
    have hmul := mul_le_mul_of_nonneg_left hp
      (le_of_lt (recovery_geometric_tail_positive 768 (by decide)))
    exact le_trans (by simpa only [mul_one] using hmul) h768

end P161Formal
