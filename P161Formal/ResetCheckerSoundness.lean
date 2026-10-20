module

public import P161Formal.ResetChecker
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Soundness of the integer residual test as an exact real inequality.
The moment's equality to its binomial sum is proved in BinomialRecurrence;
this file supplies the positive-denominator arithmetic bridge. -/

public section
namespace P161Formal
noncomputable section

theorem reset_integer_comparison_sound (a p K X bDen : ℕ) (bNum : ℤ)
    (hb : 0 < bDen)
    (hcheck : (2 * p * K * 200000000 * bDen : ℤ) ≤
      (93867565097 * X * 2048 * 2^a * bDen : ℤ) +
      bNum * (2048 * 2^a * 10^18 * 200000000 : ℤ)) :
    2 * ((p : ℝ) / 2048) * ((K : ℝ) / (2^a * 10^18)) -
      (93867565097 / 200000000) * ((X : ℝ) / 10^18) ≤ (bNum : ℝ) / bDen := by
  have hbR : (0 : ℝ) < bDen := by exact_mod_cast hb
  have hpR : (0 : ℝ) < 2^a := pow_pos (by norm_num) a
  have hR : (2 : ℝ) * p * K * 200000000 * bDen ≤
      93867565097 * X * 2048 * 2^a * bDen +
      (bNum : ℝ) * (2048 * 2^a * 10^18 * 200000000) := by
    exact_mod_cast hcheck
  have hidentity :
      2 * ((p : ℝ) / 2048) * ((K : ℝ) / (2^a * 10^18)) -
          (93867565097 / 200000000) * ((X : ℝ) / 10^18) - (bNum : ℝ) / bDen =
      (2 * p * K * 200000000 * bDen -
        (93867565097 * X * 2048 * 2^a * bDen +
          (bNum : ℝ) * (2048 * 2^a * 10^18 * 200000000))) /
        (2048 * 2^a * 10^18 * 200000000 * bDen) := by
    field_simp
    ring
  apply sub_nonpos.mp
  rw [hidentity]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr hR
  · positivity

theorem checked_reset_row_sound (a : ℕ) (fuel : Bool) (bNum : ℤ) (bDen : ℕ)
    (hb : 0 < bDen) (hcheck : checkResetRow a fuel bNum bDen = true) :
    let pair := fullProfilePairs[a]?.getD (0, 0)
    let X := (if fuel then pair.2 else pair.1) - 1
    let K := pairedMomentNumerator fullProfileFuelZero a
    let pNum := if fuel then 3 * 2048 + a else 2048
    2 * ((pNum : ℝ) / 2048) * ((K : ℝ) / (2^a * 10^18)) -
      (93867565097 / 200000000) * ((X : ℝ) / 10^18) ≤ (bNum : ℝ) / bDen := by
  unfold checkResetRow at hcheck
  exact reset_integer_comparison_sound _ _ _ _ _ _ hb (of_decide_eq_true hcheck)

end
end P161Formal
