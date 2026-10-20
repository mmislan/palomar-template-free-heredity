module

public import P161Formal.Quantitative
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Scalar budgets for the stronger witness. This branch replaces the random
fuel-clock exception by a bounded-count exponential tilt at28 actual divisions,
retaining the same0.5 recovery deadline and10^-5 allowance. Counted-word and
bounded-reward stochastic expectation comparisons remain separate obligations.
Before checking, expose Quantitative's computational constants at its next
normal owned boundary and recheck that module. No frozen source is changed.
-/

@[expose] public section
namespace P161Formal
noncomputable section
open scoped BigOperators

def strongKilledGamma : ℝ := 263197 / 1175
def strongWordNumerator : ℝ := (338971453059 / 125000) *
  ∑ j ∈ Finset.range 28, (239 : ℝ)^j / j.factorial

theorem strong_killed_gamma_identity :
    (220 : ℝ) + 4 - 12/4700 = strongKilledGamma := by norm_num [strongKilledGamma]

theorem strong_reset_comparison_constant :
    8 + (93867565097 / 200000000 : ℝ) / (9993 / 10000) = 95466445097 / 199860000 ∧
    (95466445097 / 199860000 : ℝ) < 478 := by norm_num

theorem strong_exponential_lower :
    expOneLower^112 * (1997 / 2000) ≤ Real.exp (strongKilledGamma / 2) := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h112 : expOneLower^112 ≤ Real.exp 112 := by
    have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower 112
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using h
  have hn : (1997 / 2000 : ℝ) ≤ Real.exp (-(3 / 2000)) := by
    have h := Real.add_one_le_exp (-(3 / 2000 : ℝ))
    norm_num at h
    linarith
  calc
    expOneLower^112 * (1997 / 2000) ≤ Real.exp 112 * Real.exp (-(3 / 2000)) :=
      mul_le_mul h112 hn (by norm_num) (Real.exp_nonneg _)
    _ = Real.exp (112 - 3 / 2000) := by rw [Real.exp_sub, Real.exp_neg]; rfl
    _ ≤ Real.exp (strongKilledGamma / 2) :=
      Real.exp_le_exp.mpr (by norm_num [strongKilledGamma])

theorem strong_low_words_le_two_millionths :
    strongWordNumerator / Real.exp (strongKilledGamma / 2) ≤ (2 / 1000000 : ℝ) := by
  have hN : 0 ≤ strongWordNumerator := by
    norm_num [strongWordNumerator, Finset.sum_range_succ, Nat.factorial_succ]
  have hL : 0 < expOneLower^112 * (1997 / 2000) := by norm_num [expOneLower]
  have hdiv := div_le_div_of_nonneg_left hN hL strong_exponential_lower
  have hrat : strongWordNumerator / (expOneLower^112 * (1997 / 2000)) ≤
      (2 / 1000000 : ℝ) := by
    norm_num [strongWordNumerator, expOneLower, Finset.sum_range_succ, Nat.factorial_succ]
  exact le_trans hdiv hrat

theorem strong_exp_one_le_eleven_fourths : Real.exp 1 ≤ (11 / 4 : ℝ) := by
  have h := Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 3) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  linarith

theorem strong_count_exponent :
    (16 : ℝ) * (Real.exp 1 - 1) ≤ 28 ∧ 28 * (1/2 : ℝ) - 28 = -14 := by
  have h := strong_exp_one_le_eleven_fourths
  constructor <;> linarith

theorem strong_count_tail_le_one_millionth : Real.exp (-14) ≤ (1 / 1000000 : ℝ) := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h14 : expOneLower^14 ≤ Real.exp 14 := by
    have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower 14
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using h
  have hdiv := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) (pow_pos hpos 14) h14
  have hrat : 1 / expOneLower^14 ≤ (1 / 1000000 : ℝ) := by norm_num [expOneLower]
  rw [Real.exp_neg]
  simpa only [one_div] using le_trans hdiv hrat

theorem strong_recovery_scalar_allowance :
    strongWordNumerator / Real.exp (strongKilledGamma / 2) +
      Real.exp (-14) ≤ (1 / 100000 : ℝ) := by
  have hw := strong_low_words_le_two_millionths
  have hp := strong_count_tail_le_one_millionth
  linarith

end
end P161Formal
