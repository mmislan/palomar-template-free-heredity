module

public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace HeritableCompositions

noncomputable def fairBinomialWeight (n k : ℕ) : ℝ := (n.choose k : ℝ)/(2 : ℝ)^n

theorem fairBinomialWeight_nonneg (n k : ℕ) : 0 ≤ fairBinomialWeight n k := by
  unfold fairBinomialWeight
  positivity

theorem fair_binomial_moment (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (n+1), fairBinomialWeight n k*Real.exp (t*((k : ℝ)-(n : ℝ)/2)) =
      (Real.cosh (t/2))^n := by
  rw [Real.cosh_eq,div_pow,add_pow,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  have he : Real.exp (t*((k : ℝ)-(n : ℝ)/2)) =
      Real.exp (t/2)^k*Real.exp (-(t/2))^(n-k) := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add,Nat.cast_sub hkn]
    congr 1
    ring
  rw [he]
  unfold fairBinomialWeight
  ring

theorem fair_binomial_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), fairBinomialWeight n k = 1 := by
  simpa using fair_binomial_moment n 0

theorem fair_binomial_subgaussian (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (n+1), fairBinomialWeight n k*Real.exp (t*((k : ℝ)-(n : ℝ)/2)) ≤
      Real.exp ((n : ℝ)*t^2/8) := by
  rw [fair_binomial_moment]
  have h := pow_le_pow_left₀ (Real.cosh_pos (t/2)).le (Real.cosh_le_exp_half_sq (t/2)) n
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

end HeritableCompositions
