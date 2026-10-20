module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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

/-! The independent exponential holding-time component of uniformization.
These are genuine measure integrals, with no assumed moment identities. -/
namespace HybridCTMC.HoldingTime
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem integral_density {Λ : ℝ} (hΛ : 0 < Λ) (g : ℝ → ℝ) :
    ∫ x, g x ∂expMeasure Λ = ∫ x in Ioi 0, Λ*Real.exp (-(Λ*x))*g x := by
  unfold expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 Λ)
    (by unfold gammaPDF; fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hΛ _), smul_eq_mul]
  have he : (fun x => gammaPDFReal 1 Λ x*g x) =
      (Ici (0:ℝ)).indicator (fun x => Λ*Real.exp (-(Λ*x))*g x) := by
    funext x
    simp [gammaPDFReal, Set.indicator, ite_mul]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem integral_pow {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    ∫ x, x^n ∂expMeasure Λ = (n.factorial : ℝ)/Λ^n := by
  rw [integral_density hΛ]
  have he : (fun x : ℝ => Λ*Real.exp (-(Λ*x))*x^n) =
      fun x => Λ*(x^n*Real.exp (-(Λ*x))) := by funext x; ring
  rw [he, integral_const_mul]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) hΛ
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at hg
  rw [hg]
  rw [show (n:ℝ)+1 = ((n+1:ℕ):ℝ) by push_cast; rfl, Real.rpow_natCast, pow_succ]
  field_simp
  rw [← mul_pow]
  simp [hΛ.ne']

theorem integral_id {Λ : ℝ} (hΛ : 0 < Λ) : ∫ x, x ∂expMeasure Λ = 1/Λ := by
  simpa using integral_pow hΛ 1

theorem integral_square {Λ : ℝ} (hΛ : 0 < Λ) : ∫ x, x^2 ∂expMeasure Λ = 2/Λ^2 := by
  simpa using integral_pow hΛ 2

theorem integrable_pow {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (expMeasure Λ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow hΛ]
  positivity

theorem integral_laplace {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < Λ+θ) :
    ∫ x, Real.exp (-θ*x) ∂expMeasure Λ = Λ/(Λ+θ) := by
  rw [integral_density hΛ]
  have he : (fun x => Λ*Real.exp (-(Λ*x))*Real.exp (-θ*x)) =
      fun x => Λ*Real.exp (-((Λ+θ)*x)) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (by norm_num) hθ
  norm_num at hg
  rw [hg]
  ring
end
end HybridCTMC.HoldingTime
