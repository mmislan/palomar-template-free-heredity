module

public import proofs.HybridCTMCInfrastructure.HoldingTime
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Uniform scalar convolution for the exponential arrival count.
This analytic identity alone does not identify the constructed path law. -/
namespace HybridCTMC
open MeasureTheory
noncomputable section

theorem exponential_poisson_convolution (Λ T : ℝ) (n : ℕ) :
    (∫ h in (0:ℝ)..T, Λ*Real.exp (-(Λ*h))*
      (Real.exp (-(Λ*(T-h)))*(Λ*(T-h))^n/(n.factorial : ℝ))) =
      Real.exp (-(Λ*T))*(Λ*T)^(n+1)/((n+1).factorial : ℝ) := by
  have hi :
      (fun h : ℝ => Λ*Real.exp (-(Λ*h))*
        (Real.exp (-(Λ*(T-h)))*(Λ*(T-h))^n/(n.factorial : ℝ))) =
      fun h => (Λ*Real.exp (-(Λ*T))*Λ^n/(n.factorial : ℝ))*(T-h)^n := by
    funext h
    have he : Real.exp (-(Λ*h))*Real.exp (-(Λ*(T-h))) = Real.exp (-(Λ*T)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_pow]
    calc
      _ = (Real.exp (-(Λ*h))*Real.exp (-(Λ*(T-h))))*
          (Λ*Λ^n/(n.factorial : ℝ))*(T-h)^n := by ring
      _ = _ := by rw [he]; ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) T,
    sub_self, sub_zero, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [mul_pow, pow_succ]
  field_simp [hf, hn]

end
end HybridCTMC
