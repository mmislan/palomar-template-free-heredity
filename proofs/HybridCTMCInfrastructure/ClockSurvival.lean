module

public import proofs.HybridCTMCInfrastructure.ClockFunctional
public import proofs.HybridCTMCInfrastructure.GeneratorIntegral
public import proofs.HybridCTMCInfrastructure.PoissonConvolution

@[expose] public section

/-! Exponential survival and the exact deterministic clock-count event.
The weighted survival family will extract counts from fixed-arrival laws. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace HoldingTime
theorem measure_Ioi {Λ t : ℝ} (hΛ : 0 < Λ) (ht : 0 ≤ t) :
    expMeasure Λ (Ioi t) = ENNReal.ofReal (Real.exp (-(Λ*t))) := by
  let := isProbabilityMeasure_expMeasure hΛ
  have he : ENNReal.ofReal (Real.exp (-(Λ*t))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hΛ.le ht))
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← ofReal_cdf (expMeasure Λ), cdf_expMeasure_eq hΛ, ite_eq_left ht,
    ENNReal.ofReal_sub 1 (Real.exp_nonneg _), ENNReal.ofReal_one,
    ENNReal.sub_sub_cancel (by simp) he]

def survivalWeight (Λ T : ℝ) (k : ℕ) (a : ℝ) : ℝ≥0∞ :=
  if a ≤ T then ENNReal.ofReal
    (Real.exp (-(Λ*(T-a)))*(Λ*(T-a))^k/(k.factorial : ℝ)) else 0

theorem measurable_survivalWeight (Λ T : ℝ) (k : ℕ) :
    Measurable (survivalWeight Λ T k) := by
  unfold survivalWeight
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · fun_prop
  · exact measurable_const

theorem survivalWeight_zero (Λ T a : ℝ) :
    survivalWeight Λ T 0 a =
      if a ≤ T then ENNReal.ofReal (Real.exp (-(Λ*(T-a)))) else 0 := by
  simp [survivalWeight]

theorem lintegral_survival_indicator {Λ t : ℝ} (hΛ : 0 < Λ) (ht : 0 ≤ t) :
    (∫⁻ h, if t < max 0 h then (1:ℝ≥0∞) else 0 ∂expMeasure Λ) =
      ENNReal.ofReal (Real.exp (-(Λ*t))) := by
  have he : (fun h : ℝ => if t < max 0 h then (1:ℝ≥0∞) else 0) =
      (Ioi t).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext h
    simp only [lt_max_iff, not_lt.mpr ht, false_or, Set.indicator, mem_Ioi]
  rw [he, lintegral_indicator measurableSet_Ioi]
  simpa using measure_Ioi hΛ ht
end HoldingTime

namespace Kernel
variable {S : Type*}

theorem clockIndex_eq_iff_between (w : ℕ → ℝ × S) {T : ℝ} (hT : 0 ≤ T)
    (hex : ∃ n, T < arrivalTime n w) (n : ℕ) :
    clockIndex T w = n ↔ arrivalTime n w ≤ T ∧ T < arrivalTime (n+1) w := by
  constructor
  · intro hn
    simpa only [hn] using clockIndex_segment hT w hex
  · intro hn
    exact clockIndex_eq_of_between w n hn.1 hn.2

end Kernel
end
end HybridCTMC
