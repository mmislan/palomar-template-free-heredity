module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# The actual exponential holding-time law after a real-time cut

`HybridCTMC.HoldingTime.measure_Ioi` supplies a scalar survival probability.
The missing statement proved here identifies the entire residual measure:
restrict a hold to being longer than a nonnegative elapsed time, then subtract
that elapsed time. The result is the original exponential law multiplied by
the survival probability. No independent residual clock is postulated.

This is a single-hold physical-cut lemma, not a two-horizon path-law theorem.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

private theorem expMeasure_Iic_formula {Lam : ℝ} (hLam : 0 < Lam) (t : ℝ) :
    expMeasure Lam (Iic t) =
      ENNReal.ofReal (if 0 ≤ t then 1 - Real.exp (-(Lam * t)) else 0) := by
  let := isProbabilityMeasure_expMeasure hLam
  rw [← ofReal_cdf (expMeasure Lam), cdf_expMeasure_eq hLam]

/-- The residual distribution function, before any normalization, computed
directly from the official exponential CDF and Stieltjes interval measure. -/
private theorem expMeasure_residual_Ioc {Lam s t : ℝ} (hLam : 0 < Lam)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    expMeasure Lam (Ioc s (s + t)) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) * expMeasure Lam (Iic t) := by
  let := isProbabilityMeasure_expMeasure hLam
  have he : Real.exp (-(Lam * (s + t))) =
      Real.exp (-(Lam * s)) * Real.exp (-(Lam * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    expMeasure Lam (Ioc s (s + t)) =
        ENNReal.ofReal (cdf (expMeasure Lam) (s + t) - cdf (expMeasure Lam) s) := by
      conv_lhs => rw [← measure_cdf (expMeasure Lam)]
      exact StieltjesFunction.measure_Ioc _ _ _
    _ = ENNReal.ofReal
        ((1 - Real.exp (-(Lam * (s + t)))) - (1 - Real.exp (-(Lam * s)))) := by
      rw [cdf_expMeasure_eq hLam, ite_eq_left (add_nonneg hs ht),
        cdf_expMeasure_eq hLam, ite_eq_left hs]
    _ = ENNReal.ofReal (Real.exp (-(Lam * s)) * (1 - Real.exp (-(Lam * t)))) := by
      rw [he]
      congr 1
      ring
    _ = ENNReal.ofReal (Real.exp (-(Lam * s))) * expMeasure Lam (Iic t) := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _), expMeasure_Iic_formula hLam,
        ite_eq_left ht]

/-- Memorylessness as equality of actual measures on the real line. This holds
for every residual event, including events with negative elements: those
elements automatically receive zero mass on both sides. -/
theorem expMeasure_residual_map {Lam s : ℝ} (hLam : 0 < Lam) (hs : 0 ≤ s) :
    ((expMeasure Lam).restrict (Ioi s)).map (fun t : ℝ => t - s) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) • expMeasure Lam := by
  let := isProbabilityMeasure_expMeasure hLam
  apply Measure.ext_of_Iic
  intro t
  have hm : Measurable (fun u : ℝ => u - s) := by fun_prop
  have hi : (fun u : ℝ => u - s) ⁻¹' Iic t ∩ Ioi s = Ioc s (s + t) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hu, hs'⟩
      exact ⟨hs', by linarith⟩
    · rintro ⟨hs', hu⟩
      exact ⟨by linarith, hs'⟩
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage hm),
    hi, Measure.smul_apply, smul_eq_mul]
  by_cases ht : 0 ≤ t
  · exact expMeasure_residual_Ioc hLam hs ht
  · have he : Ioc s (s + t) = (∅ : Set ℝ) := by
      ext u
      simp only [mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro hu
      linarith
    rw [he, measure_empty, expMeasure_Iic_formula hLam, ite_eq_right ht]
    simp

/-- Event form of the same physical residual identity. There is no assumption
that the residual event is nonnegative: the measure itself enforces support. -/
theorem expMeasure_residual_event {Lam s : ℝ} (hLam : 0 < Lam) (hs : 0 ≤ s)
    (A : Set ℝ) (hA : MeasurableSet A) :
    expMeasure Lam {t | s < t ∧ t - s ∈ A} =
      ENNReal.ofReal (Real.exp (-(Lam * s))) * expMeasure Lam A := by
  have hm : Measurable (fun t : ℝ => t - s) := by fun_prop
  have he : {t : ℝ | s < t ∧ t - s ∈ A} =
      (fun t : ℝ => t - s) ⁻¹' A ∩ Ioi s := by
    ext t
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi, and_comm]
  rw [he, ← Measure.restrict_apply (hA.preimage hm),
    ← Measure.map_apply hm hA, expMeasure_residual_map hLam hs,
    Measure.smul_apply, smul_eq_mul]

/-- Nonnegative-reward form, ready for integration against a finite-history
kernel when the elapsed time at a physical cut depends on that history. -/
theorem expMeasure_residual_lintegral {Lam s : ℝ} (hLam : 0 < Lam) (hs : 0 ≤ s)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t in Ioi s, F (t - s) ∂expMeasure Lam) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) * ∫⁻ u, F u ∂expMeasure Lam := by
  rw [← lintegral_map hF (by fun_prop), expMeasure_residual_map hLam hs,
    lintegral_smul_measure, smul_eq_mul]

end
end CTMCHeredity20261019
