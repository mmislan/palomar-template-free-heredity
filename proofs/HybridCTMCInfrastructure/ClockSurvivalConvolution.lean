module

public import proofs.HybridCTMCInfrastructure.ClockSurvival

@[expose] public section

/-! Uniform evaluation of iterated remaining-time survival weights. -/
namespace HybridCTMC.HoldingTime
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem survivalWeight_convolution {Λ : ℝ} (hΛ : 0 < Λ)
    (T a : ℝ) (k : ℕ) :
    (∫⁻ h, survivalWeight Λ T k (a+max 0 h) ∂expMeasure Λ) =
      survivalWeight Λ T (k+1) a := by
  by_cases ha : a ≤ T
  · let t := T-a
    have ht : 0 ≤ t := sub_nonneg.mpr ha
    let f : ℝ → ℝ := fun h => Λ*Real.exp (-(Λ*h))*
      (Real.exp (-(Λ*(t-h)))*(Λ*(t-h))^k/(k.factorial : ℝ))
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hnn : ∀ h ∈ Icc 0 t, 0 ≤ f h := by
      intro h hh
      dsimp [f]
      exact mul_nonneg (mul_nonneg hΛ.le (Real.exp_nonneg _))
        (div_nonneg (mul_nonneg (Real.exp_nonneg _)
          (pow_nonneg (mul_nonneg hΛ.le (sub_nonneg.mpr hh.2)) _))
          (Nat.cast_nonneg _))
    have hd : (fun h : ℝ => gammaPDF 1 Λ h * survivalWeight Λ T k (a+max 0 h)) =
        (Icc 0 t).indicator (fun h => ENNReal.ofReal (f h)) := by
      funext h
      by_cases hh : 0 ≤ h
      · have he : a+h ≤ T ↔ h ≤ t := by dsimp [t]; constructor <;> intro hx <;> linarith
        have hs : T-(a+h) = t-h := by dsimp [t]; ring
        simp only [gammaPDF_of_nonneg hh, Real.rpow_one, Real.Gamma_one,
          div_one, sub_self, Real.rpow_zero, mul_one, max_eq_right hh,
          survivalWeight, he, hs]
        by_cases hh' : h ≤ t
        · rw [ite_eq_left hh', indicator_of_mem (show h ∈ Icc 0 t from ⟨hh, hh'⟩)]
          exact (ENNReal.ofReal_mul (mul_nonneg hΛ.le (Real.exp_nonneg _))).symm
        · rw [ite_eq_right hh', mul_zero, indicator_of_notMem (by simp [mem_Icc, hh'])]
      · rw [gammaPDF_of_neg (lt_of_not_ge hh), zero_mul,
          indicator_of_notMem (by simp [mem_Icc, hh])]
    calc
      _ = ∫⁻ h, gammaPDF 1 Λ h * survivalWeight Λ T k (a+max 0 h) := by
        unfold expMeasure gammaMeasure
        apply lintegral_withDensity_eq_lintegral_mul
        · unfold gammaPDF; fun_prop
        · exact (measurable_survivalWeight Λ T k).comp
            (measurable_const.add (measurable_const.max measurable_id))
      _ = ∫⁻ h in Icc 0 t, ENNReal.ofReal (f h) := by
        rw [hd, lintegral_indicator measurableSet_Icc]
      _ = ENNReal.ofReal (∫ h in Icc 0 t, f h) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc
          ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hnn))
      _ = ENNReal.ofReal (∫ h in (0:ℝ)..t, f h) := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht]
      _ = survivalWeight Λ T (k+1) a := by
        rw [show (∫ h in (0:ℝ)..t, f h) =
            Real.exp (-(Λ*t))*(Λ*t)^(k+1)/((k+1).factorial : ℝ) from
          exponential_poisson_convolution Λ t k]
        simp only [survivalWeight, ite_eq_left ha, t]
  · have hz : (fun h : ℝ => survivalWeight Λ T k (a+max 0 h)) = fun _ => 0 := by
      funext h
      have hh : ¬ a+max 0 h ≤ T := by have := le_max_left 0 h; linarith
      simp only [survivalWeight, ite_eq_right hh]
    rw [hz, lintegral_zero]
    simp only [survivalWeight, ite_eq_right ha]

theorem clockIntegral_survivalWeight {Λ : ℝ} (hΛ : 0 < Λ)
    (T : ℝ) (n k : ℕ) :
    clockIntegral Λ n (survivalWeight Λ T k) = survivalWeight Λ T (n+k) 0 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [clockIntegral_succ]
    have he : (fun a => ∫⁻ h, survivalWeight Λ T k (a+max 0 h) ∂expMeasure Λ) =
        survivalWeight Λ T (k+1) := by
      funext a
      exact survivalWeight_convolution hΛ T a k
    rw [he, ih]
    congr 1
    omega

end
end HybridCTMC.HoldingTime
