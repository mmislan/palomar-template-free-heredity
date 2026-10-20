module

public import proofs.HybridCTMCInfrastructure.HoldingTime

@[expose] public section

/-! A scalar functional for finitely many independent clipped holding times.
Identification with the actual event law is a separate uniform theorem. -/
namespace HybridCTMC.HoldingTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

def clockIntegral (Λ : ℝ) : ℕ → (ℝ → ℝ≥0∞) → ℝ≥0∞
  | 0, φ => φ 0
  | n+1, φ => clockIntegral Λ n (fun a => ∫⁻ h, φ (a+max 0 h) ∂expMeasure Λ)

@[simp] theorem clockIntegral_zero (Λ : ℝ) (φ : ℝ → ℝ≥0∞) :
    clockIntegral Λ 0 φ = φ 0 := rfl

theorem clockIntegral_succ (Λ : ℝ) (n : ℕ) (φ : ℝ → ℝ≥0∞) :
    clockIntegral Λ (n+1) φ =
      clockIntegral Λ n (fun a => ∫⁻ h, φ (a+max 0 h) ∂expMeasure Λ) := rfl

theorem measurable_holding_average {Λ : ℝ} (hΛ : 0 < Λ)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun a : ℝ => ∫⁻ h, φ (a+max 0 h) ∂expMeasure Λ) := by
  let := isProbabilityMeasure_expMeasure hΛ
  exact (hφ.comp (measurable_fst.add (measurable_const.max measurable_snd))).lintegral_prod_right'

end
end HybridCTMC.HoldingTime
