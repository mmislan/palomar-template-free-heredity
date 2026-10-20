module

public import proofs.HybridCTMCInfrastructure.EventPaths

@[expose] public section

/-! Nonnegative-integral disintegration of each actual finite prefix.
These uniform one-step identities will factor clocks from state histories. -/
namespace HybridCTMC.Kernel
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem eventLaw_lintegral_prefix_step (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (n : ℕ)
    (F : (Π _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n+1))
      ∂K.eventLaw Λ hΛ x) =
    ∫⁻ u, ∫⁻ z, F (u, z)
      ∂K.clockStep Λ (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
      ∂((K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let := K.eventKernel_markov hΛ
  have h := Measure.lintegral_compProd
    (μ := (K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n))
    (κ := K.eventKernel Λ n) hF
  rw [K.eventLaw_joint hΛ x n, lintegral_map hF (by fun_prop)] at h
  exact h

omit [MeasurableSingletonClass S] in
theorem clockStep_lintegral_mul (K : HybridCTMC.Kernel S) (Λ : ℝ)
    (s : S) (B : ℝ → ℝ≥0∞) (C : S → ℝ≥0∞)
    (hB : Measurable B) (hC : Measurable C) :
    (∫⁻ z, B z.1*C z.2 ∂K.clockStep Λ s) =
      (∫⁻ h, B h ∂expMeasure Λ)*(∫⁻ y, C y ∂(K.pmf s).toMeasure) := by
  exact lintegral_prod_mul hB.aemeasurable hC.aemeasurable

end
end HybridCTMC.Kernel
