module

public import proofs.HybridCTMCInfrastructure.StateHistory

@[expose] public section

/-! Nonnegative rewards for arbitrary finite-history PMFs. This sum-based
interface avoids imposing a measurable-space structure on lists. -/
namespace HybridCTMC
open MeasureTheory
open scoped ENNReal Classical
noncomputable section

def nnReward {A : Type*} (p : PMF A) (f : A → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a*f a

theorem nnReward_bind {A B : Type*} (p : PMF A) (K : A → PMF B) (f : B → ℝ≥0∞) :
    nnReward (p.bind K) f = nnReward p (fun a => nnReward (K a) f) := by
  simp only [nnReward, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc, ENNReal.tsum_mul_left]

theorem nnReward_pure {A : Type*} (a : A) (f : A → ℝ≥0∞) :
    nnReward (PMF.pure a) f = f a := by
  simp [nnReward, PMF.pure_apply]

theorem nnReward_map {A B : Type*} (p : PMF A) (g : A → B) (f : B → ℝ≥0∞) :
    nnReward (p.map g) f = nnReward p (fun a => f (g a)) := by
  rw [PMF.map, nnReward_bind]
  simp only [Function.comp_apply, nnReward_pure]

theorem lintegral_pmf_nnReward {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : PMF A) (f : A → ℝ≥0∞) :
    (∫⁻ a, f a ∂p.toMeasure) = nnReward p f := by
  rw [lintegral_countable', nnReward]
  apply tsum_congr
  intro a
  rw [p.toMeasure_apply_singleton a (measurableSet_singleton a), mul_comm]

namespace Kernel
variable {S : Type*} [Fintype S]

theorem trajectoryReward_snoc (K : HybridCTMC.Kernel S) (n : ℕ) (x : S)
    (ψ : List S → ℝ≥0∞) :
    nnReward (K.trajectory (n+1) x) ψ = nnReward (K.trajectory n x)
      (fun xs => nnReward (K.pmf (xs.getLastD x)) (fun y => ψ (xs ++ [y]))) := by
  rw [K.trajectory_snoc, nnReward_bind]
  simp only [nnReward_map]

end Kernel
end
end HybridCTMC
