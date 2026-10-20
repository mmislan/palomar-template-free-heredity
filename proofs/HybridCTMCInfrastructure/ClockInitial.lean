module

public import proofs.HybridCTMCInfrastructure.ClockSupport

@[expose] public section

/-! The timed path has the prescribed initial state and strictly positive
holding times almost surely. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder Function
open scoped BigOperators
noncomputable section
namespace HoldingTime
theorem ae_pos (Λ : ℝ) : ∀ᵐ t ∂expMeasure Λ, 0 < t := by
  let : NullSingletonClass (expMeasure Λ) := by unfold expMeasure gammaMeasure; infer_instance
  filter_upwards [ae_nonneg Λ, (expMeasure Λ).ae_ne 0] with t ht hn
  exact lt_of_le_of_ne ht (Ne.symm hn)
end HoldingTime

namespace Kernel
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem eventLaw_eq_traj (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    K.eventLaw Λ hΛ x = by
      let := K.eventKernel_markov hΛ
      exact ProbabilityTheory.Kernel.traj (K.eventKernel Λ) 0 (fun _ => (0, x)) := by
  let := K.eventKernel_markov hΛ
  unfold eventLaw ProbabilityTheory.Kernel.trajMeasure
  rw [Measure.map_dirac]
  exact Measure.dirac_bind (by fun_prop) _

set_option maxHeartbeats 1000000 in
theorem ae_event_initial (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, w 0 = (0, x) := by
  let := K.eventKernel_markov hΛ
  rw [K.eventLaw_eq_traj hΛ x]
  let x₀ : (Π _ : Finset.Iic 0, ℝ × S) := fun _ => (0, x)
  have he :
      (ProbabilityTheory.Kernel.traj (X := fun _ : ℕ => ℝ × S) (K.eventKernel Λ) 0 x₀).map
        (fun w : ℕ → ℝ × S => updateFinset (π := fun _ : ℕ => ℝ × S) w (Finset.Iic 0) x₀) =
      ProbabilityTheory.Kernel.traj (X := fun _ : ℕ => ℝ × S) (K.eventKernel Λ) 0 x₀ :=
    ProbabilityTheory.Kernel.traj_map_updateFinset (X := fun _ : ℕ => ℝ × S)
      (κ := K.eventKernel Λ) x₀
  change ∀ᵐ w ∂ProbabilityTheory.Kernel.traj (X := fun _ : ℕ => ℝ × S)
    (K.eventKernel Λ) 0 x₀, w 0 = (0, x)
  rw [← he]
  have hp : MeasurableSet {w : ℕ → ℝ × S | w 0 = (0, x)} :=
    (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) 0)
      (measurableSet_singleton ((0:ℝ), x))
  apply (ae_map_iff
    (f := fun w : ℕ → ℝ × S => updateFinset (π := fun _ : ℕ => ℝ × S)
      w (Finset.Iic 0) x₀)
    (p := fun w : ℕ → ℝ × S => w 0 = (0, x)) (by fun_prop) hp).mpr
  exact Filter.Eventually.of_forall (fun w => by simp [updateFinset, x₀])

theorem ae_holding_pos (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ n : ℕ, 0 < (w (n+1)).1 := by
  rw [ae_all_iff]
  intro n
  apply K.eventLaw_ae hΛ x n (fun _ z => 0 < z.1)
    (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
  intro s
  let := isProbabilityMeasure_expMeasure hΛ
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
  filter_upwards [HoldingTime.ae_pos Λ] with t ht
  exact Filter.Eventually.of_forall (fun _ => ht)
end Kernel
end
end HybridCTMC
