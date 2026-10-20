module

public import proofs.HybridCTMCInfrastructure.TimedHistoryLaw
public import proofs.HybridCTMCInfrastructure.TimedEndpoint
public import proofs.HybridCTMCInfrastructure.Cleanup

@[expose] public section

/-! Endpoint identification and cleanup tails for the actual timed process. -/
namespace HybridCTMC
open MeasureTheory Set
open scoped ENNReal NNReal Classical
noncomputable section
namespace Kernel
variable {S : Type*} [Fintype S]

theorem trajectory_endpoint (K : HybridCTMC.Kernel S) (n : ℕ) (x d : S) :
    (K.trajectory n x).map (fun xs => xs.getLastD d) = (K.power n).pmf x := by
  induction n generalizing x with
  | zero => simp [trajectory, power, identity_pmf, PMF.map, PMF.pure_bind]
  | succ n ih =>
    rw [trajectory, PMF.map_bind, power, comp_pmf]
    apply congrArg (fun f => (K.pmf x).bind f)
    funext y
    rw [PMF.map_comp]
    calc
      _ = (K.trajectory n y).map (fun xs => xs.getLastD d) := by
        rw [PMF.map, PMF.map]
        apply pmf_bind_congr_support
        intro xs hx
        have hn := K.trajectory_support_nonempty n y xs hx
        have he : (x::xs).getLastD d = xs.getLastD d := by
          cases xs with
          | nil => exact (hn rfl).elim
          | cons z zs => simp
        simp only [Function.comp_apply, he]
      _ = _ := ih y

theorem poissonTrajectory_endpoint (K : HybridCTMC.Kernel S) (r : ℝ≥0) (x d : S) :
    (K.poissonTrajectory r x).map (fun xs => xs.getLastD d) = K.poisson r x := by
  rw [poissonTrajectory, PMF.map_bind, poisson]
  simp only [trajectory_endpoint]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem timedEndpoint_mass_poisson (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (A : S → Prop) :
    mass (K.timedEndpoint Λ hΛ T x) A =
      mass (K.poisson ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x) A := by
  rw [K.mass_timedEndpoint hΛ T x A,
    ← K.poissonTrajectory_endpoint ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x x, mass_map,
    ← K.timedHistory_event hΛ hT x (fun xs => A (xs.getLastD x))]
  congr 1
  ext w
  simp only [mem_ofPred_eq, timedHistory, statePrefix_getLastD, timedState]

theorem timedEndpoint_eq_poisson (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) :
    K.timedEndpoint Λ hΛ T x = K.poisson ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x := by
  apply PMF.ext
  intro y
  have h := K.timedEndpoint_mass_poisson hΛ hT x (fun z => z = y)
  simpa only [mass, tsum_ite_eq] using h

end Kernel

namespace Rates
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem killed_timed_tail (q : Rates S) (safe : S → Prop)
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) {Λ κ c b T : ℝ}
    (hΛ : 0 < Λ) (hκ : 0 < κ) (hκΛ : κ ≤ Λ)
    (hc : 0 ≤ c) (hb : 0 < b) (hT : 0 ≤ T)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ -κ*f x+c) (x : S) :
    mass (((q.stopped safe).uniformize Λ hΛ
      (q.stopped_rate_bound safe hΛ.le bound)).timedEndpoint Λ hΛ T x)
      (fun y => safe y ∧ b ≤ f y) ≤
      ENNReal.ofReal ((Real.exp (-κ*T)*(if safe x then f x else 0)+c/κ)/b) := by
  rw [Kernel.timedEndpoint_eq_poisson _ hΛ hT x]
  exact q.killed_poisson_tail safe f hf hΛ hκ hκΛ hc hb hT bound drift x

end Rates
end
end HybridCTMC
