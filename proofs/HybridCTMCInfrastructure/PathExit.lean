module

public import proofs.HybridCTMCInfrastructure.SkeletonPaths

@[expose] public section

namespace HybridCTMC
open scoped BigOperators NNReal ENNReal Classical
noncomputable section
variable {S : Type*} [Fintype S]

theorem Kernel.ext_weights {K H : Kernel S} (h : ∀ x y, K.weight x y = H.weight x y) : K = H := by
  cases K with
  | mk wk nk tk =>
    cases H with
    | mk wh nh th =>
      have hw : wk = wh := funext fun x => funext fun y => h x y
      subst wh
      rfl

namespace Rates
theorem uniformize_stopped (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    {Λ : ℝ} (hΛ : 0 < Λ) (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) :
    (q.uniformize Λ hΛ bound).stop safe =
      (q.stopped safe).uniformize Λ hΛ (q.stopped_rate_bound safe hΛ.le bound) := by
  apply Kernel.ext_weights
  intro x y
  by_cases hx : safe x
  · simp [Kernel.stop, uniformize, stopped, hx]
  · simp [Kernel.stop, Kernel.identity, uniformize, stopped, hx]

/-- A maximal exit bound for the original, source-rate uniformization skeleton.
The probability law is an explicitly constructed Poisson-random finite trajectory.
Continuous clock paths and their compensators are not premises or conclusions. -/
theorem poissonTrajectory_exit_bound (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) {Λ c b t : ℝ}
    (hΛ : 0 < Λ) (hc : 0 ≤ c) (hb : 0 < b) (ht : 0 ≤ t)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ c)
    (barrier : ∀ x, ¬safe x → b ≤ f x) (x : S) :
    mass ((q.uniformize Λ hΛ bound).poissonTrajectory ⟨Λ*t, mul_nonneg hΛ.le ht⟩ x)
      (Kernel.exited safe) ≤ ENNReal.ofReal ((f x+c*t)/b) := by
  let r : ℝ≥0 := ⟨Λ*t, mul_nonneg hΛ.le ht⟩
  change mass ((q.uniformize Λ hΛ bound).poissonTrajectory r x)
    (Kernel.exited safe) ≤ ENNReal.ofReal ((f x+c*t)/b)
  calc
    _ = mass (((q.uniformize Λ hΛ bound).stop safe).poisson r x) (fun y => ¬safe y) :=
      Kernel.poissonTrajectory_exit (q.uniformize Λ hΛ bound) safe r x
    _ = mass (((q.stopped safe).uniformize Λ hΛ
        (q.stopped_rate_bound safe hΛ.le bound)).poisson r x) (fun y => ¬safe y) :=
      congrArg (fun K : Kernel S => mass (K.poisson r x) (fun y => ¬safe y))
        (q.uniformize_stopped safe hΛ bound)
    _ ≤ _ := q.stopped_poisson_exit safe f hf hΛ hc hb ht bound drift barrier x
end Rates
end
end HybridCTMC
