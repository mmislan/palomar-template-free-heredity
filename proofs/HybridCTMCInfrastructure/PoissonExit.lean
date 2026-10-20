module

public import proofs.HybridCTMCInfrastructure.PoissonKernel

@[expose] public section

namespace HybridCTMC
open scoped BigOperators NNReal ENNReal
noncomputable section
variable {S : Type*} [Fintype S]

theorem poisson_mean (r : ℝ≥0) : HasSum (fun n => poissonWeight r n * n) (r : ℝ) := by
  have hs : HasSum (fun n => poissonWeight r (n+1) * (↑(n+1) : ℝ)) (r : ℝ) := by
    convert (ProbabilityTheory.hasSum_one_poissonMeasure r).mul_right (r : ℝ) using 1
    · funext n
      simp only [poissonWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      field_simp
    · ring
  have h := (hasSum_nat_add_iff (f := fun n => poissonWeight r n * (n : ℝ)) 1).mp hs
  simpa using h

namespace Kernel
theorem poisson_drift_tail (K : Kernel S) (r : ℝ≥0) (f : S → ℝ)
    (hf : ∀ x, 0 ≤ f x) {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b)
    (drift : ∀ x, K.expect f x ≤ f x+c)
    (A : S → Prop) [DecidablePred A] (barrier : ∀ x, A x → b ≤ f x) (x : S) :
    mass (K.poisson r x) A ≤ ENNReal.ofReal ((f x+(r : ℝ)*c)/b) := by
  have hs : HasSum (fun n => poissonWeight r n * ((f x+n*c)/b))
      ((f x+(r : ℝ)*c)/b) := by
    convert (((ProbabilityTheory.hasSum_one_poissonMeasure r).mul_right (f x)).add
      ((poisson_mean r).mul_right c)).div_const b using 1
    · funext n
      dsimp [poissonWeight]
      ring
    · ring
  rw [poisson_event]
  calc
    (∑' n, ENNReal.ofReal (poissonWeight r n)*ENNReal.ofReal ((K.power n).event A x)) ≤
        ∑' n, ENNReal.ofReal (poissonWeight r n * ((f x+n*c)/b)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [ENNReal.ofReal_mul (poissonWeight_nonneg r n)]
      apply mul_le_mul_right
      apply ENNReal.ofReal_le_ofReal
      calc
        (K.power n).event A x ≤ (K.power n).expect f x/b :=
          (K.power n).event_bound A f hf hb barrier x
        _ ≤ (f x+n*c)/b := by
          rw [power_expect]
          exact div_le_div_of_nonneg_right (K.iterate_drift f c drift n x) hb.le
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg
        (poissonWeight_nonneg r n) (div_nonneg (add_nonneg (hf x)
          (mul_nonneg (Nat.cast_nonneg n) hc)) hb.le)) hs.summable, hs.tsum_eq]
end Kernel

namespace Rates
/-- Exit-region mass of the stopped Poisson kernel. This is not yet a theorem
about sample paths of the parent source's original unstopped process. -/
theorem stopped_poisson_exit [DecidableEq S] (q : Rates S)
    (safe : S → Prop) [DecidablePred safe] (f : S → ℝ) (hf : ∀ x, 0 ≤ f x)
    {Λ c b t : ℝ} (hΛ : 0 < Λ) (hc : 0 ≤ c) (hb : 0 < b) (ht : 0 ≤ t)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ c)
    (barrier : ∀ x, ¬safe x → b ≤ f x) (x : S) :
    mass ((((q.stopped safe).uniformize Λ hΛ
      (q.stopped_rate_bound safe hΛ.le bound)).poisson ⟨Λ*t, mul_nonneg hΛ.le ht⟩) x)
      (fun y => ¬safe y) ≤ ENNReal.ofReal ((f x+c*t)/b) := by
  let K := (q.stopped safe).uniformize Λ hΛ (q.stopped_rate_bound safe hΛ.le bound)
  have hstep : ∀ y, K.expect f y ≤ f y+c/Λ := by
    intro y
    rw [show K = _ from rfl, uniformize_expect]
    exact add_le_add_right (div_le_div_of_nonneg_right (q.stopped_drift safe f hc drift y) hΛ.le) _
  have h := K.poisson_drift_tail ⟨Λ*t, mul_nonneg hΛ.le ht⟩ f hf
    (div_nonneg hc hΛ.le) hb hstep (fun y => ¬safe y) barrier x
  have he : Λ*t*(c/Λ) = c*t := by field_simp
  change mass (K.poisson ⟨Λ*t, mul_nonneg hΛ.le ht⟩ x) (fun y => ¬safe y) ≤
    ENNReal.ofReal ((f x+Λ*t*(c/Λ))/b) at h
  rw [he] at h
  exact h
end Rates
end
end HybridCTMC
