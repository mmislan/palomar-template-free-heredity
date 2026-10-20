module

public import proofs.HybridCTMCInfrastructure.EventHorizon

@[expose] public section

/-! An infinite-event-index maximal bound for predictable horizon truncation.
The clock and conditional variances come from the actual timed path law. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
noncomputable section

theorem martingale_maximal_all {W : Type*} [MeasurableSpace W] {μ : Measure W}
    [IsFiniteMeasure μ] {F : ℕ → W → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace W›}
    (hF : Martingale F ℱ μ) (h2 : ∀ n, MemLp (F n) 2 μ) {b B : ℝ} (hb : 0 < b)
    (hB : ∀ n, ∫ w, (F n w)^2 ∂μ ≤ B) :
    μ {w | ∃ n, b ≤ |F n w|} ≤ ENNReal.ofReal (B/b^2) := by
  let A : ℕ → Set W := fun n => {w | ∃ k ≤ n, b ≤ |F k w|}
  have hA : Monotone A := by
    intro i j hij w hw
    obtain ⟨k, hk, hb'⟩ := hw
    exact ⟨k, hk.trans hij, hb'⟩
  have he : {w | ∃ n, b ≤ |F n w|} = ⋃ n, A n := by
    ext w
    simp only [mem_ofPred_eq, mem_iUnion, A]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨n, k, _, hk⟩
      exact ⟨k, hk⟩
  rw [he, hA.measure_iUnion]
  exact iSup_le (fun n => martingale_maximal_square_bound hF h2 n hb (hB n))

namespace Kernel
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S]

theorem horizon_maximal (K : HybridCTMC.Kernel S) {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < θ)
    (f : S → ℝ) (x : S) (T : ℝ) {v b : ℝ} (hv0 : 0 ≤ v) (hb : 0 < b)
    (hv : ∀ s, K.expect (fun y => (f y-f s)^2) s ≤ v) :
    K.eventLaw Λ hΛ x {w | ∃ n, b ≤ |K.horizonSum Λ f T n w|} ≤
      ENNReal.ofReal ((v*(Real.exp (θ*T)*(Λ+θ)/θ))/b^2) := by
  apply martingale_maximal_all (K.martingale_horizonSum hΛ f x T)
    (K.memLp_horizonSum hΛ f x T) hb
  intro n
  exact (K.integral_horizonSum_square_le hΛ f x T n hv).trans
    (mul_le_mul_of_nonneg_left (K.sum_arrival_lower_tail hΛ hθ x n T) hv0)
end Kernel

namespace Rates
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S] [DecidableEq S]

theorem uniformized_horizon_maximal (q : Rates S) {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < θ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) (f : S → ℝ) (x : S) (T : ℝ)
    {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b)
    (hcarre : ∀ s, q.generator (fun y => (f y)^2) s-2*f s*q.generator f s ≤ c) :
    (q.uniformize Λ hΛ bound).eventLaw Λ hΛ x
      {w | ∃ n, b ≤ |(q.uniformize Λ hΛ bound).horizonSum Λ f T n w|} ≤
      ENNReal.ofReal (((c/Λ)*(Real.exp (θ*T)*(Λ+θ)/θ))/b^2) := by
  apply Kernel.horizon_maximal _ hΛ hθ f x T (div_nonneg hc hΛ.le) hb
  intro s
  rw [square_increment_uniformize]
  exact div_le_div_of_nonneg_right (hcarre s) hΛ.le
end Rates
end
end HybridCTMC
