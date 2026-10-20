module

public import proofs.HybridCTMCInfrastructure.PoissonKernel

@[expose] public section

namespace HybridCTMC
open scoped BigOperators NNReal ENNReal
noncomputable section
variable {S : Type*} [Fintype S]
namespace Rates

theorem killed_stopped_drift (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) {κ c : ℝ} (hc : 0 ≤ c)
    (drift : ∀ x, safe x → q.generator f x ≤ -κ*f x+c) (x : S) :
    (q.stopped safe).generator (fun y => if safe y then f y else 0) x ≤
      -κ*(if safe x then f x else 0)+c := by
  by_cases hx : safe x
  · simpa [generator, stopped, hx] using
      (q.killed_generator_le safe f hf x hx).trans (drift x hx)
  · simpa [generator, stopped, hx] using hc

/-- The source-independent cleanup contract. The probability space is explicitly the
Poisson mixture of the stopped uniformization kernel. Source drift, finite invariant
class, and identification with physical CTMC paths must be supplied separately. -/
theorem killed_poisson_tail [DecidableEq S] (q : Rates S)
    (safe : S → Prop) [DecidablePred safe] (f : S → ℝ) (hf : ∀ x, 0 ≤ f x)
    {Λ κ c b t : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (hκΛ : κ ≤ Λ)
    (hc : 0 ≤ c) (hb : 0 < b) (ht : 0 ≤ t)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ -κ*f x+c) (x : S) :
    mass ((((q.stopped safe).uniformize Λ hΛ
      (q.stopped_rate_bound safe hΛ.le bound)).poisson ⟨Λ*t, mul_nonneg hΛ.le ht⟩) x)
      (fun y => safe y ∧ b ≤ f y) ≤
    ENNReal.ofReal ((Real.exp (-κ*t)*(if safe x then f x else 0)+c/κ)/b) := by
  let g : S → ℝ := fun y => if safe y then f y else 0
  let K := (q.stopped safe).uniformize Λ hΛ (q.stopped_rate_bound safe hΛ.le bound)
  have hg : ∀ y, 0 ≤ g y := by intro y; dsimp [g]; split_ifs; exact hf y; rfl
  have ha : 0 ≤ 1-κ/Λ := sub_nonneg.mpr ((div_le_one hΛ).mpr hκΛ)
  have hstep : ∀ y, K.expect g y ≤ (1-κ/Λ)*g y+(1-(1-κ/Λ))*(c/κ) := by
    intro y
    rw [show K = _ from rfl, uniformize_expect]
    have hd := div_le_div_of_nonneg_right (q.killed_stopped_drift safe f hf hc drift y) hΛ.le
    have heq : (1-κ/Λ)*g y+(1-(1-κ/Λ))*(c/κ) = g y+(-κ*g y+c)/Λ := by
      field_simp
      ring
    rw [heq]
    exact add_le_add_right hd _
  have h := K.poisson_tail ⟨Λ*t, mul_nonneg hΛ.le ht⟩ g hg ha
    (div_nonneg hc hκ.le) hb hstep (fun y => safe y ∧ b ≤ f y)
    (fun y hy => by simpa [g, hy.1] using hy.2) x
  have he : Λ*t*((1-κ/Λ)-1) = -κ*t := by field_simp; ring
  change mass (K.poisson ⟨Λ*t, mul_nonneg hΛ.le ht⟩ x) (fun y => safe y ∧ b ≤ f y) ≤
    ENNReal.ofReal ((Real.exp (Λ*t*((1-κ/Λ)-1))*g x+c/κ)/b) at h
  rw [he] at h
  exact h
end Rates
end
end HybridCTMC
