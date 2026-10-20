module

public import proofs.CTMCHeredity20261019.GeneratorAdapter
public import proofs.HybridCTMCInfrastructure.Channels

@[expose] public section

/-!
# A finite labelled proposal law, with an explicit idle mark

The existing `HybridCTMC.Channels` is the only source interface. Actual labels
are retained even when their state update is null. `none` alone is the extra
uniformization idle proposal. No stopping-time, resource-counting, or timed
path-law identification is assumed or asserted here.
-/

namespace CTMCHeredity20261019.MarkedUniformization

open scoped BigOperators Classical
noncomputable section

variable {S R : Type} [Fintype R]

/-- A literal source channel changes the state; the extra idle label does not. -/
def next (C : HybridCTMC.Channels S R) (x : S) : Option R → S
  | none => x
  | some r => C.next x r

/-- Proposal weight, retaining channel identity rather than aggregating states. -/
def weight (C : HybridCTMC.Channels S R) (Lam : ℝ) (x : S) : Option R → ℝ
  | none => 1 - (∑ r, C.propensity x r) / Lam
  | some r => C.propensity x r / Lam

theorem weight_nonneg (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (x : S) (m : Option R) : 0 ≤ weight C Lam x m := by
  cases m with
  | none => exact sub_nonneg.mpr ((div_le_one hLam).mpr (bound x))
  | some r => exact div_nonneg (C.nonneg x r) hLam.le

theorem weight_sum (C : HybridCTMC.Channels S R) (Lam : ℝ) (x : S) :
    ∑ m, weight C Lam x m = 1 := by
  rw [Fintype.sum_option]
  simp only [weight]
  rw [← Finset.sum_div]
  ring

/-- The normalized distribution of the complete proposal label. -/
def law (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) : PMF (Option R) :=
  PMF.ofFintype (fun m => ENNReal.ofReal (weight C Lam x m)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ =>
      weight_nonneg C hLam bound x m), weight_sum]
    simp)

theorem law_apply (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) (m : Option R) :
    law C hLam bound x m = ENNReal.ofReal (weight C Lam x m) := by
  simp only [law, PMF.ofFintype_apply]

theorem law_apply_real (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) (m : Option R) :
    (law C hLam bound x m).toReal = weight C Lam x m := by
  rw [law_apply, ENNReal.toReal_ofReal (weight_nonneg C hLam bound x m)]

/-- The actual PMF after forgetting the proposal label. -/
def erase (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) : PMF S :=
  (law C hLam bound x).map (next C x)

/-- Finite expectation of an observable of the proposal label. -/
def expect (C : HybridCTMC.Channels S R) (Lam : ℝ) (x : S)
    (g : Option R → ℝ) : ℝ := ∑ m, weight C Lam x m * g m

/-- This expectation uses the proved normalized PMF, not a supplied law. -/
theorem expect_eq_law_sum (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (x : S) (g : Option R → ℝ) :
    expect C Lam x g = ∑ m, (law C hLam bound x m).toReal * g m := by
  simp only [law_apply_real, expect]

/-- The labelled expectation formula needs a finite mark set, not a finite
state space. In particular it applies to the source with unbounded ledgers. -/
theorem expect_next_sum (C : HybridCTMC.Channels S R) (Lam : ℝ)
    (f : S → ℝ) (x : S) :
    expect C Lam x (fun m => f (next C x m)) =
      f x + (∑ r, C.propensity x r * (f (C.next x r) - f x)) / Lam := by
  rw [expect, Fintype.sum_option]
  simp only [weight, next]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

section FiniteState
variable [Fintype S] [DecidableEq S]

/-- Erasing labels has exactly the original channel generator. Idle and actual
self-updates remain separate labels even though this expectation forgets them. -/
theorem expect_next (C : HybridCTMC.Channels S R) (Lam : ℝ)
    (f : S → ℝ) (x : S) :
    expect C Lam x (fun m => f (next C x m)) =
      f x + C.rates.generator f x / Lam := by
  rw [expect_next_sum, HybridCTMC.Channels.generator_eq]

/-- Equality with the independently reconstructed finite uniformized kernel
is proved on every observable. No generator-correspondence axiom is assumed. -/
theorem expect_next_eq_uniformizedKernel
    (C : HybridCTMC.Channels S R) {L Lam : ℝ}
    (hG : FunctionalCapacity.IsGen L C.rates.generator)
    (hLam : 0 < Lam) (hL : L ≤ Lam) (f : S → ℝ) (x : S) :
    expect C Lam x (fun m => f (next C x m)) =
      (CTMCHeredity20261019.uniformizedKernel hG hLam hL).expect f x := by
  rw [expect_next, CTMCHeredity20261019.uniformizedKernel_expect]

/-- The same erasure identity directly in the normalized label PMF's weights. -/
theorem law_state_expect_eq_uniformizedKernel
    (C : HybridCTMC.Channels S R) {L Lam : ℝ}
    (hG : FunctionalCapacity.IsGen L C.rates.generator)
    (hLam : 0 < Lam) (hL : L ≤ Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (f : S → ℝ) (x : S) :
    (∑ m, (law C hLam bound x m).toReal * f (next C x m)) =
      (CTMCHeredity20261019.uniformizedKernel hG hLam hL).expect f x := by
  rw [← expect_eq_law_sum, expect_next_eq_uniformizedKernel]

/-- The source can equally be given by an already proved generator identity. -/
theorem expect_next_eq_source
    (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (G : (S → ℝ) → S → ℝ)
    (hsource : ∀ f x, C.rates.generator f x = G f x)
    (f : S → ℝ) (x : S) :
    expect C Lam x (fun m => f (next C x m)) = f x + G f x / Lam := by
  rw [expect_next, hsource]

end FiniteState
end
end CTMCHeredity20261019.MarkedUniformization
