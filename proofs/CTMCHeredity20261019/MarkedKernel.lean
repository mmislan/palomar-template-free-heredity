module

public import proofs.CTMCHeredity20261019.MarkedUniformization
public import proofs.HybridCTMCInfrastructure.EventInvariant

@[expose] public section

/-!
# A finite state/last-mark kernel and its actual exponential-clock path law

The normalized proposal law has already been constructed from channel rates.
Here a step from `(x, oldMark)` samples its new mark `m` and installs exactly
`(next C x m, m)`. The old mark has no influence on the next proposal.
Actual state-null operations remain marked; `none` is the explicit idle label.

The timed law is the existing exponential-clock `eventLaw` of this constructed
finite kernel. Its almost-everywhere adjacent-update consistency is proved from
positive transition support. No whole-path projection identity or arbitrary
stopping-time bridge is assumed. Raw CF3 ledger reconstruction remains separate.
-/

namespace CTMCHeredity20261019.MarkedKernel

open MeasureTheory
open scoped BigOperators Classical
noncomputable section

variable {S R : Type} [Fintype S] [Fintype R]

/-- A finite kernel retaining the new proposal label alongside its actual update. -/
def kernel (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) :
    HybridCTMC.Kernel (S × Option R) where
  weight z y :=
    if y.1 = MarkedUniformization.next C z.1 y.2
    then MarkedUniformization.weight C Lam z.1 y.2 else 0
  nonneg z y := by
    split_ifs
    · exact MarkedUniformization.weight_nonneg C hLam bound z.1 y.2
    · exact le_refl 0
  total z := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      _ = ∑ m : Option R, MarkedUniformization.weight C Lam z.1 m := by
        apply Finset.sum_congr rfl
        intro m _
        simp
      _ = 1 := MarkedUniformization.weight_sum C Lam z.1

/-- The complete next-state/mark expectation under the constructed finite kernel. -/
theorem kernel_expect (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (g : S × Option R → ℝ) (z : S × Option R) :
    (kernel C hLam bound).expect g z =
      MarkedUniformization.expect C Lam z.1
        (fun m => g (MarkedUniformization.next C z.1 m, m)) := by
  change (∑ y : S × Option R,
    (if y.1 = MarkedUniformization.next C z.1 y.2
      then MarkedUniformization.weight C Lam z.1 y.2 else 0) * g y) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold MarkedUniformization.expect
  apply Finset.sum_congr rfl
  intro m _
  simp [ite_mul]

/-- Erasing the sampled label in an observable recovers the actual proposal law. -/
theorem kernel_expect_state (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (f : S → ℝ) (z : S × Option R) :
    (kernel C hLam bound).expect (fun y => f y.1) z =
      MarkedUniformization.expect C Lam z.1
        (fun m => f (MarkedUniformization.next C z.1 m)) := by
  exact kernel_expect C hLam bound (fun y => f y.1) z

/-- The last-mark expectation is precisely the actual normalized proposal law. -/
theorem kernel_expect_mark (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (g : Option R → ℝ) (z : S × Option R) :
    (kernel C hLam bound).expect (fun y => g y.2) z =
      MarkedUniformization.expect C Lam z.1 g := by
  exact kernel_expect C hLam bound (fun y => g y.2) z

/-- Equality of actual one-step PMFs after projecting to the sampled mark. -/
theorem kernel_pmf_mark (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (z : S × Option R) :
    ((kernel C hLam bound).pmf z).map Prod.snd =
      MarkedUniformization.law C hLam bound z.1 := by
  apply PMF.ext
  intro m
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  cases m <;> simp [HybridCTMC.Kernel.pmf, kernel, MarkedUniformization.law_apply, apply_ite]

/-- The physical observable agrees with the independently reconstructed finite
uniformization, proved on every observable rather than supplied as a bridge. -/
theorem kernel_expect_state_eq_uniformizedKernel [DecidableEq S]
    (C : HybridCTMC.Channels S R) {L Lam : ℝ}
    (hG : FunctionalCapacity.IsGen L C.rates.generator)
    (hLam : 0 < Lam) (hL : L ≤ Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (f : S → ℝ) (z : S × Option R) :
    (kernel C hLam bound).expect (fun y => f y.1) z =
      (uniformizedKernel hG hLam hL).expect f z.1 := by
  rw [kernel_expect_state, MarkedUniformization.expect_next_eq_uniformizedKernel]

/-- A positive-probability transition must install the state prescribed by its
own sampled mark. This is derived from the actual kernel definition. -/
theorem positive_weight_update (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (z y : S × Option R) (hy : 0 < (kernel C hLam bound).weight z y) :
    y.1 = MarkedUniformization.next C z.1 y.2 := by
  by_contra h
  have hz : (kernel C hLam bound).weight z y = 0 := by simp [kernel, h]
  rw [hz] at hy
  exact (lt_irrefl 0 hy)

section Timed

variable [MeasurableSpace (S × Option R)] [MeasurableSingletonClass (S × Option R)]

/-- The existing constructed exponential-clock law is almost surely consistent
at every adjacent proposal, including idle proposals and actual state-null ones. -/
theorem ae_event_adjacent_update (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (z : S × Option R) :
    ∀ᵐ w ∂(kernel C hLam bound).eventLaw Lam hLam z,
      ∀ n : ℕ, (w (n + 1)).2.1 =
        MarkedUniformization.next C (w n).2.1 (w (n + 1)).2.2 := by
  exact (kernel C hLam bound).ae_event_relation hLam z
    (fun a b => b.1 = MarkedUniformization.next C a.1 b.2)
    (fun a b h => positive_weight_update C hLam bound a b h)

end Timed
end
end CTMCHeredity20261019.MarkedKernel
