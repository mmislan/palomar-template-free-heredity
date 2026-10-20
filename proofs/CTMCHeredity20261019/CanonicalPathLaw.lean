module

public import proofs.CTMCHeredity20261019.PhysicalCutGlobalLaw
public import proofs.CTMCHeredity20261019.CF3Capped
public import proofs.CTMCHeredity20261019.CopyingMeasure
public import proofs.CTMCHeredity20261019.QuotientTransfer

@[expose] public section

/-!
# Actual physical-future law for the canonical post-withdrawal CF3 source

The canonical parameters are the source's M=4, c=3, N=2048, alpha=800,
beta=4000000, epsilon=0 chemistry. The source generator bound is exactly
93515792. Generator validity, the clock bound, and the finite saturation
quotient are proved; no Markov or physical-future-law premise is supplied.

The physical path law here is the actual finite capped post-withdrawal source
law. It includes bounded chemical counts, fuel, and saturated output/division
ledgers. This module does not assert a raw unbounded-ledger path construction,
the switched finite-stock mission, or a reset protocol law.
-/

namespace CTMCHeredity20261019

noncomputable section
open FunctionalCapacity HybridCTMC.Kernel MeasureTheory
open scoped Classical ENNReal

theorem canonicalSeedFree_valid : canonicalSeedFreeCF3.Valid := by
  constructor <;> norm_num [canonicalSeedFreeCF3]

theorem canonicalSeedFree_rate : cf3Rate canonicalSeedFreeCF3 = 93515792 := by
  norm_num [cf3Rate, canonicalSeedFreeCF3]

theorem canonicalSeedFree_clock_pos : (0 : ℝ) < 93515792 := by norm_num

/-- The finite canonical source kernel, with its clock bound discharged from
the actual chemistry and every saturated ledger coordinate retained. -/
def canonicalCappedKernel (Q D : ℕ) : HybridCTMC.Kernel
    (CappedState canonicalSeedFreeCF3 Q D) :=
  uniformizedKernel (cappedGen_isGen canonicalSeedFree_valid Q D)
    canonicalSeedFree_clock_pos
    (show cf3Rate canonicalSeedFreeCF3 ≤ 93515792 by rw [canonicalSeedFree_rate])

/-- Exact finite-source uniformization for every capped observable, starting
from the projection of arbitrary original source output/division ledgers. -/
theorem canonical_capped_source_expect (Q D : ℕ)
    (f : CappedState canonicalSeedFreeCF3 Q D → ℝ)
    (x : CappedSource canonicalSeedFreeCF3) :
    (canonicalCappedKernel Q D).expect f (capProject Q D x) =
      f (capProject Q D x) + cf3Gen canonicalSeedFreeCF3
        (fun y => f (capProject Q D y)) x / 93515792 := by
  rw [canonicalCappedKernel, uniformizedKernel_expect, cf3Gen_capped_lump]

section PhysicalLaw

variable (Q D : ℕ)
  [MeasurableSpace (CappedState canonicalSeedFreeCF3 Q D)]
  [MeasurableSingletonClass (CappedState canonicalSeedFreeCF3 Q D)]
  [StandardBorelSpace (CappedState canonicalSeedFreeCF3 Q D)]

/-- Exact whole-future law of the actual canonical capped chemistry at its
proved physical clock rate. The fresh path mixture is indexed by the actual
canonical source state at time T. -/
theorem canonical_capped_physical_future_law
    (x : CappedSource canonicalSeedFreeCF3) (T : ℝ) (hT : 0 ≤ T) :
    ((canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos
      (capProject Q D x)).map (physicalTimedCut T) =
    (((canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos
      (capProject Q D x)).map (timedState T)).bind
        (fun y => (canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos y) :=
  eventLaw_physicalTimedCut_map (canonicalCappedKernel Q D)
    canonicalSeedFree_clock_pos (capProject Q D x) T hT

/-- The canonical whole-future theorem in nonnegative reward form, with an
arbitrary measurable observable of the entire future holding/state sequence. -/
theorem canonical_capped_physical_future_reward
    (x : CappedSource canonicalSeedFreeCF3) (T : ℝ) (hT : 0 ≤ T)
    (F : (ℕ → ℝ × CappedState canonicalSeedFreeCF3 Q D) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (physicalTimedCut T w)
      ∂(canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos (capProject Q D x)) =
    ∫⁻ w, (∫⁻ v, F v ∂(canonicalCappedKernel Q D).eventLaw 93515792
        canonicalSeedFree_clock_pos (timedState T w))
      ∂(canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos (capProject Q D x) :=
  eventLaw_physicalTimedCut_fresh_reward (canonicalCappedKernel Q D)
    canonicalSeedFree_clock_pos (capProject Q D x) T hT F hF

/-- The actual canonical capped source clock crosses every finite real
horizon on one full-measure set. This is derived from its constructed law. -/
theorem ae_canonical_capped_unbounded_clock (x : CappedSource canonicalSeedFreeCF3) :
    ∀ᵐ w ∂(canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos
      (capProject Q D x), ∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n w :=
  ae_arrivals_unbounded (canonicalCappedKernel Q D)
    canonicalSeedFree_clock_pos (capProject Q D x)

/-- The residual sequence in the canonical whole-future law has exactly the
source's future timed states, simultaneously at all nonnegative future times. -/
theorem ae_canonical_capped_physical_future_state
    (x : CappedSource canonicalSeedFreeCF3) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ w ∂(canonicalCappedKernel Q D).eventLaw 93515792 canonicalSeedFree_clock_pos
      (capProject Q D x), ∀ u : ℝ, 0 ≤ u →
        timedState u (physicalTimedCut T w) = timedState (T + u) w :=
  ae_physicalTimedCut_timedState (canonicalCappedKernel Q D)
    canonicalSeedFree_clock_pos (capProject Q D x) T hT

end PhysicalLaw

end

end CTMCHeredity20261019
