module

public import proofs.CTMCHeredity20261019.PhysicalCutMeasurable
public import proofs.HybridCTMCInfrastructure.GeneratorIntegral

@[expose] public section

/-!
# Residual suffixes in the source continuous-time semantics

The clock-index and timed-state functions in this file are the original
HybridCTMC source definitions. The source segment characterization is reused;
no second clock index or sample-path definition is introduced. The residual
map is defined on every sequence, and its physical interpretation is proved
on sequences with unbounded arrivals at nonnegative physical times.
-/

namespace CTMCHeredity20261019

noncomputable section
open HybridCTMC.Kernel MeasureTheory ProbabilityTheory

variable {S : Type*}

/-- The source continuous-time clock on a residual suffix is exactly the
source clock at the translated physical time, with its event index shifted. -/
theorem physicalCut_clockIndex (w : ℕ → ℝ × S) (n : ℕ) (T u : ℝ)
    (hlo : arrivalTime n w ≤ T) (hhi : T < arrivalTime (n + 1) w)
    (hu : 0 ≤ u) (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    clockIndex u (physicalCut w n T) + n = clockIndex (T + u) w := by
  have hfuture := physicalCut_arrivals_unbounded w n T hhi hw
  have hsegment := clockIndex_segment hu (physicalCut w n T) (hfuture u)
  have hsource := (physicalCut_source_segment w n T u hlo hhi hu
    (clockIndex u (physicalCut w n T))).mp hsegment
  have hindex := clockIndex_eq_of_between w (n + clockIndex u (physicalCut w n T))
    hsource.1 hsource.2
  rw [hindex]
  exact Nat.add_comm _ _

/-- Equality of the actual source timed states on the full future time axis. -/
theorem physicalCut_timedState (w : ℕ → ℝ × S) (n : ℕ) (T u : ℝ)
    (hlo : arrivalTime n w ≤ T) (hhi : T < arrivalTime (n + 1) w)
    (hu : 0 ≤ u) (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    timedState u (physicalCut w n T) = timedState (T + u) w := by
  change (physicalCut w n T (clockIndex u (physicalCut w n T))).2 =
    (w (clockIndex (T + u) w)).2
  rw [physicalCut_state, ← physicalCut_clockIndex w n T u hlo hhi hu hw]
  congr 2
  exact Nat.add_comm _ _

/-- Cut at the actual source clock index at deterministic physical time T.
Coordinate zero is zero/current-state; the first future hold is residual. -/
def physicalTimedCut (T : ℝ) (w : ℕ → ℝ × S) : ℕ → ℝ × S :=
  physicalCut w (clockIndex T w) T

@[simp] theorem physicalTimedCut_zero (T : ℝ) (w : ℕ → ℝ × S) :
    physicalTimedCut T w 0 = (0, timedState T w) := rfl

@[simp] theorem physicalTimedCut_one (T : ℝ) (w : ℕ → ℝ × S) :
    physicalTimedCut T w 1 =
      (arrivalTime (clockIndex T w + 1) w - T, (w (clockIndex T w + 1)).2) := rfl

section Measurability

variable [MeasurableSpace S]

/-- Measurability of the actual physical-cut map uses countably many event
index cases and the source's existing measurable_clockIndex theorem. -/
theorem measurable_physicalTimedCut (T : ℝ) :
    Measurable (physicalTimedCut (S := S) T) := by
  have hm : Measurable (fun z : (ℕ → ℝ × S) × ℕ => physicalCut z.1 z.2 T) :=
    measurable_from_prod_countable_left (fun n => measurable_physicalCut n T)
  exact hm.comp (measurable_id.prodMk (measurable_clockIndex T))

end Measurability

theorem physicalTimedCut_clockIndex (w : ℕ → ℝ × S) (T u : ℝ)
    (hT : 0 ≤ T) (hu : 0 ≤ u)
    (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    clockIndex u (physicalTimedCut T w) + clockIndex T w = clockIndex (T + u) w := by
  have hs := clockIndex_segment hT w (hw T)
  exact physicalCut_clockIndex w (clockIndex T w) T u hs.1 hs.2 hu hw

theorem physicalTimedCut_timedState (w : ℕ → ℝ × S) (T u : ℝ)
    (hT : 0 ≤ T) (hu : 0 ≤ u)
    (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    timedState u (physicalTimedCut T w) = timedState (T + u) w := by
  have hs := clockIndex_segment hT w (hw T)
  exact physicalCut_timedState w (clockIndex T w) T u hs.1 hs.2 hu hw

/-- Source-level semigroup identity for residual suffixes, retaining every
future hold and state. This is deterministic composition, with no claim yet
about the conditional distribution of the composed maps. -/
theorem physicalTimedCut_compose (w : ℕ → ℝ × S) (T u : ℝ)
    (hT : 0 ≤ T) (hu : 0 ≤ u)
    (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    physicalTimedCut u (physicalTimedCut T w) = physicalTimedCut (T + u) w := by
  have hs := clockIndex_segment hT w (hw T)
  have hi : clockIndex T w + clockIndex u (physicalTimedCut T w) =
      clockIndex (T + u) w := by
    rw [Nat.add_comm]
    exact physicalTimedCut_clockIndex w T u hT hu hw
  change physicalCut (physicalCut w (clockIndex T w) T)
      (clockIndex u (physicalTimedCut T w)) u =
    physicalCut w (clockIndex (T + u) w) (T + u)
  rw [physicalCut_compose w (clockIndex T w) (clockIndex u (physicalTimedCut T w)) T u hs.2,
    hi]

/-- Physical cuts preserve the path support needed for further physical cuts. -/
theorem physicalTimedCut_regular (w : ℕ → ℝ × S) (T : ℝ) (hT : 0 ≤ T)
    (hp : ∀ k : ℕ, 0 < (w (k + 1)).1)
    (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    (∀ k : ℕ, 0 < (physicalTimedCut T w (k + 1)).1) ∧
      (∀ u : ℝ, ∃ k : ℕ, u < arrivalTime k (physicalTimedCut T w)) := by
  have hs := clockIndex_segment hT w (hw T)
  exact ⟨physicalCut_holding_pos w (clockIndex T w) T hs.2 hp,
    physicalCut_arrivals_unbounded w (clockIndex T w) T hs.2 hw⟩

section ActualLaw

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S]

theorem ae_physicalTimedCut_regular (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x,
      (∀ k : ℕ, 0 < (physicalTimedCut T w (k + 1)).1) ∧
      (∀ u : ℝ, ∃ k : ℕ, u < arrivalTime k (physicalTimedCut T w)) := by
  filter_upwards [K.ae_holding_pos hΛ x, ae_arrivals_unbounded K hΛ x] with w hp hw
  exact physicalTimedCut_regular w T hT hp hw

/-- One source-law full-measure set gives the actual timed-state identity
simultaneously at every future nonnegative physical time. -/
theorem ae_physicalTimedCut_timedState (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ u : ℝ, 0 ≤ u →
      timedState u (physicalTimedCut T w) = timedState (T + u) w := by
  filter_upwards [ae_arrivals_unbounded K hΛ x] with w hw
  intro u hu
  exact physicalTimedCut_timedState w T u hT hu hw

end ActualLaw

end

end CTMCHeredity20261019
