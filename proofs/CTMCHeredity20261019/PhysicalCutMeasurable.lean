module

public import proofs.CTMCHeredity20261019.PhysicalCut
public import proofs.HybridCTMCInfrastructure.ClockInitial

@[expose] public section

/-!
# Measurability and regularity of the actual residual suffix

The measurable maps below are the deterministic `physicalCut` of the source
holding-time/state sequence. They therefore support `Measure.map` without a
new law or any conditional-law bridge assumption. The only additional source
import beyond PhysicalCut's EventArrival closure is ClockInitial, already used
for almost-sure positivity of the actual source holding times.
-/

namespace CTMCHeredity20261019

noncomputable section
open MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open scoped BigOperators

variable {S : Type*}

section Measurability

variable [MeasurableSpace S]

private theorem measurable_physicalCut_arrival (n : ℕ) :
    Measurable (fun w : ℕ → ℝ × S => arrivalTime n w) :=
  (measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl

/-- Joint measurability in the deterministic physical cut time and the entire
source sequence, with the event index n fixed. -/
theorem measurable_physicalCut_joint (n : ℕ) :
    Measurable (fun z : ℝ × (ℕ → ℝ × S) => physicalCut z.2 n z.1) := by
  apply measurable_pi_iff.mpr
  intro k
  cases k with
  | zero =>
      have hs : Measurable (fun z : ℝ × (ℕ → ℝ × S) => (z.2 n).2) :=
        ((measurable_pi_apply (X := fun _ : ℕ => ℝ × S) n).comp measurable_snd).snd
      simpa only [physicalCut_zero] using
        (show Measurable (fun _ : ℝ × (ℕ → ℝ × S) => (0 : ℝ)) from measurable_const).prodMk hs
  | succ k =>
      cases k with
      | zero =>
          have ha : Measurable (fun z : ℝ × (ℕ → ℝ × S) => arrivalTime (n + 1) z.2) :=
            (measurable_physicalCut_arrival (S := S) (n + 1)).comp measurable_snd
          have hs : Measurable (fun z : ℝ × (ℕ → ℝ × S) => (z.2 (n + 1)).2) :=
            ((measurable_pi_apply (X := fun _ : ℕ => ℝ × S)
              (n + 1)).comp measurable_snd).snd
          simpa only [Nat.zero_add, physicalCut_one, Pi.sub_apply] using
            (ha.sub measurable_fst).prodMk hs
      | succ k =>
          simpa only [physicalCut_later, Function.comp_def] using
            (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (n + k + 2)).comp measurable_snd

/-- The exact future-sequence map at a fixed physical cut time is measurable. -/
theorem measurable_physicalCut (n : ℕ) (T : ℝ) :
    Measurable (fun w : ℕ → ℝ × S => physicalCut w n T) := by
  exact (measurable_physicalCut_joint (S := S) n).comp
    (measurable_const.prodMk measurable_id)

/-- The ordinary source between-arrival event used to select a cut index is
measurable. This uses the existing measurable arrival-time theorem directly. -/
theorem measurableSet_physicalCut_segment (n : ℕ) (T : ℝ) :
    MeasurableSet {w : ℕ → ℝ × S | arrivalTime n w ≤ T ∧
      T < arrivalTime (n + 1) w} :=
  (measurableSet_le (measurable_physicalCut_arrival n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_physicalCut_arrival (n + 1)))

end Measurability

/-- Unbounded arrivals transfer through the actual residual suffix. The local
finite-sum comparison avoids importing the wider ClockInterpolation module
merely to use its monotonicity lemma. -/
theorem physicalCut_arrivals_unbounded (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ)
    (hhi : T < arrivalTime (n + 1) w)
    (hw : ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w) :
    ∀ u : ℝ, ∃ k : ℕ, u < arrivalTime k (physicalCut w n T) := by
  intro u
  obtain ⟨m, hm⟩ := hw (T + u)
  refine ⟨m + 1, ?_⟩
  rw [physicalCut_arrival w n T hhi m]
  have hbound : arrivalTime m w ≤ arrivalTime (n + m + 1) w := by
    unfold arrivalTime
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono
      exact (Nat.le_add_left m n).trans (Nat.le_succ (n + m))
    · intro i _ _
      exact le_max_left 0 (w (i + 1)).1
  linarith

section ActualLaw

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S]

/-- The constructed source event law has one full-measure set on which the
arrivals cross every real horizon. Countably many natural horizons suffice. -/
theorem ae_arrivals_unbounded (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ t : ℝ, ∃ m : ℕ, t < arrivalTime m w := by
  have hn : ∀ᵐ w ∂K.eventLaw Λ hΛ x,
      ∀ k : ℕ, ∃ m : ℕ, (k : ℝ) < arrivalTime m w := by
    rw [ae_all_iff]
    intro k
    exact K.ae_arrival_crosses hΛ x (k : ℝ)
  filter_upwards [hn] with w hw
  intro t
  obtain ⟨k, hk⟩ := exists_nat_gt t
  obtain ⟨m, hm⟩ := hw k
  exact ⟨m, hk.trans hm⟩

/-- On the actual source law, every valid deterministic-index residual cut
retains positive future holds and unbounded future arrivals. This is a support
property of a measurable map, with no assertion about its conditional law. -/
theorem ae_physicalCut_regular (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (n : ℕ) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, T < arrivalTime (n + 1) w →
      (∀ k : ℕ, 0 < (physicalCut w n T (k + 1)).1) ∧
      (∀ u : ℝ, ∃ k : ℕ, u < arrivalTime k (physicalCut w n T)) := by
  filter_upwards [K.ae_holding_pos hΛ x, ae_arrivals_unbounded K hΛ x] with w hp hw
  intro hhi
  exact ⟨physicalCut_holding_pos w n T hhi hp,
    physicalCut_arrivals_unbounded w n T hhi hw⟩

end ActualLaw

end

end CTMCHeredity20261019
