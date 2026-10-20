module

public import proofs.CTMCHeredity20261019.V2.RecoveryStops
public import proofs.CTMCHeredity20261019.V2.NoBoundaryArrival
public import proofs.HybridCTMCInfrastructure.GeneratorIntegral

@[expose] public section

/-!
# V2: physical meaning of the actual first Ready512 event-index stop

Positive holds identify every finite event state with the right-continuous
physical state at its arrival. Unbounded arrivals give all nonnegative times
their ordinary between-arrivals semantics. These support properties are proved
almost surely for the actual marked reconstruction and raw lift, rather than
supplied as recovery assumptions.

The selected stop is current-population Ready512, including an immediate time
zero hit. No recovery probability, deadline, quantitative tail, executed-window
stitching, seed switch, or mission conclusion is asserted.
-/

namespace CTMCHeredity20261019.V2.PhysicalRecoveryStops

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift RawStoppedFuture RecoveryStops
open scoped BigOperators ENNReal Classical

section Deterministic

variable {S : Type*}

def firstIndex (P : S → Prop) (v : ℕ → ℝ × S) (n : ℕ) : Prop :=
  P (v n).2 ∧ ∀ m : ℕ, m < n → ¬ P (v m).2

def firstPhysicalHit (P : S → Prop) (v : ℕ → ℝ × S) (T : ℝ) : Prop :=
  0 ≤ T ∧ P (timedState T v) ∧ ∀ t : ℝ, 0 ≤ t → t < T → ¬ P (timedState t v)

theorem positive_holds_arrival_strictMono (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1) : StrictMono (fun n => arrivalTime n v) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs : arrivalTime (n + 1) v = arrivalTime n v + max 0 (v (n + 1)).1 := by
    simp only [arrivalTime, Finset.sum_range_succ]
  have hm : 0 < max 0 (v (n + 1)).1 := (hpos n).trans_le (le_max_right _ _)
  rw [hs]
  linarith

/-- Pointwise source semantics on the half-open physical interval, including
its left endpoint. No stochastic or regularity premise is needed locally. -/
theorem timedState_eq_on_segment (v : ℕ → ℝ × S) (n : ℕ) {t : ℝ}
    (hlo : arrivalTime n v ≤ t) (hhi : t < arrivalTime (n + 1) v) :
    timedState t v = (v n).2 := by
  change (v (clockIndex t v)).2 = (v n).2
  rw [clockIndex_eq_of_between v n hlo hhi]

theorem timedState_at_arrival (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1) (n : ℕ) :
    timedState (arrivalTime n v) v = (v n).2 :=
  timedState_eq_on_segment v n le_rfl
    ((positive_holds_arrival_strictMono v hpos) (Nat.lt_succ_self n))

/-- Exact finite-arrival first-hit equivalence. Positive holds alone suffice:
every earlier time is crossed by the displayed finite arrival itself. -/
theorem firstIndex_iff_physical_arrival (P : S → Prop) (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1) (n : ℕ) :
    firstIndex P v n ↔ firstPhysicalHit P v (arrivalTime n v) := by
  constructor
  · rintro ⟨hn, hprev⟩
    refine ⟨arrivalTime_nonneg n v, ?_, ?_⟩
    · rw [timedState_at_arrival v hpos n]
      exact hn
    · intro t ht htn
      have hs := clockIndex_segment ht v ⟨n, htn⟩
      have hi : clockIndex t v < n := by
        by_contra h
        have hni : n ≤ clockIndex t v := Nat.le_of_not_gt h
        have hm := (arrivalTime_mono v) hni
        linarith [hs.1]
      exact hprev (clockIndex t v) hi
  · rintro ⟨_, hn, hprev⟩
    refine ⟨?_, ?_⟩
    · rw [timedState_at_arrival v hpos n] at hn
      exact hn
    · intro m hm
      have hh := hprev (arrivalTime m v) (arrivalTime_nonneg m v)
        ((positive_holds_arrival_strictMono v hpos) hm)
      rw [timedState_at_arrival v hpos m] at hh
      exact hh

/-- With the genuine nonexplosive clock support, every physical first hit is
attained at an actual arrival. No assertion that such a hit exists is made. -/
theorem physical_firstHit_iff (P : S → Prop) (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < arrivalTime n v) (T : ℝ) :
    firstPhysicalHit P v T ↔ ∃ n : ℕ, T = arrivalTime n v ∧ firstIndex P v n := by
  constructor
  · intro hT
    let n := clockIndex T v
    have hs := clockIndex_segment hT.1 v (hunbounded T)
    have he : arrivalTime n v = T := by
      apply le_antisymm hs.1
      by_contra h
      have hlt : arrivalTime n v < T := lt_of_not_ge h
      have hbad := hT.2.2 (arrivalTime n v) (arrivalTime_nonneg n v) hlt
      rw [timedState_at_arrival v hpos n] at hbad
      exact hbad hT.2.1
    refine ⟨n, he.symm, ?_⟩
    apply (firstIndex_iff_physical_arrival P v hpos n).mpr
    rw [he]
    exact hT
  · rintro ⟨n, rfl, hn⟩
    exact (firstIndex_iff_physical_arrival P v hpos n).mp hn

theorem has_firstIndex_iff (P : S → Prop) (v : ℕ → ℝ × S) :
    (∃ n : ℕ, firstIndex P v n) ↔ ∃ n : ℕ, P (v n).2 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · intro h
    exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

/-- Literal nonhitting at all nonnegative physical times is equivalent to
absence of an event-index first hit. No eventual hit is postulated. -/
theorem no_firstIndex_iff_physical_nonhit (P : S → Prop) (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1) :
    (¬ ∃ n : ℕ, firstIndex P v n) ↔ ∀ t : ℝ, 0 ≤ t → ¬ P (timedState t v) := by
  rw [has_firstIndex_iff]
  constructor
  · intro h t _ ht
    exact h ⟨clockIndex t v, ht⟩
  · intro h ⟨n, hn⟩
    have hh := h (arrivalTime n v) (arrivalTime_nonneg n v)
    rw [timedState_at_arrival v hpos n] at hh
    exact hh hn

theorem firstPhysicalHit_zero_iff (P : S → Prop) (v : ℕ → ℝ × S)
    (hpos : ∀ n : ℕ, 0 < (v (n + 1)).1) :
    firstPhysicalHit P v 0 ↔ P (v 0).2 := by
  have he := firstIndex_iff_physical_arrival P v hpos 0
  have hz : arrivalTime 0 v = 0 := by simp [arrivalTime]
  rw [hz] at he
  exact he.symm.trans (by simp [firstIndex])

end Deterministic

section ActualSource

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

def firstReady512Physical {p : Par} (v : RawPath p) (T : ℝ) : Prop :=
  firstPhysicalHit rawReady512 v T

/-- Deterministic literal raw source bridge under explicit positive holds. -/
theorem raw_firstReady512_iff_physical (p : Par) (x : SourceState p) (w : MarkedPath p)
    (hpos : ∀ n : ℕ, 0 < (rawSequence p x w (n + 1)).1) (n : ℕ) :
    firstReady512Raw p x w n ↔
      firstReady512Physical (rawSequence p x w) (arrivalTime n w) := by
  have he := firstIndex_iff_physical_arrival rawReady512 (rawSequence p x w) hpos n
  rw [rawSequence_arrivalTime] at he
  exact he

/-- The actual marked law discharges support and observable-prefix coherence
simultaneously, at every possible first-hit index. -/
theorem ae_firstReady512_prefix_physical {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old, ∀ n : ℕ,
      (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈
        firstReady512Slices p n ↔
        firstReady512Physical (rawSequence p x w) (arrivalTime n w)) := by
  filter_upwards [ae_firstReady512_raw hp x old, ae_rawSequence_clock_regular hp x old] with w hready hclock
  intro n
  exact (hready n).trans (raw_firstReady512_iff_physical p x w hclock.1 n)

theorem ae_firstReady512_initial_physical {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (firstReady512Physical (rawSequence p x w) 0 ↔ rawReady512 x) := by
  filter_upwards [ae_rawSequence_clock_regular hp x old, ae_rawSequence_initial hp x old] with w hclock hzero
  have he := firstPhysicalHit_zero_iff rawReady512 (rawSequence p x w) hclock.1
  rw [hzero] at he
  exact he

theorem ae_physical_firstReady512_is_arrival {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old, ∀ T : ℝ,
      (firstReady512Physical (rawSequence p x w) T ↔
        ∃ n : ℕ, T = arrivalTime n w ∧ firstReady512Raw p x w n) := by
  filter_upwards [ae_rawSequence_clock_regular hp x old] with w hclock
  intro T
  have he := physical_firstHit_iff rawReady512 (rawSequence p x w) hclock.1 hclock.2 T
  change firstReady512Physical (rawSequence p x w) T ↔
    ∃ n : ℕ, T = arrivalTime n (rawSequence p x w) ∧ firstReady512Raw p x w n at he
  simpa only [rawSequence_arrivalTime] using he

/-- Actual observable-slice nonhitting is literal absence of Ready512 at
every nonnegative physical time, including the time-zero state. -/
theorem ae_firstReady512_nonhit_physical {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (w ∉ eventIndexHitEvent (firstReady512Slices p) ↔
        ∀ T : ℝ, 0 ≤ T → ¬ rawReady512 (timedState T (rawSequence p x w))) := by
  filter_upwards [ae_firstReady512_hit hp x old, ae_rawSequence_clock_regular hp x old] with w hready hclock
  exact (not_congr hready).trans
    (no_firstIndex_iff_physical_nonhit rawReady512 (rawSequence p x w) hclock.1)

/-- The exact stopped mass retains every physical nonhit path. This is a
source-law identity, without an eventual-recovery assumption. -/
theorem firstReady512_physical_nonhit_mass {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    rawStoppedSource hp x old (firstReady512Slices p) Set.univ +
      CF3MarkedKernel.eventLaw hp (coreProject x) old
        {w | ∀ T : ℝ, 0 ≤ T → ¬ rawReady512 (timedState T (rawSequence p x w))} = 1 := by
  have he : CF3MarkedKernel.eventLaw hp (coreProject x) old
      (eventIndexHitEvent (firstReady512Slices p))ᶜ =
        CF3MarkedKernel.eventLaw hp (coreProject x) old
          {w | ∀ T : ℝ, 0 ≤ T → ¬ rawReady512 (timedState T (rawSequence p x w))} := by
    apply measure_congr
    filter_upwards [ae_firstReady512_nonhit_physical hp x old] with w hw
    exact propext hw
  rw [← he]
  exact raw_stopped_nonhit_mass hp x old (firstReady512Slices p)
    (measurableSet_firstReady512Slices p) (firstReady512Slices_disjoint p)

/-- The actual raw pushforward law supplies both genuine clock properties.
The existing countably measurable support theorem is reused with no boundary
set, so no new raw nonexplosion premise is introduced. -/
theorem ae_rawLift_clock_regular {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old,
      (∀ n : ℕ, 0 < (v (n + 1)).1) ∧
      (∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n v) := by
  filter_upwards [NoBoundaryArrival.cf3_rawLiftLaw_ae_clockBoundarySupport hp x old
    ∅ Set.countable_empty] with v hv
  exact ⟨hv.1, hv.2.1⟩

theorem ae_rawLift_initial {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old, v 0 = (0, x) := by
  unfold rawLiftLaw
  apply (ae_map_iff (measurable_rawSequence p x).aemeasurable
    (show MeasurableSet {v : RawPath p | v 0 = (0, x)} from
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) 0)
        (measurableSet_singleton (0, x)))).mpr
  exact ae_rawSequence_initial hp x old

/-- The physical-arrival interpretation also holds directly under the
constructed raw path measure, retaining its natural-valued q/nd coordinates. -/
theorem ae_rawLift_firstReady512_physical {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old, ∀ n : ℕ,
      (firstIndex rawReady512 v n ↔ firstReady512Physical v (arrivalTime n v)) := by
  filter_upwards [ae_rawLift_clock_regular hp x old] with v hv
  intro n
  exact firstIndex_iff_physical_arrival rawReady512 v hv.1 n

theorem ae_rawLift_firstReady512_initial_physical {p : Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old, (firstReady512Physical v 0 ↔ rawReady512 x) := by
  filter_upwards [ae_rawLift_clock_regular hp x old, ae_rawLift_initial hp x old]
    with v hv hzero
  have he := firstPhysicalHit_zero_iff rawReady512 v hv.1
  rw [hzero] at he
  exact he

theorem ae_rawLift_physical_firstReady512_is_arrival {p : Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old, ∀ T : ℝ,
      (firstReady512Physical v T ↔
        ∃ n : ℕ, T = arrivalTime n v ∧ firstIndex rawReady512 v n) := by
  filter_upwards [ae_rawLift_clock_regular hp x old] with v hv
  intro T
  exact physical_firstHit_iff rawReady512 v hv.1 hv.2 T

theorem ae_rawLift_firstReady512_nonhit_physical {p : Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) :
    ∀ᵐ v ∂rawLiftLaw hp x old,
      ((¬ ∃ n : ℕ, firstIndex rawReady512 v n) ↔
        ∀ T : ℝ, 0 ≤ T → ¬ rawReady512 (timedState T v)) := by
  filter_upwards [ae_rawLift_clock_regular hp x old] with v hv
  exact no_firstIndex_iff_physical_nonhit rawReady512 v hv.1

end ActualSource

end
end CTMCHeredity20261019.V2.PhysicalRecoveryStops
