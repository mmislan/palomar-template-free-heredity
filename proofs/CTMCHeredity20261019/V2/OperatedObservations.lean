module

public import proofs.CTMCHeredity20261019.V2.ExecutedWindows
public import proofs.CTMCHeredity20261019.V2.PhysicalOperated
public import proofs.CTMCHeredity20261019.V2.MarkedCountTail

@[expose] public section

/-!
# Version 2: executed proposal counts on the actual joint operated history

Regular clocks suffice for deterministic stitching of the positive visited
lists. At every service boundary the old left endpoint is retained; the new
right coordinate-zero sentinel is omitted. Each recorded block therefore
contributes exactly its executed positive-prefix count, including labels
whose physical update is null. No auxiliary infinite segment tail is counted.

The support needed for this deterministic induction is then derived under
the actual completedLaw from the actual segment and terminal event laws.
Thus the sum of recorded division counts and the global stitched count are
equal jointly, rather than inferred from a marginal path-law identity.
This module does not assert local-to-global q/nd offset identities for every
window or identify either phase with a different common-clock construction.
-/

namespace CTMCHeredity20261019.V2.OperatedObservations

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift NoBoundaryArrival PhysicalSplice ExecutedWindows
open MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

section DeterministicClock

variable {S : Type*}

theorem prefixSplice_holding_pos (n : ℕ) (T : ℝ) (w v : Path S)
    (hlo : arrivalTime n w ≤ T)
    (hw : ∀ k : ℕ, 0 < (w (k + 1)).1)
    (hv : ∀ k : ℕ, 0 < (v (k + 1)).1) :
    ∀ k : ℕ, 0 < (prefixSplice n T (Preorder.frestrictLe n w, v) (k + 1)).1 := by
  intro k
  by_cases hk : k + 1 ≤ n
  · rw [prefixSplice_prefix n T _ v (k + 1) hk]
    exact hw k
  · by_cases he : k + 1 = n + 1
    · rw [he, prefixSplice_first, cutPrefixArrival_frestrict]
      have hp := hv 0
      dsimp only [Prod.fst]
      linarith
    · have hl : n + 1 < k + 1 := by omega
      rw [prefixSplice_later n T _ v (k + 1) hl]
      have hs : k + 1 - n = (k + 1 - n - 1) + 1 := by omega
      rw [hs]
      exact hv _

/-- A regular left clock and a regular fresh right clock give a regular
stitched clock. No condition on an unused segment tail is substituted for
the clock of the stitched future. -/
theorem splice_clockSupport (T : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ClockBoundarySupport ∅ w) (hv : ClockBoundarySupport ∅ v) :
    ClockBoundarySupport ∅ (splice T (w, v)) := by
  have hs := clockIndex_segment hT w (hw.2.1 T)
  refine ⟨prefixSplice_holding_pos (clockIndex T w) T w v hs.1 hw.1 hv.1, ?_, ?_⟩
  · intro R
    obtain ⟨k, hk⟩ := hv.2.1 (R - T)
    refine ⟨clockIndex T w + k + 1, ?_⟩
    change R < arrivalTime (clockIndex T w + k + 1)
      (prefixSplice (clockIndex T w) T (Preorder.frestrictLe (clockIndex T w) w, v))
    rw [prefixSplice_arrival_positive (clockIndex T w) T w v hs.1 (hv.1 0).le k]
    have ha := (arrivalTime_mono v) (Nat.le_succ k)
    linarith
  · intro k
    simp only [Set.mem_empty_iff_false, not_false_eq_true]

theorem selectedCount_zero (P : S → Prop) (w : Path S)
    (hw : 0 < (w 1).1) : selectedCount P 0 w = 0 := by
  have ha : 0 < arrivalTime 1 w := by
    simpa [arrivalTime, max_eq_right hw.le] using hw
  have hi := clockIndex_eq_of_between w 0 (by simp [arrivalTime]) ha
  simp only [selectedCount, timedHistory, hi, statePrefix_zero, List.tail_cons,
    countAll]

/-- The existing proposal-count observable inherits exact executed-list
concatenation. The right initial sentinel contributes no operation. -/
theorem splice_selectedCount (P : S → Prop) (T u : ℝ) (w v : Path S)
    (hT : 0 ≤ T) (hw : ∃ k : ℕ, T < arrivalTime k w)
    (hv : 0 ≤ (v 1).1) (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    selectedCount P (T + u) (splice T (w, v)) =
      selectedCount P T w + selectedCount P u v := by
  unfold selectedCount
  rw [splice_timedHistory_tail_after T u w v hT hw hv hu hex, countAll_append]

end DeterministicClock

section DeterministicHistory

/-- Clock regularity of the entire backward stitch follows by deterministic
induction on the clocks of its recorded segments and terminal tail. -/
theorem stitch_clockSupport (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (h : RawOperated.History p n) (v : MarkedPath p)
    (hh : ∀ i : Fin n, ClockBoundarySupport ∅ (h.1 i).1)
    (hv : ClockBoundarySupport ∅ v) :
    ClockBoundarySupport ∅ (PhysicalOperated.stitch p T n (h, v)) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
      have ht : ∀ i : Fin n, ClockBoundarySupport ∅ ((Operated.tail h).1 i).1 :=
        fun i => hh i.succ
      exact splice_clockSupport T (h.1 0).1
        (PhysicalOperated.stitch p T n (Operated.tail h, v)) hT (hh 0)
        (ih (Operated.tail h) ht)

/-- Pointwise all-block source observation theorem on explicitly regular
histories. It reads precisely the executed positive part of each block. -/
theorem stitch_selectedCount (p : Par) (P : CF3MarkedKernel.State p → Prop)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (h : RawOperated.History p n) (v : MarkedPath p)
    (hh : ∀ i : Fin n, ClockBoundarySupport ∅ (h.1 i).1)
    (hv : ClockBoundarySupport ∅ v) :
    selectedCount P ((n : ℝ) * T) (PhysicalOperated.stitch p T n (h, v)) =
      ∑ i : Fin n, selectedCount P T (h.1 i).1 := by
  induction n with
  | zero =>
      simpa [PhysicalOperated.stitch] using selectedCount_zero P v (hv.1 0)
  | succ n ih =>
      have ht : ∀ i : Fin n, ClockBoundarySupport ∅ ((Operated.tail h).1 i).1 :=
        fun i => hh i.succ
      have hr := stitch_clockSupport p T hT n (Operated.tail h) v ht hv
      have htime : ((n + 1 : ℕ) : ℝ) * T = T + (n : ℝ) * T := by
        push_cast
        ring
      change selectedCount P (((n + 1 : ℕ) : ℝ) * T)
        (splice T ((h.1 0).1, PhysicalOperated.stitch p T n (Operated.tail h, v))) = _
      rw [htime, splice_selectedCount P T ((n : ℝ) * T) (h.1 0).1
        (PhysicalOperated.stitch p T n (Operated.tail h, v)) hT ((hh 0).2.1 T)
        (hr.1 0).le (mul_nonneg (Nat.cast_nonneg n) hT) (hr.2.1 _),
        ih (Operated.tail h) ht, Fin.sum_univ_succ]
      rfl

theorem stitch_divisionCount (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (h : RawOperated.History p n) (v : MarkedPath p)
    (hh : ∀ i : Fin n, ClockBoundarySupport ∅ (h.1 i).1)
    (hv : ClockBoundarySupport ∅ v) :
    divisionCount p ((n : ℝ) * T) (PhysicalOperated.stitch p T n (h, v)) =
      rawHistoryDivisionCount p T n h :=
  stitch_selectedCount p divisionState T hT n h v hh hv

end DeterministicHistory

section ActualJointLaw

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

/-- Both the recorded clocks and the fresh terminal clock are regular under
the actual joint completed law, with arbitrary initial natural ledgers. -/
theorem completedLaw_ae_clockSupport {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      (∀ i : Fin n, ClockBoundarySupport ∅ (z.1.1 i).1) ∧
        ClockBoundarySupport ∅ z.2 := by
  have hm : MeasurableSet {w : MarkedPath p | ClockBoundarySupport ∅ w} :=
    measurableSet_clockBoundarySupport ∅ Set.countable_empty
  have hseg : MeasurableSet {h : RawOperated.History p n |
      ∀ i : Fin n, ClockBoundarySupport ∅ (h.1 i).1} :=
    RawOperated.measurableSet_allSegments (fun s => ClockBoundarySupport ∅ s.1)
      (hm.preimage measurable_fst) n
  have hjoint : MeasurableSet {z : RawOperated.History p n × MarkedPath p |
      (∀ i : Fin n, ClockBoundarySupport ∅ (z.1.1 i).1) ∧
        ClockBoundarySupport ∅ z.2} :=
    (hseg.preimage measurable_fst).inter (hm.preimage measurable_snd)
  change ∀ᵐ z ∂(RawOperated.rawLaw hp T n x).compProd
    (PhysicalOperated.terminalKernel hp n), _
  apply Measure.ae_compProd_of_ae_ae hjoint
  filter_upwards [RawOperated.rawLaw_ae_clocks hp T n x ∅ Set.countable_empty] with h hh
  have hv : ∀ᵐ v ∂PhysicalOperated.terminalKernel hp n h, ClockBoundarySupport ∅ v :=
    cf3_marked_ae_clockBoundarySupport hp (coreProject h.2) none ∅ Set.countable_empty
  filter_upwards [hv] with v hv
  exact ⟨fun i => (hh i).1, hv⟩

/-- The actual recorded division-count sum and actual stitched global count
are equal on the same completed history. This is stronger than a marginal
count-law identity and never counts an auxiliary infinite segment tail. -/
theorem completedLaw_ae_divisionCount {p : Par} (hp : p.Valid) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      rawHistoryDivisionCount p T n z.1 =
        divisionCount p ((n : ℝ) * T) (PhysicalOperated.stitch p T n z) := by
  filter_upwards [completedLaw_ae_clockSupport hp T n x] with z hz
  exact (stitch_divisionCount p T hT n z.1 z.2 hz.1 hz.2).symm

/-- Consequently the recorded total has the exact actual homogeneous source
count distribution at n*T. The underlying joint AE equality was proved first. -/
theorem completedLaw_recordedDivisionCount_law {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    (PhysicalOperated.completedLaw hp T n x).map
        (fun z => rawHistoryDivisionCount p T n z.1) =
      (CF3MarkedKernel.eventLaw hp (coreProject x) none).map
        (divisionCount p ((n : ℝ) * T)) := by
  calc
    _ = (PhysicalOperated.completedLaw hp T n x).map
        (fun z => divisionCount p ((n : ℝ) * T) (PhysicalOperated.stitch p T n z)) :=
      Measure.map_congr (completedLaw_ae_divisionCount hp T hT n x)
    _ = ((PhysicalOperated.completedLaw hp T n x).map (PhysicalOperated.stitch p T n)).map
        (divisionCount p ((n : ℝ) * T)) :=
      (Measure.map_map (measurable_divisionCount p ((n : ℝ) * T))
        (PhysicalOperated.measurable_stitch p T n)).symm
    _ = _ := by rw [PhysicalOperated.completedLaw_stitch hp T hT n x]

/-- Appending the actual normalized terminal law leaves the recorded joint
history marginal unchanged. -/
theorem completedLaw_fst {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    (PhysicalOperated.completedLaw hp T n x).map Prod.fst = RawOperated.rawLaw hp T n x := by
  exact Measure.fst_compProd (RawOperated.rawLaw hp T n x) (PhysicalOperated.terminalKernel hp n)

/-- The original operated-law count observable therefore has the exact
homogeneous physical source count law, without an auxiliary terminal path
in the public observable. -/
theorem rawLaw_recordedDivisionCount_law {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    (RawOperated.rawLaw hp T n x).map (rawHistoryDivisionCount p T n) =
      (CF3MarkedKernel.eventLaw hp (coreProject x) none).map
        (divisionCount p ((n : ℝ) * T)) := by
  calc
    _ = ((PhysicalOperated.completedLaw hp T n x).map Prod.fst).map
        (rawHistoryDivisionCount p T n) := by rw [completedLaw_fst]
    _ = (PhysicalOperated.completedLaw hp T n x).map
        (fun z => rawHistoryDivisionCount p T n z.1) :=
      Measure.map_map (measurable_rawHistoryDivisionCount p T n) measurable_fst
    _ = _ := completedLaw_recordedDivisionCount_law hp T hT n x

end ActualJointLaw

end
end CTMCHeredity20261019.V2.OperatedObservations
