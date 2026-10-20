module

public import P161Formal.SourceIdealMission

/-! Recorded resource counts equal the positive-index marks of the one global
physical path. Prefix caps therefore hold through60; unused segment futures,
coordinate-zero sentinels and the appended future after60 are excluded. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open V2.NoBoundaryArrival V2.PhysicalSplice V2.ExecutedWindows
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance stockObsRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stockObsRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance stockObsMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stockObsMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

theorem stitch_after_selectedCount (p : FunctionalCapacity.Par)
    (P : CF3MarkedKernel.State p → Prop) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (h : RawOperated.History p n) (v : MarkedPath p)
    (hh : ∀ i : Fin n, ClockBoundarySupport ∅ (h.1 i).1)
    (hv : ClockBoundarySupport ∅ v) (u : ℝ) (hu : 0 ≤ u) :
    selectedCount P ((n : ℝ)*T+u) (PhysicalOperated.stitch p T n (h,v)) =
      rawHistorySelectedCount p P T n h+selectedCount P u v := by
  induction n with
  | zero => simp [PhysicalOperated.stitch,rawHistorySelectedCount]
  | succ n ih =>
      have ht : ∀ i : Fin n, ClockBoundarySupport ∅ ((Operated.tail h).1 i).1 :=
        fun i => hh i.succ
      have hr := OperatedObservations.stitch_clockSupport p T hT n (Operated.tail h) v ht hv
      have htime : ((n+1 : ℕ) : ℝ)*T+u = T+((n : ℝ)*T+u) := by push_cast; ring
      change selectedCount P (((n+1 : ℕ) : ℝ)*T+u)
        (splice T ((h.1 0).1,PhysicalOperated.stitch p T n (Operated.tail h,v))) = _
      rw [htime,OperatedObservations.splice_selectedCount P T ((n : ℝ)*T+u) (h.1 0).1
        (PhysicalOperated.stitch p T n (Operated.tail h,v)) hT ((hh 0).2.1 T)
        (hr.1 0).le (add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT) hu) (hr.2.1 _),
        ih (Operated.tail h) ht]
      simp only [rawHistorySelectedCount,Fin.sum_univ_succ,Operated.tail]
      omega

set_option backward.isDefEq.respectTransparency false in
theorem whole_path_selected_count_sixty (z : V4.TwoPhaseLaw.Completion)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2)
    (P : CF3MarkedKernel.State canonicalSeedOnCF3 → Prop) :
    selectedCount P 60 (wholePath z) =
      rawHistorySelectedCount canonicalSeedOnCF3 P blockDuration 300 z.1.1+
        rawHistorySelectedCount seedOff P blockDuration 300 z.1.2 := by
  have hclock := offPath_clockSupport z hoff hv
  have hafter := stitch_after_selectedCount canonicalSeedOnCF3 P blockDuration
    blockDuration_nonneg 300 z.1.1 (offPath z) hon hclock 30 (by norm_num)
  have hoffCount := OperatedObservations.stitch_selectedCount seedOff P blockDuration
    blockDuration_nonneg 300 z.1.2 z.2 hoff hv
  have ht : ((300 : ℕ) : ℝ)*blockDuration = 30 := by norm_num [blockDuration]
  rw [ht] at hafter hoffCount
  change selectedCount P (30+30) (wholePath z) = _ at hafter
  norm_num only at hafter
  exact hafter.trans (congrArg (fun k => rawHistorySelectedCount canonicalSeedOnCF3 P blockDuration 300 z.1.1+k)
    hoffCount)

def globalFeedCount (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : ℕ :=
  selectedCount (sourceFeedState 6) t (wholePath z)

def globalSeedCount (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : ℕ :=
  selectedCount (sourceSeedState 6) t (wholePath z)

def globalDivisionCount (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : ℕ :=
  selectedCount divisionState t (wholePath z)

set_option backward.isDefEq.respectTransparency false in
theorem ae_global_resource_counts (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      globalFeedCount z 60 = switchedFeedCount z.1 ∧
      globalSeedCount z 60 = switchedSeedCount z.1 ∧
      globalDivisionCount z 60 = SwitchStockTail.totalDivisions z.1 := by
  filter_upwards [V4.TwoPhaseLaw.completedSwitchLaw_ae_clocks x] with z hz
  have hf := whole_path_selected_count_sixty z hz.1 hz.2.1 hz.2.2 (sourceFeedState 6)
  have hs := whole_path_selected_count_sixty z hz.1 hz.2.1 hz.2.2 (sourceSeedState 6)
  have hd := whole_path_selected_count_sixty z hz.1 hz.2.1 hz.2.2 divisionState
  have hfeed : sourceFeedState 6 = sourceFeedState 0 := by
    funext z
    rcases z with ⟨core,mark⟩
    cases mark with
    | none => rfl
    | some m =>
        cases m with
        | inr d => rfl
        | inl ik =>
            rcases ik with ⟨i,k⟩
            cases k with
            | inl tj => rfl
            | inr b => cases b <;> rfl
  have hseed : sourceSeedState 6 = sourceSeedState 0 := by
    funext z
    rcases z with ⟨core,mark⟩
    cases mark with
    | none => rfl
    | some m =>
        cases m with
        | inr d => rfl
        | inl ik =>
            rcases ik with ⟨i,k⟩
            cases k with
            | inl tj => rfl
            | inr b => cases b <;> rfl
  have hdiv : @divisionState canonicalSeedOnCF3 = @divisionState seedOff := by
    funext z
    rcases z with ⟨core,mark⟩
    cases mark with
    | none => rfl
    | some m => cases m <;> rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [globalFeedCount,switchedFeedCount,phaseFeedCount,hfeed,literal_seed_on_parameter,literal_seed_off_parameter,seedOff] using hf
  · simpa only [globalSeedCount,switchedSeedCount,phaseSeedCount,hseed,literal_seed_on_parameter,literal_seed_off_parameter,seedOff] using hs
  · simpa only [globalDivisionCount,SwitchStockTail.totalDivisions,rawHistoryDivisionCount,
      divisionCount,rawHistorySelectedCount,hdiv] using hd

theorem ae_global_resource_prefix_caps (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      idealResourceGood z.1 → ∀ t : ℝ, 0 ≤ t → t ≤ 60 →
        globalFeedCount z t ≤ 800000000 ∧ globalSeedCount z t ≤ 5000 ∧
          globalDivisionCount z t ≤ 1200 := by
  filter_upwards [ae_global_resource_counts x,V4.TwoPhaseLaw.completedSwitchLaw_ae_clocks x] with z hc hz
  have hclock := globalRaw_clockSupport z hz.1 hz.2.1 hz.2.2 x
  change ClockBoundarySupport ∅ (wholePath z) at hclock
  intro hg t ht ht60
  have ha : globalFeedCount z 60 ≤ 800000000 := by rw [hc.1]; exact hg.1
  have hs : globalSeedCount z 60 ≤ 5000 := by rw [hc.2.1]; exact hg.2.1
  have hd : globalDivisionCount z 60 ≤ 1200 := by rw [hc.2.2]; exact hg.2.2
  exact ⟨(selectedCount_mono_of_crosses (sourceFeedState 6) (wholePath z) ht ht60
      (hclock.2.1 60)).trans ha,
    (selectedCount_mono_of_crosses (sourceSeedState 6) (wholePath z) ht ht60
      (hclock.2.1 60)).trans hs,
    (selectedCount_mono_of_crosses divisionState (wholePath z) ht ht60
      (hclock.2.1 60)).trans hd⟩

end
end P161Formal
