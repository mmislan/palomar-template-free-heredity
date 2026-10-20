module

public import P161Formal.SourceFeedTail
public import P161Formal.SourceSeedTail
public import P161Formal.SourceGlobalObservations
public import P161Formal.Quantitative
public import proofs.CTMCHeredity20261019.V2.SwitchStockTail

/-! The four probability allowances are combined on one actual completed
switched law. This intermediate theorem still precedes the complete physical
resource observations and the absorbing finite-stock pushforward. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped BigOperators ENNReal Classical
noncomputable section

local instance idealMissionRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance idealMissionRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance idealMissionMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance idealMissionMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def idealResourceGood (h : TwoPhaseHistory) : Prop :=
  switchedFeedCount h ≤ 800000000 ∧ switchedSeedCount h ≤ 5000 ∧
    SwitchStockTail.totalDivisions h ≤ 1200

theorem measurableSet_idealResourceGood : MeasurableSet {h | idealResourceGood h} := by
  exact (measurableSet_le measurable_switchedFeedCount measurable_const).inter
    ((measurableSet_le measurable_switchedSeedCount measurable_const).inter
      (measurableSet_le SwitchStockTail.measurable_totalDivisions measurable_const))

theorem switched_resource_failure (x : Raw) :
    switchedLaw x {h | ¬idealResourceGood h} ≤ ENNReal.ofReal (3*Real.exp (-20)) := by
  have he : {h : TwoPhaseHistory | ¬idealResourceGood h} =
      {h | 800000000 < switchedFeedCount h} ∪
        ({h | 5000 < switchedSeedCount h} ∪ {h | 1200 < SwitchStockTail.totalDivisions h}) := by
    ext h
    simp only [idealResourceGood,Set.mem_union,Set.mem_ofPred_eq,not_and_or,not_le]
  rw [he]
  calc
    _ ≤ switchedLaw x {h | 800000000 < switchedFeedCount h}+
        (switchedLaw x {h | 5000 < switchedSeedCount h}+
          switchedLaw x {h | 1200 < SwitchStockTail.totalDivisions h}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-20))+
        (ENNReal.ofReal (Real.exp (-20))+ENNReal.ofReal (Real.exp (-20))) :=
      add_le_add (switched_feed_gt_800000000 x) (add_le_add (switched_seeds_gt_5000 x)
        (SwitchStockTail.switched_divisions_gt_1200 x))
    _ = _ := by
      rw [←ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),
        ←ENNReal.ofReal_add (Real.exp_nonneg _) (by positivity)]
      congr 1
      ring

theorem completed_resource_failure (x : Raw) :
    V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬idealResourceGood z.1} ≤
      ENNReal.ofReal (3*Real.exp (-20)) := by
  have hm := Measure.map_apply (μ := V4.TwoPhaseLaw.completedSwitchLaw x)
    measurable_fst measurableSet_idealResourceGood.compl
  rw [V4.TwoPhaseLaw.completedSwitchLaw_fst x] at hm
  exact hm.symm.le.trans (switched_resource_failure x)

def idealCandidateMission (x : Raw) (z : V4.TwoPhaseLaw.Completion) : Prop :=
  continuousEvent (globalRaw x z) ∧ globalRenewalMission x z ∧ idealResourceGood z.1

theorem ideal_candidate_failure_probability (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬idealCandidateMission x z} ≤
      ENNReal.ofReal failureCeiling := by
  have he : {z : V4.TwoPhaseLaw.Completion | ¬idealCandidateMission x z} =
      {z | ¬continuousEvent (globalRaw x z) ∨ ¬globalRenewalMission x z} ∪
        {z | ¬idealResourceGood z.1} := by
    ext z
    simp only [idealCandidateMission,Set.mem_union,Set.mem_ofPred_eq,not_and_or]
    tauto
  rw [he]
  calc
    _ ≤ V4.TwoPhaseLaw.completedSwitchLaw x
        {z | ¬continuousEvent (globalRaw x z) ∨ ¬globalRenewalMission x z}+
        V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬idealResourceGood z.1} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((9545923/9062500000 : ℝ)+11/100000+10*Real.exp (-8))+
        ENNReal.ofReal (3*Real.exp (-20)) :=
      add_le_add (g60_and_global_renewal_failure x hx) (completed_resource_failure x)
    _ = ENNReal.ofReal ((9545923/9062500000 : ℝ)+11/100000+10*Real.exp (-8)+3*Real.exp (-20)) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal complete_failure_arithmetic

end
end P161Formal
