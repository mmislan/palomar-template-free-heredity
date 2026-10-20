module

public import P161Formal.SourceRenewalAudit
public import P161Formal.G60ActualProbability

/-! Unconditional integration of the whole seed-free renewal future inside
the actual V4 switched completion law. The entire seeded past is retained;
no successful history, reset resource stock or independent phase is assumed. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019 CF3Marked CF3RawPathLift
open V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped ENNReal Classical
noncomputable section

local instance renewalSwitchRawMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (SourceState p) := ⊤
local instance renewalSwitchRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance renewalSwitchMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance renewalSwitchMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

local instance renewalSwitchRecoveryMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalSwitchRecoveryMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

theorem completed_switch_off_joint_reward (x : Raw)
    (F : PhaseHistory × RecoveryPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,offPath z) ∂V4.TwoPhaseLaw.completedSwitchLaw x) =
      ∫⁻ a, ∫⁻ w, F (a,w)
        ∂CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject (sourceResetAll a.2)) none
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
  let H : TwoPhaseHistory → ℝ≥0∞ := fun h =>
    ∫⁻ v, F (h.1,offPath (h,v)) ∂V4.TwoPhaseLaw.terminalKernel h
  have hG : Measurable (fun z : V4.TwoPhaseLaw.Completion => F (z.1.1,offPath z)) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_offPath)
  have hH : Measurable H := hG.lintegral_kernel_prod_right'
  calc
    _ = ∫⁻ h, H h ∂switchedLaw x := Measure.lintegral_compProd hG
    _ = ∫⁻ a, ∫⁻ b, H (a,b)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      switchedLaw_lintegral x H hH
    _ = _ := by
      apply lintegral_congr
      intro a
      change (∫⁻ b, PhysicalOperated.completionValue canonicalSeedFree_valid blockDuration 300
        (fun w => F (a,w)) b
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)) = _
      exact PhysicalOperated.rawLaw_stitch_value canonicalSeedFree_valid blockDuration
        (by norm_num [blockDuration]) 300 (sourceResetAll a.2) (fun w => F (a,w))
        (hF.comp (measurable_const.prodMk measurable_id))

set_option backward.isDefEq.respectTransparency false in
theorem completed_switch_off_event_bound (x : Raw) (B : Set RecoveryPath)
    (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hbound : ∀ y : RecoveryCore, CF3MarkedKernel.eventLaw recoveryValid y none B ≤ c) :
    V4.TwoPhaseLaw.completedSwitchLaw x (offPath ⁻¹' B) ≤ c := by
  let f : RecoveryPath → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  calc
    _ = ∫⁻ z, f (offPath z) ∂V4.TwoPhaseLaw.completedSwitchLaw x := by
      rw [←lintegral_indicator_one (hB.preimage measurable_offPath)]
      rfl
    _ = ∫⁻ a, ∫⁻ w, f w
        ∂CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject (sourceResetAll a.2)) none
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      completed_switch_off_joint_reward x (fun z => f z.2) (hf.comp measurable_snd)
    _ ≤ ∫⁻ _a, c ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_mono
      intro a
      let y : RecoverySource := sourceResetAll (p := literalSourcePar 0) a.2
      change (∫⁻ w : RecoveryPath, B.indicator (fun _ => 1) w
        ∂CF3MarkedKernel.eventLaw recoveryValid (coreProject y) none) ≤ c
      exact (lintegral_indicator_one
        (μ := CF3MarkedKernel.eventLaw recoveryValid (coreProject y) none) hB).le.trans (hbound _)
    _ = c := by rw [lintegral_const,measure_univ,mul_one]

theorem completed_switch_renewal_protocol_failure (x : Raw) :
    V4.TwoPhaseLaw.completedSwitchLaw x
      {z | offPath z ∈ renewalFailure (renewalSchedule 10)} ≤
        ENNReal.ofReal ((11/100000 : ℝ)+10*Real.exp (-8)) :=
  completed_switch_off_event_bound x (renewalFailure (renewalSchedule 10))
    (measurableSet_renewalFailure _) _ (fun y => eleven_recovery_ten_division_failure_bound y none)

theorem g60_completion_failure_probability (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬continuousEvent (globalRaw x z)} ≤
      ENNReal.ofReal (9545923/9062500000 : ℝ) := by
  calc
    _ = V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬pathEvent (globalRaw x z)} := by
      apply measure_congr
      filter_upwards [completedSwitchLaw_ae_continuous_event_iff x] with z hc
      exact propext (not_congr hc).symm
    _ = pathLaw x {w | ¬pathEvent w} :=
      (Measure.map_apply (measurable_globalRaw x) measurableSet_pathEvent.compl).symm
    _ = pathLaw x {w | ¬continuousEvent w} := by
      apply measure_congr
      filter_upwards [pathLaw_ae_clockSupport x] with w hw
      exact propext (not_congr (pathEvent_iff_continuous w hw))
    _ ≤ _ := g60_actual_failure_probability x hx

theorem g60_and_renewal_protocol_failure (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x
      {z | ¬continuousEvent (globalRaw x z) ∨ offPath z ∈ renewalFailure (renewalSchedule 10)} ≤
        ENNReal.ofReal ((9545923/9062500000 : ℝ)+11/100000+10*Real.exp (-8)) := by
  calc
    _ ≤ V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬continuousEvent (globalRaw x z)}+
        V4.TwoPhaseLaw.completedSwitchLaw x {z | offPath z ∈ renewalFailure (renewalSchedule 10)} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (9545923/9062500000 : ℝ)+
        ENNReal.ofReal ((11/100000 : ℝ)+10*Real.exp (-8)) :=
      add_le_add (g60_completion_failure_probability x hx) (completed_switch_renewal_protocol_failure x)
    _ = _ := by
      rw [←ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 9545923/9062500000) (by positivity)]
      congr 1
      ring

end
end P161Formal
