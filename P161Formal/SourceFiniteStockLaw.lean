module

public import P161Formal.SourceGlobalLedger

/-! Support under the actual unconditional switched completion law. All sampled
positive marks satisfy the physical fuel-debit premises on the one global raw
fold. The finite-stock absorbing construction will consume this support. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped BigOperators Classical
noncomputable section

local instance finiteStockRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance finiteStockRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance finiteStockMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance finiteStockMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

local instance finiteStockLiteralRawMeasurableSpace :
    MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance finiteStockLiteralRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance finiteStockLiteralMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance finiteStockLiteralMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

theorem measurableSet_sourceRawSupported (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    MeasurableSet {w | sourceRawSupported seed x w} :=
  (measurableSet_sourceSupportedSegment (literalSourcePar seed)).preimage
    (RawOperated.measurable_rawPair (literalSourcePar seed) x)

theorem measurableSet_joint_sourceRawSupported (seed : ℝ) :
    MeasurableSet {a : SourceState (literalSourcePar seed) × MarkedPath (literalSourcePar seed) |
      sourceRawSupported seed a.1 a.2} := by
  have h : MeasurableSet (⋃ x : SourceState (literalSourcePar seed),
      {a : SourceState (literalSourcePar seed) × MarkedPath (literalSourcePar seed) |
        a.1 = x ∧ sourceRawSupported seed x a.2}) := by
    apply MeasurableSet.iUnion
    intro x
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_sourceRawSupported seed x).preimage measurable_snd)
  convert h using 1
  ext a
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · intro ha
    exact ⟨a.1,rfl,ha⟩
  · rintro ⟨x,hax,hx⟩
    simpa only [hax] using hx

def switchedSourceSupported (h : TwoPhaseHistory) : Prop :=
  RawOperated.allSegments (sourceSupportedSegment canonicalSeedOnCF3) h.1 ∧
    RawOperated.allSegments (sourceSupportedSegment seedOff) h.2

theorem measurableSet_switchedSourceSupported : MeasurableSet {h | switchedSourceSupported h} :=
  ((RawOperated.measurableSet_allSegments (sourceSupportedSegment canonicalSeedOnCF3)
    (measurableSet_sourceSupportedSegment canonicalSeedOnCF3) 300).preimage measurable_fst).inter
      ((RawOperated.measurableSet_allSegments (sourceSupportedSegment seedOff)
        (measurableSet_sourceSupportedSegment seedOff) 300).preimage measurable_snd)

theorem switchedLaw_ae_sourceSupported (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, switchedSourceSupported h := by
  change ∀ᵐ h ∂(RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)).compProd
    afterSwitchKernel, _
  apply Measure.ae_compProd_of_ae_ae measurableSet_switchedSourceSupported
  filter_upwards [source_rawLaw_ae_supported seedOn_valid blockDuration 300 (sourceResetAll x)] with a ha
  have hb := source_rawLaw_ae_supported canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
  filter_upwards [hb] with b hb
  exact ⟨ha,hb⟩

theorem completedSwitchLaw_ae_sourceSupported (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x, switchedSourceSupported z.1 := by
  change ∀ᵐ z ∂(switchedLaw x).compProd V4.TwoPhaseLaw.terminalKernel, _
  apply Measure.ae_compProd_of_ae_ae (measurableSet_switchedSourceSupported.preimage measurable_fst)
  filter_upwards [switchedLaw_ae_sourceSupported x] with h hh
  exact Filter.Eventually.of_forall (fun _ => hh)

set_option backward.isDefEq.respectTransparency false in
theorem completedSwitchLaw_ae_terminal_supported (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x, sourceRawSupported 0 z.1.2.2 z.2 := by
  have hm : MeasurableSet {z : V4.TwoPhaseLaw.Completion | sourceRawSupported 0 z.1.2.2 z.2} :=
    (measurableSet_joint_sourceRawSupported 0).preimage
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  change ∀ᵐ z ∂(switchedLaw x).compProd V4.TwoPhaseLaw.terminalKernel, _
  apply Measure.ae_compProd_of_ae_ae hm
  apply Filter.Eventually.of_forall
  intro h
  exact ae_raw_source_positive canonicalSeedFree_valid h.2.2 none

set_option backward.isDefEq.respectTransparency false in
theorem completedSwitchLaw_ae_global_supported (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      sourceRawSupported 6 (sourceResetAll (p := literalSourcePar 6) x) (wholePath z) := by
  filter_upwards [completedSwitchLaw_ae_sourceSupported x,
    completedSwitchLaw_ae_terminal_supported x,
    V4.TwoPhaseLaw.completedSwitchLaw_ae_compatible x,
    V4.TwoPhaseLaw.completedSwitchLaw_ae_faithful x] with z hs hv hc hf
  have hco : RawOperated.compatible (literalSourcePar 0) blockDuration 300
      (sourceResetAll (p := literalSourcePar 0) z.1.1.2) z.1.2 := by
    simpa only [literal_seed_off_parameter,seedOff] using hc.2
  have hfo : RawOperated.allSegments (RawOperated.faithful (literalSourcePar 0)) z.1.2 := by
    simpa only [literal_seed_off_parameter,seedOff] using hf.2
  have hso : RawOperated.allSegments (sourceSupportedSegment (literalSourcePar 0)) z.1.2 := by
    simpa only [literal_seed_off_parameter,seedOff] using hs.2
  have ho := source_stitch_supported 0 (by norm_num) blockDuration 300
    (sourceResetAll (p := literalSourcePar 0) z.1.1.2) z.1.2 z.2 hco hfo hso hv
  have hoff : sourceRawSupported 0 (sourceResetAll (p := literalSourcePar 0) z.1.1.2) (offPath z) := by
    simpa only [literal_seed_off_parameter,seedOff,offPath] using ho
  have hoffSix := source_raw_supported_zero_to_six _ (offPath z) hoff
  have hcore : coreProject (p := literalSourcePar 6) (sourceResetAll (p := literalSourcePar 0) z.1.1.2) =
      coreProject (p := literalSourcePar 6) z.1.1.2 := rfl
  have hright := source_raw_supported_core_congr 6 (by norm_num)
    (sourceResetAll (p := literalSourcePar 0) z.1.1.2) z.1.1.2 hcore (offPath z) hoffSix
  have hci : RawOperated.compatible (literalSourcePar 6) blockDuration 300
      (sourceResetAll (p := literalSourcePar 6) x) z.1.1 := by
    simpa only [literal_seed_on_parameter] using hc.1
  have hfi : RawOperated.allSegments (RawOperated.faithful (literalSourcePar 6)) z.1.1 := by
    simpa only [literal_seed_on_parameter] using hf.1
  have hsi : RawOperated.allSegments (sourceSupportedSegment (literalSourcePar 6)) z.1.1 := by
    simpa only [literal_seed_on_parameter] using hs.1
  have hon := source_stitch_supported 6 (by norm_num) blockDuration 300
    (sourceResetAll (p := literalSourcePar 6) x) z.1.1 (offPath z) hci hfi hsi hright
  simpa only [literal_seed_on_parameter,wholePath] using hon

end
end P161Formal
