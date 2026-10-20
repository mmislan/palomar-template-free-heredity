module

public import P161Formal.SourceStoppedMissionBridge
public import Mathlib.MeasureTheory.Measure.Map

/-! Full canonical finite-stock mission on the actual coupled realization law.
The realization retains the driving switched history together with its stopped
stock state. Its graph is a measurable embedding, so every event (including the
entire physical mission) has exactly its original probability, with no discarded
or renormalized exhaustion mass. Physical observations read the stopped state. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped Classical ENNReal
noncomputable section

local instance finiteMissionGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance finiteMissionGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance finiteMissionGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance finiteMissionGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance finiteMissionRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance finiteMissionRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance finiteMissionMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance finiteMissionMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

abbrev SourceStockPath := ℕ → Option SourceStockState
abbrev SourceRealizedStockTrace := V4.TwoPhaseLaw.Completion × SourceStockPath

def sourceRealizedStockTrace (x : Raw) (z : V4.TwoPhaseLaw.Completion) : SourceRealizedStockTrace :=
  (z,sourceStockRun x z)

theorem measurable_sourceRealizedStockTrace (x : Raw) : Measurable (sourceRealizedStockTrace x) :=
  measurable_id.prodMk (measurable_pi_iff.mpr (measurable_sourceStockRun x))

theorem measurableSet_sourceStockGraph (x : Raw) :
    MeasurableSet {u : SourceRealizedStockTrace | u.2 = sourceStockRun x u.1} := by
  have he : {u : SourceRealizedStockTrace | u.2 = sourceStockRun x u.1} =
      ⋂ n : ℕ, {u : SourceRealizedStockTrace | u.2 n = sourceStockRun x u.1 n} := by
    ext u
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact ⟨fun h n => congrFun h n,fun h => funext h⟩
  rw [he]
  exact MeasurableSet.iInter (fun n => measurableSet_eq_fun
    ((measurable_pi_apply n).comp measurable_snd) ((measurable_sourceStockRun x n).comp measurable_fst))

theorem measurableEmbedding_sourceRealizedStockTrace (x : Raw) :
    MeasurableEmbedding (sourceRealizedStockTrace x) := by
  refine ⟨?_,measurable_sourceRealizedStockTrace x,?_⟩
  · intro a b h
    exact congrArg Prod.fst h
  · intro s hs
    have he : sourceRealizedStockTrace x '' s =
        {u : SourceRealizedStockTrace | u.1 ∈ s} ∩ {u | u.2 = sourceStockRun x u.1} := by
      ext u
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨hz,rfl⟩
      · rintro ⟨hu,hg⟩
        exact ⟨u.1,hu,Prod.ext rfl hg.symm⟩
    rw [he]
    exact (hs.preimage measurable_fst).inter (measurableSet_sourceStockGraph x)

def sourceRealizedFiniteStockLaw (x : Raw) : Measure SourceRealizedStockTrace :=
  (V4.TwoPhaseLaw.completedSwitchLaw x).map (sourceRealizedStockTrace x)

instance sourceRealizedFiniteStockLaw_probability (x : Raw) : IsProbabilityMeasure (sourceRealizedFiniteStockLaw x) := by
  constructor
  rw [sourceRealizedFiniteStockLaw,
    Measure.map_apply (measurable_sourceRealizedStockTrace x) MeasurableSet.univ]
  simp

def sourceRealizedObservations (u : SourceRealizedStockTrace) : MissionObservations where
  state t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => sourcePopulation (seed := 6) s.raw)).getD emptyStockPopulation
  credits t i j := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => (s.raw i).q j)).getD 0
  initiatingDivisions t i := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => (s.raw i).nd)).getD 0
  feed t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.feed).getD 0
  seeds t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.seeds).getD 0
  consumedFuel t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => s.consumed+s.victimFuel)).getD 0
  precursors t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => s.births+s.seeds)).getD 0
  divisions t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.divisions).getD 0
  victimSlots t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => 3*2048*s.divisions)).getD 0
  victimFuel t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.victimFuel).getD 0
  isDivision t := globalSourceDivisionAt u.1 t ∧ u.2 (sourceGlobalPrefix u.1 t) ≠ none

theorem source_realized_observations_eq_stopped (x : Raw) (z : V4.TwoPhaseLaw.Completion) :
    sourceRealizedObservations (sourceRealizedStockTrace x z) = sourceStoppedObservations x z := rfl

/-- The full beta4m mission, with one fixed seed switch and one finite stock.
All quantitative source, physical-time, stopped-recovery, witness and budget
premises are discharged. Only the allowed prepared old-founder condition remains. -/
theorem template_free_heredity_finite_stock (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    sourceRealizedFiniteStockLaw x {u | ¬completeMission (sourceRealizedObservations u)} ≤
      ENNReal.ofReal failureCeiling := by
  calc
    _ = V4.TwoPhaseLaw.completedSwitchLaw x
        ((sourceRealizedStockTrace x) ⁻¹' {u | ¬completeMission (sourceRealizedObservations u)}) :=
      (measurableEmbedding_sourceRealizedStockTrace x).map_apply _ _
    _ = V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬completeMission (sourceStoppedObservations x z)} := rfl
    _ ≤ _ := source_stopped_completeMission_failure x hx

end
end P161Formal
