module

public import P161Formal.SourceStockProcessLaw

/-! Physical-time observations of the concrete absorbing stock process.
Absorbing failure is represented by zero physical populations and no accepted
division; it is retained in the sample space and fails protected floors. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped Classical
noncomputable section

local instance stoppedObsGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stoppedObsGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance stoppedObsGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stoppedObsGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

local instance stoppedObsRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance stoppedObsRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stoppedObsMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance stoppedObsMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

def sourceStockStateAt (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : Option SourceStockState :=
  sourceStockRun x z (sourceGlobalPrefix z t)

def emptyStockPopulation : Population := ⟨fun _ _ => 0,fun _ => false⟩

def sourceStoppedObservations (x : Raw) (z : V4.TwoPhaseLaw.Completion) : MissionObservations where
  state t := ((sourceStockStateAt x z t).map (fun s => sourcePopulation (seed := 6) s.raw)).getD emptyStockPopulation
  credits t i j := ((sourceStockStateAt x z t).map (fun s => (s.raw i).q j)).getD 0
  initiatingDivisions t i := ((sourceStockStateAt x z t).map (fun s => (s.raw i).nd)).getD 0
  feed t := ((sourceStockStateAt x z t).map SourceStockState.feed).getD 0
  seeds t := ((sourceStockStateAt x z t).map SourceStockState.seeds).getD 0
  consumedFuel t := ((sourceStockStateAt x z t).map (fun s => s.consumed+s.victimFuel)).getD 0
  precursors t := ((sourceStockStateAt x z t).map (fun s => s.births+s.seeds)).getD 0
  divisions t := ((sourceStockStateAt x z t).map SourceStockState.divisions).getD 0
  victimSlots t := ((sourceStockStateAt x z t).map (fun s => 3*2048*s.divisions)).getD 0
  victimFuel t := ((sourceStockStateAt x z t).map SourceStockState.victimFuel).getD 0
  isDivision t := globalSourceDivisionAt z t ∧ sourceStockStateAt x z t ≠ none

theorem source_stock_prefix_raw_time (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) :
    (sourceStockAtPrefix x z (sourceGlobalPrefix z t)).raw = globalState x z t := rfl

theorem ae_source_stock_matches_through_sixty (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x, idealResourceGood z.1 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 60 →
        sourceStockStateAt x z t = some (sourceStockAtPrefix x z (sourceGlobalPrefix z t)) := by
  filter_upwards [ae_global_resource_prefix_caps x,completedSwitchLaw_ae_global_supported x] with z hc hs
  intro hg t ht ht60
  have hcap := hc hg t ht ht60
  have ha : sourcePrefixCount 6 sourceMarkFeed (wholePath z) (sourceGlobalPrefix z t) ≤ 800000000 := by
    change (sourcePhysicalObservations x z).feed t ≤ 800000000
    rw [source_observations_feed]
    exact hcap.1
  have he : sourcePrefixCount 6 sourceMarkSeeds (wholePath z) (sourceGlobalPrefix z t) ≤ 5000 := by
    change (sourcePhysicalObservations x z).seeds t ≤ 5000
    rw [source_observations_seed]
    exact hcap.2.1
  have hd : sourcePrefixCount 6 sourceMarkDivision (wholePath z) (sourceGlobalPrefix z t) ≤ 1200 := by
    change (sourcePhysicalObservations x z).divisions t ≤ 1200
    rw [source_observations_division]
    exact hcap.2.2
  exact source_stock_identical_at_prefix x z hs (sourceGlobalPrefix z t) ha he hd

end
end P161Formal
