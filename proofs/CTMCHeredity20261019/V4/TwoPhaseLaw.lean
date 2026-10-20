module

public import proofs.CTMCHeredity20261019.V2.SeedSwitch
public import proofs.CTMCHeredity20261019.V2.PhysicalOperated
public import proofs.CTMCHeredity20261019.V3.Support

@[expose] public section

/-!
# Completion and joint support of the actual canonical switched law

The terminal seed-free marked path is conditionally sampled from the second
phase's returned raw state. The normalized joint law retains both operated
phase histories, including failures, and has the verified switchedLaw as its
first marginal. Compatible reset starts, faithful complete source folds, and
all marked clock support hold simultaneously. No observation correspondence
or successful-mission law is an input to this construction.
-/

namespace CTMCHeredity20261019.V4.TwoPhaseLaw

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V2.NoBoundaryArrival
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

abbrev Completion := SeedSwitch.TwoPhaseHistory × MarkedPath seedOff

/-- Actual off-source continuation from the final raw state. No success test
appears in the conditional sampling kernel. -/
def terminalKernel : ProbabilityTheory.Kernel SeedSwitch.TwoPhaseHistory (MarkedPath seedOff) where
  toFun h := CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject h.2.2) none
  measurable' := (measurable_of_countable (fun y : Raw =>
    CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject y) none)).comp
      (measurable_snd.comp measurable_snd)

instance terminalKernel_markov : IsMarkovKernel terminalKernel where
  isProbabilityMeasure h := CF3MarkedKernel.eventLaw_probability
    canonicalSeedFree_valid (coreProject h.2.2) none

/-- The unconditional two-phase operated history with its actual terminal tail. -/
def completedSwitchLaw (x : Raw) : Measure Completion :=
  (SeedSwitch.switchedLaw x).compProd terminalKernel

instance completedSwitchLaw_probability (x : Raw) :
    IsProbabilityMeasure (completedSwitchLaw x) := by
  unfold completedSwitchLaw
  infer_instance

/-- Appending the actual terminal tail preserves the entire two-phase history
law, rather than only a scalar reward or terminal-state distribution. -/
theorem completedSwitchLaw_fst (x : Raw) :
    (completedSwitchLaw x).map Prod.fst = SeedSwitch.switchedLaw x :=
  Measure.fst_compProd (SeedSwitch.switchedLaw x) terminalKernel

theorem completedSwitchLaw_ae_compatible (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x, SeedSwitch.jointCompatible x z.1 := by
  have hh := SeedSwitch.switchedLaw_ae_compatible x
  rw [← completedSwitchLaw_fst x] at hh
  exact ae_of_ae_map measurable_fst.aemeasurable hh

theorem completedSwitchLaw_ae_faithful (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x, SeedSwitch.jointFaithful z.1 := by
  have hh := SeedSwitch.switchedLaw_ae_faithful x
  rw [← completedSwitchLaw_fst x] at hh
  exact ae_of_ae_map measurable_fst.aemeasurable hh

/-- The stronger proved block-boundary exclusion is retained under completion. -/
theorem completedSwitchLaw_ae_jointClockSupport (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x, SeedSwitch.jointClockSupport z.1 := by
  have hh := SeedSwitch.switchedLaw_ae_clock_support x
  rw [← completedSwitchLaw_fst x] at hh
  exact ae_of_ae_map measurable_fst.aemeasurable hh

theorem completedSwitchLaw_ae_terminalClockSupport (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x, ClockBoundarySupport ∅ z.2 := by
  have hm : MeasurableSet {v : MarkedPath seedOff | ClockBoundarySupport ∅ v} :=
    measurableSet_clockBoundarySupport ∅ Set.countable_empty
  change ∀ᵐ z ∂(SeedSwitch.switchedLaw x).compProd terminalKernel, _
  apply Measure.ae_compProd_of_ae_ae (hm.preimage measurable_snd)
  exact Filter.Eventually.of_forall (fun h =>
    cf3_marked_ae_clockBoundarySupport (p := seedOff) canonicalSeedFree_valid
      (coreProject h.2.2) none ∅ Set.countable_empty)

private theorem clock_empty_of_boundary {S : Type*} (w : ℕ → ℝ × S)
    (hw : ClockBoundarySupport {blockDuration} w) : ClockBoundarySupport ∅ w :=
  ⟨hw.1, hw.2.1, fun _ => Set.notMem_empty _⟩

/-- Both phases and the terminal tail have positive, unbounded marked clocks
on the same actual joint draw. -/
theorem completedSwitchLaw_ae_clocks (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x,
      (∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1) ∧
      (∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1) ∧
      ClockBoundarySupport ∅ z.2 := by
  filter_upwards [completedSwitchLaw_ae_jointClockSupport x,
    completedSwitchLaw_ae_terminalClockSupport x] with z hs hv
  exact ⟨fun b => clock_empty_of_boundary _ ((hs.1 b).1),
    fun b => clock_empty_of_boundary _ ((hs.2 b).1), hv⟩

/-- One simultaneous support theorem for deterministic all-window composition.
The predicates are source reset/fold/clock facts, not desired bridge premises. -/
theorem completedSwitchLaw_ae_support (x : Raw) :
    ∀ᵐ z ∂completedSwitchLaw x,
      SeedSwitch.jointCompatible x z.1 ∧
      SeedSwitch.jointFaithful z.1 ∧
      (∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1) ∧
      (∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1) ∧
      ClockBoundarySupport ∅ z.2 := by
  filter_upwards [completedSwitchLaw_ae_compatible x,
    completedSwitchLaw_ae_faithful x, completedSwitchLaw_ae_clocks x] with z hc hf hk
  exact ⟨hc, hf, hk⟩

end
end CTMCHeredity20261019.V4.TwoPhaseLaw
