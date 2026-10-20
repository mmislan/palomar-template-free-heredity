module

public import proofs.CTMCHeredity20261019.V2.OperatedObservations

@[expose] public section

/-! # Actual joint support for all-window observations

The marginal identities transfer the already constructed raw history support
to the completed law. These predicates describe the source fold, actual reset
starts and regular clocks, independently of the desired observation identity.
-/

namespace CTMCHeredity20261019.V3.Support

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.NoBoundaryArrival
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

theorem completedLaw_ae_compatible {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      RawOperated.compatible p T n x z.1 := by
  have hh := RawOperated.rawLaw_ae_compatible hp T n x
  rw [← OperatedObservations.completedLaw_fst hp T n x] at hh
  exact (ae_map_iff measurable_fst.aemeasurable
    (RawOperated.measurableSet_compatible p T n x)).mp hh

theorem completedLaw_ae_faithful {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      ∀ i : Fin n, RawOperated.faithful p (z.1.1 i) := by
  have hh := RawOperated.rawLaw_ae_faithful hp T n x
  rw [← OperatedObservations.completedLaw_fst hp T n x] at hh
  exact (ae_map_iff measurable_fst.aemeasurable
    (RawOperated.measurableSet_allSegments (RawOperated.faithful p)
      (RawOperated.measurableSet_faithful p) n)).mp hh

/-- One full-measure support set for every segment and the terminal tail.
There is no intersection over real times in this statement. -/
theorem completedLaw_ae_support {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      RawOperated.compatible p T n x z.1 ∧
      (∀ i : Fin n, RawOperated.faithful p (z.1.1 i)) ∧
      (∀ i : Fin n, ClockBoundarySupport ∅ (z.1.1 i).1) ∧
      ClockBoundarySupport ∅ z.2 := by
  filter_upwards [completedLaw_ae_compatible hp T n x,
    completedLaw_ae_faithful hp T n x,
    OperatedObservations.completedLaw_ae_clockSupport hp T n x] with z hc hf hk
  exact ⟨hc, hf, hk⟩

end
end CTMCHeredity20261019.V3.Support
