module

public import proofs.HybridCTMCInfrastructure.TimedProcess
public import proofs.HybridCTMCInfrastructure.Composition

@[expose] public section

/-! Deterministic-horizon endpoint kernels of the actual timed process.
These finite PMFs can be composed by conditional_failure without independence
between successive operations and without random-return stopping machinery. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem mass_eq_toMeasure (p : PMF S) (A : S → Prop) : mass p A = p.toMeasure {s | A s} := by
  rw [p.toMeasure_apply (Set.to_countable _).measurableSet]
  rfl

namespace Kernel
def endpointLaw (K : HybridCTMC.Kernel S) (Λ : ℝ) (hΛ : 0 < Λ) (t : ℝ) (x : S) : Measure S :=
  (K.eventLaw Λ hΛ x).map (timedState t)

instance endpointLaw_probability (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (t : ℝ) (x : S) : IsProbabilityMeasure (K.endpointLaw Λ hΛ t x) := by
  change IsProbabilityMeasure ((K.eventLaw Λ hΛ x).map (timedState t))
  infer_instance

def timedEndpoint (K : HybridCTMC.Kernel S) (Λ : ℝ) (hΛ : 0 < Λ) (t : ℝ) (x : S) : PMF S :=
  (K.endpointLaw Λ hΛ t x).toPMF

theorem timedEndpoint_toMeasure (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (t : ℝ) (x : S) : (K.timedEndpoint Λ hΛ t x).toMeasure = K.endpointLaw Λ hΛ t x :=
  Measure.toPMF_toMeasure _

theorem mass_timedEndpoint (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (t : ℝ) (x : S) (A : S → Prop) :
    mass (K.timedEndpoint Λ hΛ t x) A = K.eventLaw Λ hΛ x {w | A (timedState t w)} := by
  rw [mass_eq_toMeasure, timedEndpoint_toMeasure, endpointLaw,
    Measure.map_apply (measurable_timedState t) (Set.to_countable _).measurableSet]
  rfl
end Kernel
end
end HybridCTMC
