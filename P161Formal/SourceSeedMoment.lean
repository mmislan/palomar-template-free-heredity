module

public import P161Formal.SourceSeedIntensity
public import proofs.CTMCHeredity20261019.V2.SeedSwitch

/-! Uniform accepted-seed moments through the actual operated histories.
The bound72 is valid in each phase, including the zero-seed phase. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance seedMomentRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance seedMomentRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance seedMomentMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance seedMomentMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

theorem actual_phase_seed_moment (seed : ℝ) (hseed : 0 ≤ seed) (hseed6 : seed ≤ 6)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (x : SourceState (literalSourcePar seed)) :
    (∫⁻ h, ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(rawHistorySelectedCount (literalSourcePar seed)
      (sourceSeedState seed) T n h : ℝ)))
      ∂RawOperated.rawLaw (literal_source_valid seed hseed) T n x) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ)*72*T*(Real.exp (1/10)-1))) := by
  have h := actual_raw_law_weighted_bound (literal_source_valid seed hseed) (sourceSeedState seed)
    (1/10) (fun _ => (1 : ℝ)) hT (source_seed_step_nonnegative seed hseed)
    (source_seed_nn_step_bound seed hseed hseed6) n x
  have he : (n : ℝ)*FunctionalCapacity.cf3Rate (literalSourcePar seed)*T*
      ((1+(72/FunctionalCapacity.cf3Rate (literalSourcePar seed))*(Real.exp (1/10)-1))-1) =
        (n : ℝ)*72*T*(Real.exp (1/10)-1) := by
    field_simp [(CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).ne']
    ring
  simpa only [rawHistoryWeightedReward,ENNReal.ofReal_one,mul_one,he] using h

def phaseSeedCount (seed : ℝ) (h : PhaseHistory) : ℕ :=
  rawHistorySelectedCount (literalSourcePar seed) (sourceSeedState seed) blockDuration 300 h

def phaseSeedWeight (seed : ℝ) (h : PhaseHistory) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(phaseSeedCount seed h : ℝ)))

theorem measurable_phaseSeedCount (seed : ℝ) : Measurable (phaseSeedCount seed) :=
  measurable_rawHistorySelectedCount (literalSourcePar seed) (sourceSeedState seed) blockDuration 300

theorem measurable_phaseSeedWeight (seed : ℝ) : Measurable (phaseSeedWeight seed) :=
  (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp ((1/10 : ℝ)*k)))).comp
    (measurable_phaseSeedCount seed)

set_option backward.isDefEq.respectTransparency false in
theorem phase_seed_thirty (seed : ℝ) (hseed : 0 ≤ seed) (hseed6 : seed ≤ 6) (x : Raw) :
    (∫⁻ h, phaseSeedWeight seed h
      ∂RawOperated.rawLaw (literal_source_valid seed hseed) blockDuration 300
        (sourceResetAll (p := literalSourcePar seed) x)) ≤
      ENNReal.ofReal (Real.exp (2160*(Real.exp (1/10)-1))) := by
  have h := actual_phase_seed_moment seed hseed hseed6
    (by norm_num [blockDuration] : (0 : ℝ) ≤ blockDuration) 300
    (sourceResetAll (p := literalSourcePar seed) x)
  have he : ((300 : ℕ) : ℝ)*72*blockDuration*(Real.exp (1/10)-1) =
      2160*(Real.exp (1/10)-1) := by norm_num [blockDuration]
  simpa only [phaseSeedWeight,phaseSeedCount,he] using h

end
end P161Formal
