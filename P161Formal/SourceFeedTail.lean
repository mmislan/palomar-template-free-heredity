module

public import P161Formal.SourceFeedKernel
public import proofs.CTMCHeredity20261019.V2.SeedSwitch

/-! One global accepted-feed bound through the actual fixed-time seed switch.
The terminal occupation witness is retained across every operated window and
the phase boundary. Initial fuel is paid once, not once per recovery or phase. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019 CF3Marked CF3RawPathLift
open V2 V2.SeedSwitch
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance feedTailRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance feedTailRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance feedTailMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance feedTailMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

abbrev feedMomentRate : ℝ := 4*stockFeedK1+1

def sharedFuelWitness (x : Raw) : ℝ := fuelOccupationWitness (fun i => (x i).R)

theorem source_fuel_witness_eq_shared (seed : ℝ) (x : Raw) :
    sourceFuelWitness (seed := seed) x = sharedFuelWitness x := rfl

theorem shared_fuel_reset_all (seed : ℝ) (x : Raw) :
    sharedFuelWitness (sourceResetAll (p := literalSourcePar seed) x) = sharedFuelWitness x := rfl

theorem actual_phase_feed_weighted_moment (seed : ℝ) (hseed : 0 ≤ seed)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (x : SourceState (literalSourcePar seed)) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (stockEta*(rawHistorySelectedCount (literalSourcePar seed)
      (sourceFeedState seed) T n h : ℝ)))*ENNReal.ofReal (sourceFuelWitness (seed := seed) h.2)
      ∂RawOperated.rawLaw (literal_source_valid seed hseed) T n x) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ)*T*feedMomentRate))*ENNReal.ofReal (sourceFuelWitness (seed := seed) x) := by
  have h := actual_raw_law_weighted_bound (literal_source_valid seed hseed) (sourceFeedState seed)
    stockEta (coreFuelWitness seed) hT (source_feed_step_nonnegative seed hseed)
    (source_feed_nn_step_bound seed hseed) n x
  change (∫⁻ h, ENNReal.ofReal (Real.exp (stockEta*(rawHistorySelectedCount (literalSourcePar seed)
      (sourceFeedState seed) T n h : ℝ)))*ENNReal.ofReal (sourceFuelWitness (seed := seed) h.2)
      ∂RawOperated.rawLaw (literal_source_valid seed hseed) T n x) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ)*FunctionalCapacity.cf3Rate (literalSourcePar seed)*T*
          ((1+feedMomentRate/FunctionalCapacity.cf3Rate (literalSourcePar seed))-1)))*
          ENNReal.ofReal (sourceFuelWitness (seed := seed) x) at h
  have he : (n : ℝ)*FunctionalCapacity.cf3Rate (literalSourcePar seed)*T*
      ((1+feedMomentRate/FunctionalCapacity.cf3Rate (literalSourcePar seed))-1) =
        (n : ℝ)*T*feedMomentRate := by
    field_simp [(CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).ne']
    ring
  simpa only [he] using h

def phaseFeedCount (seed : ℝ) (h : PhaseHistory) : ℕ :=
  rawHistorySelectedCount (literalSourcePar seed) (sourceFeedState seed) blockDuration 300 h

def phaseFeedWeight (seed : ℝ) (h : PhaseHistory) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (stockEta*(phaseFeedCount seed h : ℝ)))

theorem measurable_phaseFeedCount (seed : ℝ) : Measurable (phaseFeedCount seed) :=
  measurable_rawHistorySelectedCount (literalSourcePar seed) (sourceFeedState seed) blockDuration 300

theorem measurable_phaseFeedWeight (seed : ℝ) : Measurable (phaseFeedWeight seed) :=
  (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (stockEta*k)))).comp
    (measurable_phaseFeedCount seed)

theorem measurable_sharedFuelWitness : Measurable (fun x : Raw => ENNReal.ofReal (sharedFuelWitness x)) :=
  measurable_of_countable _

set_option backward.isDefEq.respectTransparency false in
theorem phase_feed_weighted_thirty (seed : ℝ) (hseed : 0 ≤ seed) (x : Raw) :
    (∫⁻ h, phaseFeedWeight seed h*ENNReal.ofReal (sharedFuelWitness h.2)
      ∂RawOperated.rawLaw (literal_source_valid seed hseed) blockDuration 300
        (sourceResetAll (p := literalSourcePar seed) x)) ≤
      ENNReal.ofReal (Real.exp (30*feedMomentRate))*ENNReal.ofReal (sharedFuelWitness x) := by
  have h := actual_phase_feed_weighted_moment seed hseed
    (by norm_num [blockDuration] : (0 : ℝ) ≤ blockDuration) 300
    (sourceResetAll (p := literalSourcePar seed) x)
  have he : ((300 : ℕ) : ℝ)*blockDuration*feedMomentRate = 30*feedMomentRate := by norm_num [blockDuration]
  simpa only [phaseFeedWeight,phaseFeedCount,he,source_fuel_witness_eq_shared,
    shared_fuel_reset_all] using h

def switchedFeedCount (h : TwoPhaseHistory) : ℕ := phaseFeedCount 6 h.1+phaseFeedCount 0 h.2

theorem measurable_switchedFeedCount : Measurable switchedFeedCount :=
  ((measurable_phaseFeedCount 6).comp measurable_fst).add
    ((measurable_phaseFeedCount 0).comp measurable_snd)

theorem feed_weight_sum (h : TwoPhaseHistory) :
    ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ))) =
      phaseFeedWeight 6 h.1*phaseFeedWeight 0 h.2 := by
  rw [switchedFeedCount,Nat.cast_add,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem switched_feed_weighted_moment (x : Raw) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ)))*
      ENNReal.ofReal (sharedFuelWitness h.2.2) ∂switchedLaw x) ≤
        ENNReal.ofReal (Real.exp (60*feedMomentRate))*ENNReal.ofReal (sharedFuelWitness x) := by
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (30*feedMomentRate))
  let F : TwoPhaseHistory → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ)))*ENNReal.ofReal (sharedFuelWitness h.2.2)
  have hF : Measurable F :=
    ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (stockEta*k)))).comp
      measurable_switchedFeedCount).mul
      (measurable_sharedFuelWitness.comp (measurable_snd.comp measurable_snd))
  have hoff (a : PhaseHistory) :
      (∫⁻ b, phaseFeedWeight 0 b*ENNReal.ofReal (sharedFuelWitness b.2)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)) ≤
          B*ENNReal.ofReal (sharedFuelWitness a.2) :=
    phase_feed_weighted_thirty 0 (by norm_num) a.2
  have hon : (∫⁻ a, phaseFeedWeight 6 a*ENNReal.ofReal (sharedFuelWitness a.2)
      ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) ≤
        B*ENNReal.ofReal (sharedFuelWitness x) := phase_feed_weighted_thirty 6 (by norm_num) x
  calc
    _ = ∫⁻ a, ∫⁻ b, F (a,b)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      switchedLaw_lintegral x F hF
    _ = ∫⁻ a, phaseFeedWeight 6 a*(∫⁻ b, phaseFeedWeight 0 b*ENNReal.ofReal (sharedFuelWitness b.2)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2))
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_congr
      intro a
      calc
        _ = ∫⁻ b, phaseFeedWeight 6 a*(phaseFeedWeight 0 b*ENNReal.ofReal (sharedFuelWitness b.2))
            ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2) := by
          apply lintegral_congr
          intro b
          dsimp [F]
          rw [feed_weight_sum]
          exact mul_assoc _ _ _
        _ = _ := lintegral_const_mul _
          ((measurable_phaseFeedWeight 0).mul (measurable_sharedFuelWitness.comp measurable_snd))
    _ ≤ ∫⁻ a, B*(phaseFeedWeight 6 a*ENNReal.ofReal (sharedFuelWitness a.2))
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_mono
      intro a
      exact (mul_le_mul_right (hoff a) (phaseFeedWeight 6 a)).trans_eq (by ac_rfl)
    _ = B*(∫⁻ a, phaseFeedWeight 6 a*ENNReal.ofReal (sharedFuelWitness a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) :=
      lintegral_const_mul B ((measurable_phaseFeedWeight 6).mul
        (measurable_sharedFuelWitness.comp measurable_snd))
    _ ≤ B*(B*ENNReal.ofReal (sharedFuelWitness x)) := mul_le_mul_right hon B
    _ = _ := by
      dsimp only [B]
      rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      congr 2
      ring

set_option backward.isDefEq.respectTransparency false in
theorem switched_feed_mgf (x : Raw) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ))) ∂switchedLaw x) ≤
      ENNReal.ofReal (Real.exp (4*stockS+60*feedMomentRate)) := by
  have hw (h : TwoPhaseHistory) : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (4*stockS))*ENNReal.ofReal (sharedFuelWitness h.2.2) := by
    rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hl := fuel_occupation_lower (fun i => (h.2.2 i).R)
    have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (4*stockS))
    have he : Real.exp (4*stockS)*Real.exp (-4*stockS) = 1 := by
      rw [←Real.exp_add,show (4*stockS)+(-4*stockS) = (0 : ℝ) by ring,Real.exp_zero]
    change 1 ≤ Real.exp (4*stockS)*fuelOccupationWitness (fun i => (h.2.2 i).R)
    linarith
  have hm : Measurable (fun h : TwoPhaseHistory =>
      ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ)))*ENNReal.ofReal (sharedFuelWitness h.2.2)) :=
    ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (stockEta*k)))).comp
      measurable_switchedFeedCount).mul
      (measurable_sharedFuelWitness.comp (measurable_snd.comp measurable_snd))
  calc
    _ ≤ ∫⁻ h, ENNReal.ofReal (Real.exp (4*stockS))*(
        ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ)))*ENNReal.ofReal (sharedFuelWitness h.2.2))
        ∂switchedLaw x := by
      apply lintegral_mono
      intro h
      simpa only [mul_one] using
        (mul_le_mul_right (hw h) (ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ))))).trans_eq
          (by ac_rfl)
    _ = ENNReal.ofReal (Real.exp (4*stockS))*(∫⁻ h,
        ENNReal.ofReal (Real.exp (stockEta*(switchedFeedCount h : ℝ)))*ENNReal.ofReal (sharedFuelWitness h.2.2)
        ∂switchedLaw x) := lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (Real.exp (4*stockS))*(ENNReal.ofReal (Real.exp (60*feedMomentRate))*
        ENNReal.ofReal (sharedFuelWitness x)) :=
      mul_le_mul_right (switched_feed_weighted_moment x) _
    _ ≤ ENNReal.ofReal (Real.exp (4*stockS))*(ENNReal.ofReal (Real.exp (60*feedMomentRate))*1) :=
      mul_le_mul_right (mul_le_mul_right (show ENNReal.ofReal (sharedFuelWitness x) ≤ 1 from by
        rw [←ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (fuel_occupation_upper _)) _) _
    _ = _ := by rw [mul_one,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]

theorem switched_feed_ge_800000000 (x : Raw) :
    switchedLaw x {h | 800000000 ≤ switchedFeedCount h} ≤ ENNReal.ofReal (Real.exp (-20)) := by
  have ht := count_tail_of_mgf (switchedLaw x) switchedFeedCount measurable_switchedFeedCount
    (show (0 : ℝ) ≤ stockEta by norm_num [stockEta]) (switched_feed_mgf x) 800000000
  have he := stock_feed_coarse_division_exponent
  exact ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))

theorem switched_feed_gt_800000000 (x : Raw) :
    switchedLaw x {h | 800000000 < switchedFeedCount h} ≤ ENNReal.ofReal (Real.exp (-20)) :=
  (measure_mono (fun _ hh => Nat.le_of_lt hh)).trans (switched_feed_ge_800000000 x)

end
end P161Formal
