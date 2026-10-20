module

public import P161Formal.SourceSeedMoment

/-! Accepted seed entries under the unconditional two-phase law. This uses
uniform conditional phase moments in the same manner as the preserved owner
SwitchStockTail, with the source-specific seed labels and ceiling. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance seedTailRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance seedTailRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩

local instance seedTailMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance seedTailMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def switchedSeedCount (h : TwoPhaseHistory) : ℕ := phaseSeedCount 6 h.1+phaseSeedCount 0 h.2

theorem measurable_switchedSeedCount : Measurable switchedSeedCount :=
  ((measurable_phaseSeedCount 6).comp measurable_fst).add
    ((measurable_phaseSeedCount 0).comp measurable_snd)

theorem seed_weight_sum (h : TwoPhaseHistory) :
    ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(switchedSeedCount h : ℝ))) =
      phaseSeedWeight 6 h.1*phaseSeedWeight 0 h.2 := by
  rw [switchedSeedCount,Nat.cast_add,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem switched_seed_mgf (x : Raw) :
    (∫⁻ h, ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(switchedSeedCount h : ℝ))) ∂switchedLaw x) ≤
      ENNReal.ofReal (Real.exp (4320*(Real.exp (1/10)-1))) := by
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2160*(Real.exp (1/10)-1)))
  have hF : Measurable (fun h : TwoPhaseHistory =>
      ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(switchedSeedCount h : ℝ)))) :=
    (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp ((1/10 : ℝ)*k)))).comp
      measurable_switchedSeedCount
  have hoff (a : PhaseHistory) :
      (∫⁻ b, phaseSeedWeight 0 b
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)) ≤ B :=
    phase_seed_thirty 0 (by norm_num) (by norm_num) a.2
  have hon : (∫⁻ a, phaseSeedWeight 6 a
      ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) ≤ B :=
    phase_seed_thirty 6 (by norm_num) (by norm_num) x
  calc
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (Real.exp ((1/10 : ℝ)*(switchedSeedCount (a,b) : ℝ)))
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      switchedLaw_lintegral x _ hF
    _ = ∫⁻ a, phaseSeedWeight 6 a*(∫⁻ b, phaseSeedWeight 0 b
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2))
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_congr
      intro a
      calc
        _ = ∫⁻ b, phaseSeedWeight 6 a*phaseSeedWeight 0 b
            ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2) :=
          lintegral_congr (fun b => seed_weight_sum (a,b))
        _ = _ := lintegral_const_mul (phaseSeedWeight 6 a) (measurable_phaseSeedWeight 0)
    _ ≤ ∫⁻ a, B*phaseSeedWeight 6 a
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      lintegral_mono (fun a => (mul_le_mul_right (hoff a) (phaseSeedWeight 6 a)).trans_eq (mul_comm _ _))
    _ = B*(∫⁻ a, phaseSeedWeight 6 a
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) :=
      lintegral_const_mul B (measurable_phaseSeedWeight 6)
    _ ≤ B*B := mul_le_mul_right hon B
    _ = _ := by
      dsimp only [B]
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      apply congrArg ENNReal.ofReal
      apply congrArg Real.exp
      ring

theorem switched_seeds_ge_5000 (x : Raw) :
    switchedLaw x {h | 5000 ≤ switchedSeedCount h} ≤ ENNReal.ofReal (Real.exp (-20)) := by
  have ht := count_tail_of_mgf (switchedLaw x) switchedSeedCount measurable_switchedSeedCount
    (by norm_num : (0 : ℝ) ≤ 1/10) (switched_seed_mgf x) 5000
  exact ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr stock_seed_exponent))

theorem switched_seeds_gt_5000 (x : Raw) :
    switchedLaw x {h | 5000 < switchedSeedCount h} ≤ ENNReal.ofReal (Real.exp (-20)) :=
  (measure_mono (fun _ hh => Nat.le_of_lt hh)).trans (switched_seeds_ge_5000 x)

end
end P161Formal
