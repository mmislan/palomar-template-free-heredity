module

public import proofs.CTMCHeredity20261019.V2.SeedSwitch
public import proofs.CTMCHeredity20261019.V2.MarkedCountTail

@[expose] public section

/-!
# Actual division-count tail for the canonical switched operated law

The count reads complete actual division marks on the executed block windows,
including operations with a null physical state change. The two conditional
phase MGF bounds are composed under the actual joint switch law. No phase
independence, successful-history conditioning, or resource replenishment is
assumed. The resulting tail controls this one division allowance; it does not
prove the full finite-stock mission or the other simultaneous resource tails.
-/

namespace CTMCHeredity20261019.V2.SwitchStockTail

open FunctionalCapacity MeasureTheory ProbabilityTheory
open SeedSwitch MarkedCountTail
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

/-- Actual positive-index division marks executed in all 600 physical windows.
This is a mark count, not a difference of reset nd ledgers. -/
def totalDivisions (h : TwoPhaseHistory) : ℕ :=
  rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300 h.1 +
    rawHistoryDivisionCount seedOff blockDuration 300 h.2

theorem measurable_totalDivisions : Measurable totalDivisions := by
  have ha : Measurable (fun h : TwoPhaseHistory =>
      rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300 h.1) :=
    (measurable_rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300).comp
      (measurable_fst : Measurable (fun h : TwoPhaseHistory => h.1))
  have hb : Measurable (fun h : TwoPhaseHistory =>
      rawHistoryDivisionCount seedOff blockDuration 300 h.2) :=
    (measurable_rawHistoryDivisionCount seedOff blockDuration 300).comp
      (measurable_snd : Measurable (fun h : TwoPhaseHistory => h.2))
  change Measurable (fun h : TwoPhaseHistory =>
    rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300 h.1 +
      rawHistoryDivisionCount seedOff blockDuration 300 h.2)
  exact ha.add hb

private theorem measurable_phaseReward (p : Par) (θ : ℝ) :
    Measurable (fun h : RawOperated.History p 300 =>
      ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p blockDuration 300 h : ℝ)))) := by
  simpa only [Function.comp_def] using
    (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ * (k : ℝ))))).comp
      (measurable_rawHistoryDivisionCount p blockDuration 300)

private theorem reward_sum (θ : ℝ) (a b : PhaseHistory) :
    ENNReal.ofReal (Real.exp (θ * (totalDivisions (a, b) : ℝ))) =
      ENNReal.ofReal (Real.exp
        (θ * (rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300 a : ℝ))) *
      ENNReal.ofReal (Real.exp
        (θ * (rawHistoryDivisionCount seedOff blockDuration 300 b : ℝ))) := by
  rw [totalDivisions, Nat.cast_add, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

private theorem phase_mgf {p : Par} (hp : p.Valid) (hM : p.M = 4) (hc : p.c = 3)
    {θ : ℝ} (hθ : 0 ≤ θ) (x : SourceState p) :
    (∫⁻ h, ENNReal.ofReal (Real.exp
      (θ * (rawHistoryDivisionCount p blockDuration 300 h : ℝ)))
      ∂RawOperated.rawLaw hp blockDuration 300 x) ≤
        ENNReal.ofReal (Real.exp (480 * (Real.exp θ - 1))) := by
  have hb := rawLaw_divisionCount_mgf hp hM hc
    (by norm_num [blockDuration] : 0 ≤ blockDuration) hθ 300 x
  have he : (300 : ℝ) * 16 * blockDuration * (Real.exp θ - 1) =
      480 * (Real.exp θ - 1) := by norm_num [blockDuration]
  exact hb.trans_eq (congrArg (fun r : ℝ => ENNReal.ofReal (Real.exp r)) he)

/-- A uniform conditional second-phase bound is integrated against the actual
first-phase law. The phases are not replaced by an independent product law. -/
theorem switched_division_mgf (x : Raw) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (θ * (totalDivisions h : ℝ))) ∂switchedLaw x) ≤
      ENNReal.ofReal (Real.exp (960 * (Real.exp θ - 1))) := by
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (480 * (Real.exp θ - 1)))
  let fa : PhaseHistory → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp
    (θ * (rawHistoryDivisionCount canonicalSeedOnCF3 blockDuration 300 a : ℝ)))
  let fb : PhaseHistory → ℝ≥0∞ := fun b => ENNReal.ofReal (Real.exp
    (θ * (rawHistoryDivisionCount seedOff blockDuration 300 b : ℝ)))
  have hfa : Measurable fa := measurable_phaseReward canonicalSeedOnCF3 θ
  have hfb : Measurable fb := measurable_phaseReward seedOff θ
  have hF : Measurable (fun h : TwoPhaseHistory =>
      ENNReal.ofReal (Real.exp (θ * (totalDivisions h : ℝ)))) := by
    simpa only [Function.comp_def] using
      (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ * (k : ℝ))))).comp
        measurable_totalDivisions
  have hoff (a : PhaseHistory) :
      (∫⁻ b, fb b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
        (sourceResetAll a.2)) ≤ B :=
    phase_mgf (p := seedOff) canonicalSeedFree_valid rfl rfl hθ (sourceResetAll a.2)
  have hon :
      (∫⁻ a, fa a ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) ≤ B :=
    phase_mgf (p := canonicalSeedOnCF3) seedOn_valid rfl rfl hθ (sourceResetAll x)
  calc
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (Real.exp (θ * (totalDivisions (a, b) : ℝ)))
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      switchedLaw_lintegral x _ hF
    _ = ∫⁻ a, fa a * (∫⁻ b, fb b
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2))
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_congr
      intro a
      calc
        _ = ∫⁻ b, fa a * fb b
            ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2) :=
          lintegral_congr (fun b => reward_sum θ a b)
        _ = _ := lintegral_const_mul (fa a) hfb
    _ ≤ ∫⁻ a, B * fa a
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      lintegral_mono (fun a => (mul_le_mul_right (hoff a) (fa a)).trans_eq (mul_comm (fa a) B))
    _ = B * (∫⁻ a, fa a
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)) :=
      lintegral_const_mul B hfa
    _ ≤ B * B := mul_le_mul_right hon B
    _ = _ := by
      dsimp only [B]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply congrArg ENNReal.ofReal
      apply congrArg Real.exp
      ring

theorem division_exponent_rational :
    960 * (((20 : ℝ) / 19) ^ 4 - 1) - ((1 : ℝ) / 5) * 1200 =
      -2785200 / 130321 := by norm_num

/-- Actual terminal division-budget tail on the normalized switched raw law. -/
theorem switched_divisions_ge_1200 (x : Raw) :
    switchedLaw x {h | 1200 ≤ totalDivisions h} ≤ ENNReal.ofReal (Real.exp (-20)) := by
  have ht := count_tail_of_mgf (switchedLaw x) totalDivisions measurable_totalDivisions
    (by norm_num : 0 ≤ (1 : ℝ) / 5)
    (switched_division_mgf x (by norm_num : 0 ≤ (1 : ℝ) / 5)) 1200
  have he : 960 * (Real.exp ((1 : ℝ) / 5) - 1) - ((1 : ℝ) / 5) * 1200 ≤ -20 := by
    nlinarith [MarkedCountTail.division_exponent_le_neg_twenty]
  exact ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))

theorem switched_divisions_gt_1200 (x : Raw) :
    switchedLaw x {h | 1200 < totalDivisions h} ≤ ENNReal.ofReal (Real.exp (-20)) :=
  (measure_mono (fun _ hh => Nat.le_of_lt hh)).trans (switched_divisions_ge_1200 x)

end
end CTMCHeredity20261019.V2.SwitchStockTail
