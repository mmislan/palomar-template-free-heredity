module

public import P161Formal.CountedLivePoisson
public import P161Formal.SourceRecoveryKernel

/-! The literal beta4m physical-time low-division recovery estimate. This is
the probability of an actual visited-history event under the source marked
clock law, before adding the separately owned division-count tail. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019
open scoped BigOperators ENNReal Classical
noncomputable section

local instance : MeasurableSpace RecoveryMarkedState := ⊤
local instance : MeasurableSingletonClass RecoveryMarkedState := ⟨fun _ => trivial⟩

def recoveryLowDivisionEvent (w : ℕ → ℝ × RecoveryMarkedState) : Prop :=
  countedLiveEvent recoveryStateLive recoveryStateDivision 28 (timedHistory (1/2) w)

theorem source_timed_low_division_recovery_bound (x : RecoveryCore)
    (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | recoveryLowDivisionEvent w} ≤
      ENNReal.ofReal (2/1000000 : ℝ) := by
  have ha : 0 ≤ recoveryWordA := by norm_num [recoveryWordA,strongKilledGamma]
  have hb : 0 ≤ recoveryWordB := by norm_num [recoveryWordB]
  have h := timed_counted_live_event_bound (CF3MarkedKernel.kernel recoveryValid)
    recoveryStateLive recoveryStateDivision recoveryStatePotential recoveryWordA recoveryWordB
    recovery_state_potential_nonnegative recovery_state_potential_barrier ha hb
    (by
      intro z hz
      refine le_trans ?_ (recovery_kernel_nonreset_bound z hz)
      apply (CF3MarkedKernel.kernel recoveryValid).expect_mono
      intro y
      split_ifs <;> simp_all)
    (by
      intro z hz
      refine le_trans ?_ (recovery_kernel_reset_bound z hz)
      apply (CF3MarkedKernel.kernel recoveryValid).expect_mono
      intro y
      split_ifs <;> simp_all)
    (Lam := FunctionalCapacity.cf3Rate (literalSourcePar 0)) (T := 1/2)
      (CF3MarkedKernel.rate_positive recoveryValid) (by norm_num) 28 (x,old)
  have hprod : FunctionalCapacity.cf3Rate (literalSourcePar 0)*(1/2)*(recoveryWordA-1) = -(strongKilledGamma/2) := by
    rw [source_common_clock.2]
    norm_num [recoveryWordA,strongKilledGamma]
  have hreset : FunctionalCapacity.cf3Rate (literalSourcePar 0)*(1/2)*recoveryWordB = 239 := by
    rw [source_common_clock.2]
    norm_num [recoveryWordB]
  rw [hprod,hreset] at h
  let P : ℝ := Real.exp (-(strongKilledGamma/2))*
    (∑ j ∈ Finset.range 28, (239 : ℝ)^j/j.factorial)
  have hP : 0 ≤ P := by unfold P; positivity
  have hmax := mul_le_mul_of_nonneg_left (recovery_state_potential_max (x,old)) hP
  have hscalar : P*(338971453059/125000 : ℝ) ≤ (2/1000000 : ℝ) := by
    have heq : P*(338971453059/125000 : ℝ) =
        strongWordNumerator/Real.exp (strongKilledGamma/2) := by
      unfold P strongWordNumerator
      rw [Real.exp_neg]
      ring
    rw [heq]
    exact strong_low_words_le_two_millionths
  change (CF3MarkedKernel.kernel recoveryValid).eventLaw
    (FunctionalCapacity.cf3Rate (literalSourcePar 0)) (CF3MarkedKernel.rate_positive recoveryValid)
    (x,old) {w | countedLiveEvent recoveryStateLive recoveryStateDivision 28
      (timedHistory (1/2) w)} ≤ _
  exact h.trans (ENNReal.ofReal_le_ofReal (hmax.trans hscalar))

end
end P161Formal
