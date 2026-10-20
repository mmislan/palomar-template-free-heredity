module

public import P161Formal.SourceTimedRecovery
public import proofs.CTMCHeredity20261019.V2.MarkedCountTail

/-! Complete marked-history recovery allowance. The high actual-division tail
is instantiated from the owner's MGF, not reproved or replaced by a proposal
count. Continuous first-hit/stopped interpretation is the next bridge. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open scoped ENNReal Classical
noncomputable section

local instance recoveryTailMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance recoveryTailMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

theorem history_mark_count_eq_owner {S : Type*} (P : S → Prop) (xs : List S) :
    historyMarkCount P xs = V2.MarkedCountTail.countAll P xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [historyMarkCount,V2.MarkedCountTail.countAll,ih]

theorem recovery_division_predicate_eq :
    recoveryStateDivision = V2.MarkedCountTail.divisionState (p := literalSourcePar 0) := by
  funext z
  apply propext
  rcases z with ⟨_core,m⟩
  cases m with
  | none => simp [recoveryStateDivision,isDivisionProposal,
      V2.MarkedCountTail.divisionState,V2.MarkedCountTail.isDivision]
  | some m => cases m <;> simp [recoveryStateDivision,isDivisionProposal,
      V2.MarkedCountTail.divisionState,V2.MarkedCountTail.isDivision]

def recoveryDivisionCount (T : ℝ) (w : ℕ → ℝ × RecoveryMarkedState) : ℕ :=
  historyMarkCount recoveryStateDivision (timedHistory T w).tail

theorem recovery_division_count_eq_owner (T : ℝ) (w : ℕ → ℝ × RecoveryMarkedState) :
    recoveryDivisionCount T w = V2.MarkedCountTail.divisionCount (literalSourcePar 0) T w := by
  unfold recoveryDivisionCount
  rw [recovery_division_predicate_eq,history_mark_count_eq_owner]
  rfl

theorem recovery_high_division_tail (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old
      {w | 28 ≤ recoveryDivisionCount (1/2) w} ≤ ENNReal.ofReal (1/1000000 : ℝ) := by
  have ht := V2.MarkedCountTail.count_tail_of_mgf
    (CF3MarkedKernel.eventLaw recoveryValid x old)
    (V2.MarkedCountTail.divisionCount (literalSourcePar 0) (1/2))
    (V2.MarkedCountTail.measurable_divisionCount (literalSourcePar 0) (1/2))
    (by norm_num : (0 : ℝ) ≤ 1)
    (V2.MarkedCountTail.divisionCount_mgf recoveryValid rfl rfl
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1) x old) 28
  have he : (16 : ℝ)*(1/2)*(Real.exp 1-1)-1*28 ≤ -14 := by
    have h := strong_count_exponent.1
    nlinarith
  have hs := (Real.exp_le_exp.mpr he).trans strong_count_tail_le_one_millionth
  simp only [recovery_division_count_eq_owner]
  exact ht.trans (ENNReal.ofReal_le_ofReal hs)

def recoveryVisitedNonreadyEvent (w : ℕ → ℝ × RecoveryMarkedState) : Prop :=
  timedHistory (1/2) w ≠ [] ∧ ∀ z ∈ timedHistory (1/2) w, recoveryStateLive z

theorem recovery_visited_nonready_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | recoveryVisitedNonreadyEvent w} ≤
      ENNReal.ofReal (3/1000000 : ℝ) := by
  have hsub : {w | recoveryVisitedNonreadyEvent w} ⊆
      {w | recoveryLowDivisionEvent w} ∪ {w | 28 ≤ recoveryDivisionCount (1/2) w} := by
    intro w hw
    by_cases hn : recoveryDivisionCount (1/2) w < 28
    · exact Or.inl ⟨hw.1,hw.2,hn⟩
    · exact Or.inr (Nat.le_of_not_gt hn)
  calc
    _ ≤ CF3MarkedKernel.eventLaw recoveryValid x old
        ({w | recoveryLowDivisionEvent w} ∪ {w | 28 ≤ recoveryDivisionCount (1/2) w}) :=
      measure_mono hsub
    _ ≤ CF3MarkedKernel.eventLaw recoveryValid x old {w | recoveryLowDivisionEvent w}+
        CF3MarkedKernel.eventLaw recoveryValid x old {w | 28 ≤ recoveryDivisionCount (1/2) w} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (2/1000000 : ℝ)+ENNReal.ofReal (1/1000000 : ℝ) :=
      add_le_add (source_timed_low_division_recovery_bound x old) (recovery_high_division_tail x old)
    _ = _ := by
      rw [←ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 2/1000000)
        (by norm_num : (0 : ℝ) ≤ 1/1000000)]
      congr 1
      norm_num

theorem recovery_visited_nonready_allowance (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | recoveryVisitedNonreadyEvent w} ≤
      ENNReal.ofReal (1/100000 : ℝ) :=
  (recovery_visited_nonready_bound x old).trans (ENNReal.ofReal_le_ofReal (by norm_num))

end
end P161Formal
