module

public import P161Formal.SourcePhysicalRecovery
public import proofs.CTMCHeredity20261019.V2.ExecutedWindows

/-! Two-unit waiting time for the first strictly fresh actual division.
The coordinate-zero last-mark sentinel is excluded, even if its old mark is
itself a division. Null-state physical division labels remain counted. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open scoped BigOperators ENNReal Classical
noncomputable section

local instance divisionWaitMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance divisionWaitMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

theorem recovery_kernel_division_lower (z : RecoveryMarkedState) :
    4/FunctionalCapacity.cf3Rate (literalSourcePar 0) ≤
      (CF3MarkedKernel.kernel recoveryValid).event recoveryStateDivision z := by
  simp only [recovery_division_predicate_eq]
  rw [V2.MarkedCountTail.division_event_eq]
  apply div_le_div_of_nonneg_right _ (CF3MarkedKernel.rate_positive recoveryValid).le
  have h := (total_division_intensity_bounds (sourcePopulation (coreRepresent z.1))).1
  simpa only [siteDivisionIntensity,Fintype.sum_option,contract_division_rate_is_source] using h

theorem recovery_kernel_nondivision_bound (z : RecoveryMarkedState) :
    (CF3MarkedKernel.kernel recoveryValid).expect
      (fun y => if ¬recoveryStateDivision y then 1 else 0) z ≤
        1-4/FunctionalCapacity.cf3Rate (literalSourcePar 0) := by
  have he : (CF3MarkedKernel.kernel recoveryValid).expect
      (fun y => if ¬recoveryStateDivision y then 1 else 0) z +
      (CF3MarkedKernel.kernel recoveryValid).event recoveryStateDivision z = 1 := by
    unfold HybridCTMC.Kernel.event
    rw [←HybridCTMC.Kernel.expect_add]
    have hf : (fun y : RecoveryMarkedState =>
        (if ¬recoveryStateDivision y then (1 : ℝ) else 0)+
          (if recoveryStateDivision y then 1 else 0)) = (fun _ => 1) := by
      funext y
      by_cases hp : recoveryStateDivision y <;> simp [hp]
    rw [hf,HybridCTMC.Kernel.expect_const]
  linarith [recovery_kernel_division_lower z]

def divisionNoFreshHistory (w : ℕ → ℝ × RecoveryMarkedState) : Prop :=
  countedLiveEvent (fun _ => True) recoveryStateDivision 1 (timedHistory 2 w)

theorem no_fresh_division_history_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | divisionNoFreshHistory w} ≤
      ENNReal.ofReal (Real.exp (-8)) := by
  have ha : 0 ≤ 1-4/FunctionalCapacity.cf3Rate (literalSourcePar 0) := by
    rw [source_common_clock.2]
    norm_num
  have h := timed_counted_live_event_bound (CF3MarkedKernel.kernel recoveryValid)
    (fun _ => True) recoveryStateDivision (fun _ => 1)
    (1-4/FunctionalCapacity.cf3Rate (literalSourcePar 0)) 1
    (fun _ => by norm_num) (fun _ _ => le_rfl) ha (by norm_num)
    (by
      intro z _
      simpa only [true_and,mul_one] using recovery_kernel_nondivision_bound z)
    (by
      intro z _
      calc
        _ ≤ (CF3MarkedKernel.kernel recoveryValid).expect
            (fun _ : RecoveryMarkedState => (1 : ℝ)) z := by
          apply (CF3MarkedKernel.kernel recoveryValid).expect_mono
          intro y
          split_ifs <;> norm_num
        _ = 1*1 := by
          rw [(CF3MarkedKernel.kernel recoveryValid).expect_const 1 z]
          norm_num)
    (CF3MarkedKernel.rate_positive recoveryValid) (by norm_num : (0 : ℝ) ≤ 2) 1 (x,old)
  change (CF3MarkedKernel.kernel recoveryValid).eventLaw
    (FunctionalCapacity.cf3Rate (literalSourcePar 0)) (CF3MarkedKernel.rate_positive recoveryValid)
    (x,old) {w | countedLiveEvent (fun _ => True) recoveryStateDivision 1 (timedHistory 2 w)} ≤ _
  have he : FunctionalCapacity.cf3Rate (literalSourcePar 0)*2*
      (1-4/FunctionalCapacity.cf3Rate (literalSourcePar 0)-1) = (-8 : ℝ) := by
    rw [source_common_clock.2]
    norm_num
  simpa only [he,Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,
    div_one,mul_one] using h

theorem history_mark_count_eq_zero_iff {S : Type*} (P : S → Prop) (xs : List S) :
    historyMarkCount P xs = 0 ↔ ∀ z ∈ xs, ¬P z := by
  induction xs with
  | nil => simp [historyMarkCount]
  | cons x xs ih =>
    by_cases hx : P x <;> simp [historyMarkCount,hx,ih]

theorem mem_timed_history_tail {S : Type*} (T : ℝ) (w : ℕ → ℝ × S) (z : S) :
    z ∈ (timedHistory T w).tail ↔
      ∃ n : ℕ, 0 < n ∧ n ≤ clockIndex T w ∧ (w n).2 = z := by
  rw [V2.ExecutedWindows.timedHistory_tail_eq]
  simp only [V2.ExecutedWindows.positiveStates,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val+1,by omega,by have := i.isLt; omega,hi⟩
  · rintro ⟨n,hn,hnk,he⟩
    refine ⟨⟨n-1,by omega⟩,?_⟩
    have hsub : n-1+1 = n := by omega
    simpa only [hsub] using he

def firstFreshDivision (w : ℕ → ℝ × RecoveryMarkedState) (n : ℕ) : Prop :=
  0 < n ∧ recoveryStateDivision (w n).2 ∧
    ∀ m : ℕ, 0 < m → m < n → ¬recoveryStateDivision (w m).2

def divisionWaitFailure (w : ℕ → ℝ × RecoveryMarkedState) : Prop :=
  ¬∃ n : ℕ, arrivalTime n w ≤ 2 ∧ firstFreshDivision w n

theorem division_wait_failure_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | divisionWaitFailure w} ≤
      ENNReal.ofReal (Real.exp (-8)) := by
  refine (measure_mono_ae ?_).trans (no_fresh_division_history_bound x old)
  filter_upwards [(CF3MarkedKernel.kernel recoveryValid).ae_arrival_crosses
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old) 2] with w hcross
  intro hw
  refine ⟨timed_history_nonempty 2 w,fun _ _ => trivial,?_⟩
  have hz : historyMarkCount recoveryStateDivision (timedHistory 2 w).tail = 0 := by
    apply (history_mark_count_eq_zero_iff _ _).mpr
    intro z hz hdiv
    obtain ⟨n,hn,hnk,he⟩ := (mem_timed_history_tail 2 w z).mp hz
    have hex : ∃ m : ℕ, 0 < m ∧ recoveryStateDivision (w m).2 :=
      ⟨n,hn,by simpa only [he] using hdiv⟩
    have hmin : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn,by simpa only [he] using hdiv⟩
    apply hw
    refine ⟨Nat.find hex,?_,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
    · exact ((arrivalTime_mono w) (hmin.trans hnk)).trans
        (clockIndex_segment (by norm_num : (0 : ℝ) ≤ 2) w hcross).1
    · intro m hm hmmin hmd
      exact (Nat.find_min hex hmmin) ⟨hm,hmd⟩
  omega

end
end P161Formal
