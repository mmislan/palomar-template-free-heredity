module

public import P161Formal.SourceRenewalBound

/-! Eleven recoveries interleaved with ten strictly fresh divisions on the
same actual seed-free marked path. Every later local estimate is integrated
against attained past stopping mass, using the proved whole future law. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019
open scoped BigOperators ENNReal Classical
noncomputable section

local instance renewalProtocolMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalProtocolMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

def renewalPredicate (recovery : Bool) : ℕ → RecoveryMarkedState → Prop :=
  if recovery then recoveryExitPredicate else freshDivisionPredicate

def renewalDeadline (recovery : Bool) : ℝ := if recovery then 1/2 else 2

def renewalAllowance (recovery : Bool) : ℝ≥0∞ :=
  if recovery then ENNReal.ofReal (1/100000 : ℝ) else ENNReal.ofReal (Real.exp (-8))

def renewalSlices (recovery : Bool) :=
  boundedSourceSlices (renewalPredicate recovery) (renewalDeadline recovery)

def renewalFailure : List Bool → Set RecoveryPath
  | [] => ∅
  | recovery :: rest =>
    (eventIndexHitEvent (renewalSlices recovery))ᶜ ∪
      ⋃ n : ℕ, eventIndexStopSlice (renewalSlices recovery) n ∩
        normalizedEventSuffix n ⁻¹' renewalFailure rest

theorem measurableSet_renewalFailure (stages : List Bool) :
    MeasurableSet (renewalFailure stages) := by
  induction stages with
  | nil => exact MeasurableSet.empty
  | cons recovery rest ih =>
    exact (measurableSet_eventIndexHitEvent (renewalSlices recovery)
      (measurableSet_boundedSourceSlices _ _)).compl.union
      (MeasurableSet.iUnion (fun n =>
        (measurableSet_eventIndexStopSlice (renewalSlices recovery)
          (measurableSet_boundedSourceSlices _ _) n).inter
        (ih.preimage (measurable_normalizedEventSuffix n))))

theorem source_episode_nonhit_bound (recovery : Bool) (x : RecoveryCore)
    (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old
      (eventIndexHitEvent (renewalSlices recovery))ᶜ ≤ renewalAllowance recovery := by
  cases recovery with
  | false => exact bounded_division_nonhit_bound x old
  | true => exact bounded_recovery_nonhit_bound x old

theorem renewal_failure_bound (stages : List Bool) (x : RecoveryCore)
    (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old (renewalFailure stages) ≤
      (stages.map renewalAllowance).sum := by
  induction stages generalizing x old with
  | nil => simp only [renewalFailure,measure_empty,List.map_nil,List.sum_nil,le_refl]
  | cons recovery rest ih =>
    have hf := (measure_stopped_future_union_le (CF3MarkedKernel.kernel recoveryValid)
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old) (renewalSlices recovery)
      (renewalFailure rest) (measurableSet_renewalFailure rest)).trans
      (partial_stop_future_event_bound (CF3MarkedKernel.kernel recoveryValid)
        (CF3MarkedKernel.rate_positive recoveryValid) (x,old) (renewalSlices recovery)
        (measurableSet_boundedSourceSlices _ _) (bounded_source_slices_disjoint _ _)
        (renewalFailure rest) (measurableSet_renewalFailure rest)
        (rest.map renewalAllowance).sum (fun z => ih z.1 z.2))
    calc
      _ ≤ CF3MarkedKernel.eventLaw recoveryValid x old
          (eventIndexHitEvent (renewalSlices recovery))ᶜ +
        CF3MarkedKernel.eventLaw recoveryValid x old
          (⋃ n : ℕ, eventIndexStopSlice (renewalSlices recovery) n ∩
            normalizedEventSuffix n ⁻¹' renewalFailure rest) := measure_union_le _ _
      _ ≤ renewalAllowance recovery+(rest.map renewalAllowance).sum :=
        add_le_add (source_episode_nonhit_bound recovery x old) hf
      _ = _ := by rw [List.map_cons,List.sum_cons]

def renewalSchedule : ℕ → List Bool
  | 0 => [true]
  | n+1 => true :: false :: renewalSchedule n

theorem eleven_recovery_ten_division_failure_bound (x : RecoveryCore)
    (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old (renewalFailure (renewalSchedule 10)) ≤
      ENNReal.ofReal ((11/100000 : ℝ)+10*Real.exp (-8)) := by
  have h := renewal_failure_bound (renewalSchedule 10) x old
  have hs : ((renewalSchedule 10).map renewalAllowance).sum =
      11*ENNReal.ofReal (1/100000 : ℝ)+10*ENNReal.ofReal (Real.exp (-8)) := by
    simp only [renewalSchedule,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      renewalAllowance,Bool.false_eq_true,ite_true,ite_false]
    ring
  rw [hs] at h
  have he : (11 : ℝ≥0∞)*ENNReal.ofReal (1/100000 : ℝ)+
      10*ENNReal.ofReal (Real.exp (-8)) =
      ENNReal.ofReal ((11/100000 : ℝ)+10*Real.exp (-8)) := by
    rw [←ENNReal.ofReal_ofNat (n := 11),←ENNReal.ofReal_ofNat (n := 10),
      ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11),
      ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
      ←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact h.trans_eq he

end
end P161Formal
