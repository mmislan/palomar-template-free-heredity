module

public import P161Formal.SourceDivisionWait

/-! Measurable bounded partial stops for renewal and their quantitative
nonhit bounds. Recovery stops at the first Ready512 or floor failure;
on a globally floor-safe path the selected state is therefore Ready512.
Only observed prefixes occur in a stop slice. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory Preorder HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019 V2.RecoveryStops
open scoped BigOperators ENNReal Classical
noncomputable section

local instance renewalStopsMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalStopsMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

abbrev RecoveryPath := ℕ → ℝ × RecoveryMarkedState
abbrev RecoveryPrefix (n : ℕ) := EventPrefix RecoveryMarkedState n

def boundedSourceSlices (P : ℕ → RecoveryMarkedState → Prop) (T : ℝ) (n : ℕ) :
    Set (RecoveryPrefix n) :=
  firstSlices (literalSourcePar 0) P n ∩ {u | cutPrefixArrival n u ≤ T}

theorem measurableSet_boundedSourceSlices (P : ℕ → RecoveryMarkedState → Prop)
    (T : ℝ) (n : ℕ) : MeasurableSet (boundedSourceSlices P T n) :=
  (measurableSet_firstSlices (literalSourcePar 0) P n).inter
    (measurableSet_le (measurable_cutPrefixArrival n) measurable_const)

theorem bounded_source_slices_pullback (P : ℕ → RecoveryMarkedState → Prop)
    (T : ℝ) (w : RecoveryPath) (n : ℕ) :
    w ∈ eventIndexStopSlice (boundedSourceSlices P T) n ↔
      arrivalTime n w ≤ T ∧ P n (w n).2 ∧ ∀ m : ℕ, m < n → ¬P m (w m).2 := by
  change (frestrictLe n w ∈ firstSlices (literalSourcePar 0) P n ∧
    cutPrefixArrival n (frestrictLe n w) ≤ T) ↔ _
  rw [firstSlices_pullback,cutPrefixArrival_frestrict]
  tauto

theorem bounded_source_slices_disjoint (P : ℕ → RecoveryMarkedState → Prop) (T : ℝ) :
    Pairwise (fun n m => Disjoint (eventIndexStopSlice (boundedSourceSlices P T) n)
      (eventIndexStopSlice (boundedSourceSlices P T) m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro w hn hm
  exact Set.disjoint_left.mp (firstSlices_disjoint (literalSourcePar 0) P hnm) hn.1 hm.1

def sourceBoundedNoHit (P : ℕ → RecoveryMarkedState → Prop) (T : ℝ) (w : RecoveryPath) : Prop :=
  w ∉ eventIndexHitEvent (boundedSourceSlices P T)

theorem source_bounded_nohit_iff (P : ℕ → RecoveryMarkedState → Prop) (T : ℝ)
    (w : RecoveryPath) :
    sourceBoundedNoHit P T w ↔
      ¬∃ n : ℕ, arrivalTime n w ≤ T ∧ P n (w n).2 ∧ ∀ m : ℕ, m < n → ¬P m (w m).2 := by
  simp only [sourceBoundedNoHit,eventIndexHitEvent,Set.mem_iUnion,
    bounded_source_slices_pullback]

def recoveryExitPredicate (_n : ℕ) (z : RecoveryMarkedState) : Prop := ¬recoveryStateLive z

def freshDivisionPredicate (n : ℕ) (z : RecoveryMarkedState) : Prop :=
  0 < n ∧ recoveryStateDivision z

theorem bounded_recovery_nonhit_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old
      {w | sourceBoundedNoHit recoveryExitPredicate (1/2) w} ≤
        ENNReal.ofReal (1/100000 : ℝ) := by
  refine (measure_mono_ae ?_).trans (recovery_visited_nonready_allowance x old)
  filter_upwards [(CF3MarkedKernel.kernel recoveryValid).ae_arrival_crosses
    (CF3MarkedKernel.rate_positive recoveryValid) (x,old) (1/2)] with w hcross
  intro hw
  have hno := (source_bounded_nohit_iff recoveryExitPredicate (1/2) w).mp hw
  refine ⟨timed_history_nonempty (1/2) w,?_⟩
  intro z hz
  by_contra hbad
  obtain ⟨n,hn,he⟩ := (mem_statePrefix (clockIndex (1/2) w) w z).mp hz
  have hex : ∃ m : ℕ, recoveryExitPredicate m (w m).2 :=
    ⟨n,by simpa only [recoveryExitPredicate,he] using hbad⟩
  have hmin : Nat.find hex ≤ n := Nat.find_min' hex
    (by simpa only [recoveryExitPredicate,he] using hbad)
  apply hno
  refine ⟨Nat.find hex,?_,Nat.find_spec hex,fun m hm => Nat.find_min hex hm⟩
  exact ((arrivalTime_mono w) (hmin.trans hn)).trans
    (clockIndex_segment (by norm_num : (0 : ℝ) ≤ 1/2) w hcross).1

theorem bounded_division_nohit_iff (w : RecoveryPath) :
    sourceBoundedNoHit freshDivisionPredicate 2 w ↔ divisionWaitFailure w := by
  rw [source_bounded_nohit_iff]
  unfold divisionWaitFailure
  apply not_congr
  apply exists_congr
  intro n
  simp only [freshDivisionPredicate,firstFreshDivision]
  constructor
  · rintro ⟨ht,⟨hn,hd⟩,hprev⟩
    exact ⟨ht,hn,hd,fun m hm hmn hdm => hprev m hmn ⟨hm,hdm⟩⟩
  · rintro ⟨ht,hn,hd,hprev⟩
    refine ⟨ht,⟨hn,hd⟩,?_⟩
    rintro m hmn ⟨hm,hdm⟩
    exact hprev m hm hmn hdm

theorem bounded_division_nonhit_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old
      {w | sourceBoundedNoHit freshDivisionPredicate 2 w} ≤
        ENNReal.ofReal (Real.exp (-8)) := by
  simpa only [bounded_division_nohit_iff] using division_wait_failure_bound x old

end
end P161Formal
