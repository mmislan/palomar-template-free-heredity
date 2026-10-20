module

public import P161Formal.SourceRecoveryTail
public import proofs.CTMCHeredity20261019.V2.PhysicalRecoveryStops
public import proofs.HybridCTMCInfrastructure.TimedPathExit

/-! Literal physical recovery failure. The estimate concerns failure while
applicable floors hold locally, under the unconditioned actual marked law.
No future successful mission or eventual recovery is assumed. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open V2.PhysicalRecoveryStops
open scoped ENNReal Classical
noncomputable section

local instance physicalRecoveryMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance physicalRecoveryMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

theorem first_physical_hit_before_iff {S : Type*} (P : S → Prop)
    (w : ℕ → ℝ × S) {T : ℝ}
    (hpos : ∀ n : ℕ, 0 < (w (n+1)).1)
    (hcross : ∃ n : ℕ, T < arrivalTime n w) :
    (∃ t : ℝ, t ≤ T ∧ firstPhysicalHit P w t) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ P (timedState t w) := by
  constructor
  · rintro ⟨t,ht,hfirst⟩
    exact ⟨t,hfirst.1,ht,hfirst.2.1⟩
  · rintro ⟨t,ht,htT,hP⟩
    have hindex : P (w (clockIndex t w)).2 := hP
    have hex : ∃ n : ℕ, P (w n).2 := ⟨clockIndex t w,hindex⟩
    have hmin : Nat.find hex ≤ clockIndex t w := Nat.find_min' hex hindex
    have htcross : ∃ n : ℕ, t < arrivalTime n w := by
      obtain ⟨n,hn⟩ := hcross
      exact ⟨n,htT.trans_lt hn⟩
    refine ⟨arrivalTime (Nat.find hex) w,?_,?_⟩
    · exact ((arrivalTime_mono w) hmin).trans ((clockIndex_segment ht w htcross).1.trans htT)
    · exact (firstIndex_iff_physical_arrival P w hpos (Nat.find hex)).mp
        ⟨Nat.find_spec hex,fun m hm => Nat.find_min hex hm⟩

theorem timed_history_nonempty {S : Type*} (T : ℝ) (w : ℕ → ℝ × S) :
    timedHistory T w ≠ [] := by
  intro he
  have hl := congrArg List.length he
  simp [timedHistory,statePrefix] at hl

def recoveryStateFloor (z : RecoveryMarkedState) : Prop :=
  ∀ i : SiteId, ∀ j : SpeciesId, 16 ≤ ((z.1 i).1 j).val

def recoveryStateReady (z : RecoveryMarkedState) : Prop :=
  V2.RecoveryStops.coreReady512 z.1

theorem recovery_live_iff_floor_nonready (z : RecoveryMarkedState) :
    recoveryStateLive z ↔ recoveryStateFloor z ∧ ¬recoveryStateReady z := by
  change ((∀ i : SiteId, ∀ j : SpeciesId, True → 16 ≤ ((z.1 i).1 j).val) ∧
    ¬(∀ i : SiteId, ∀ j : SpeciesId, 512 ≤ ((z.1 i).1 j).val)) ↔ _
  simp [recoveryStateFloor,recoveryStateReady,V2.RecoveryStops.coreReady512]

def recoveryPhysicalFailure (w : ℕ → ℝ × RecoveryMarkedState) : Prop :=
  (∀ t : ℝ, 0 ≤ t → t ≤ 1/2 → recoveryStateFloor (timedState t w)) ∧
    ¬∃ t : ℝ, t ≤ 1/2 ∧ firstPhysicalHit recoveryStateReady w t

theorem recovery_physical_failure_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old {w | recoveryPhysicalFailure w} ≤
      ENNReal.ofReal (1/100000 : ℝ) := by
  refine (measure_mono_ae ?_).trans (recovery_visited_nonready_allowance x old)
  filter_upwards [(CF3MarkedKernel.kernel recoveryValid).ae_arrival_crosses
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old) (1/2),
    (CF3MarkedKernel.kernel recoveryValid).ae_holding_pos
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old)] with w hcross hpos
  intro hw
  have hnot : ¬∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/2 ∧ recoveryStateReady (timedState t w) :=
    fun hh => hw.2 ((first_physical_hit_before_iff recoveryStateReady w hpos hcross).mpr hh)
  have hlive : ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 → recoveryStateLive (timedState t w) := by
    intro t ht htT
    exact (recovery_live_iff_floor_nonready _).mpr
      ⟨hw.1 t ht htT,fun hr => hnot ⟨t,ht,htT,hr⟩⟩
  refine ⟨timed_history_nonempty (1/2) w,?_⟩
  intro z hz
  by_contra hbad
  have he := (timedHistory_exited_iff recoveryStateLive w
    (by norm_num : (0 : ℝ) ≤ 1/2) hcross hpos).mp ⟨z,hz,hbad⟩
  rcases he with ⟨t,ht,htT,hfail⟩
  exact hfail (hlive t ht htT)

end
end P161Formal
