module

public import P161Formal.SourceRenewalProtocol

/-! Physical meaning of the attained renewal stops. This connects each
observed-prefix recovery to current-population Ready512 under its local floor,
and each positive division index to the first actual division time. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open V2.PhysicalRecoveryStops
open scoped Classical
noncomputable section

theorem normalized_suffix_state {S : Type*} (w : ℕ → ℝ × S) (n k : ℕ) :
    (normalizedEventSuffix n w k).2 = (w (n+k)).2 := by
  cases k with
  | zero => simp only [normalizedEventSuffix,Nat.add_zero]
  | succ k => rfl

theorem normalized_suffix_arrival {S : Type*} (w : ℕ → ℝ × S) (n k : ℕ) :
    arrivalTime (n+k) w = arrivalTime n w+arrivalTime k (normalizedEventSuffix n w) := by
  unfold arrivalTime
  rw [Finset.sum_range_add]
  congr 1

theorem normalized_suffix_positive {S : Type*} (w : ℕ → ℝ × S)
    (hpos : ∀ k : ℕ, 0 < (w (k+1)).1) (n : ℕ) :
    ∀ k : ℕ, 0 < (normalizedEventSuffix n w (k+1)).1 := by
  intro k
  exact hpos (n+k)

theorem normalized_suffix_unbounded {S : Type*} (w : ℕ → ℝ × S)
    (hclock : ∀ t : ℝ, ∃ k : ℕ, t < arrivalTime k w) (n : ℕ) :
    ∀ t : ℝ, ∃ k : ℕ, t < arrivalTime k (normalizedEventSuffix n w) := by
  intro t
  obtain ⟨m,hm⟩ := hclock (arrivalTime n w+max 0 t)
  have hmn : n ≤ m := by
    by_contra hh
    have hle := (arrivalTime_mono w) (Nat.le_of_lt (Nat.lt_of_not_ge hh))
    have hnon := le_max_left (0 : ℝ) t
    linarith
  have he := normalized_suffix_arrival w n (m-n)
  rw [Nat.add_sub_of_le hmn] at he
  refine ⟨m-n,?_⟩
  have ht := le_max_right (0 : ℝ) t
  linarith

theorem normalized_suffix_timed_state {S : Type*} (w : ℕ → ℝ × S)
    (hclock : ∀ t : ℝ, ∃ k : ℕ, t < arrivalTime k w) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    timedState (arrivalTime n w+t) w = timedState t (normalizedEventSuffix n w) := by
  let k := clockIndex t (normalizedEventSuffix n w)
  have hs := clockIndex_segment ht (normalizedEventSuffix n w)
    (normalized_suffix_unbounded w hclock n t)
  have hlo : arrivalTime (n+k) w ≤ arrivalTime n w+t := by
    rw [normalized_suffix_arrival]
    exact add_le_add_right hs.1 _
  have hhi : arrivalTime n w+t < arrivalTime (n+k+1) w := by
    rw [Nat.add_assoc,normalized_suffix_arrival]
    exact add_lt_add_right hs.2 _
  rw [timedState_eq_on_segment w (n+k) hlo hhi]
  exact (normalized_suffix_state w n k).symm

theorem renewal_nonfailure_cons (recovery : Bool) (rest : List Bool) (w : RecoveryPath)
    (hw : w ∉ renewalFailure (recovery::rest)) :
    ∃ n : ℕ, w ∈ eventIndexStopSlice (renewalSlices recovery) n ∧
      normalizedEventSuffix n w ∉ renewalFailure rest := by
  have hn : w ∈ eventIndexHitEvent (renewalSlices recovery) := by
    by_contra hh
    exact hw (Or.inl hh)
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hn
  refine ⟨n,hn,?_⟩
  intro hbad
  exact hw (Or.inr (Set.mem_iUnion.mpr ⟨n,hn,hbad⟩))

theorem attained_recovery_first_physical (w : RecoveryPath) (n : ℕ)
    (hpos : ∀ k : ℕ, 0 < (w (k+1)).1)
    (hstop : w ∈ eventIndexStopSlice (renewalSlices true) n)
    (hfloor : ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 → recoveryStateFloor (timedState t w)) :
    arrivalTime n w ≤ 1/2 ∧ firstPhysicalHit recoveryStateReady w (arrivalTime n w) := by
  have hs := (bounded_source_slices_pullback recoveryExitPredicate (1/2) w n).mp hstop
  refine ⟨hs.1,(firstIndex_iff_physical_arrival recoveryStateReady w hpos n).mp ?_⟩
  have hf : recoveryStateFloor (w n).2 := by
    rw [←timedState_at_arrival w hpos n]
    exact hfloor _ (arrivalTime_nonneg n w) hs.1
  have hready : recoveryStateReady (w n).2 := by
    by_contra hr
    exact hs.2.1 ((recovery_live_iff_floor_nonready _).mpr ⟨hf,hr⟩)
  refine ⟨hready,?_⟩
  intro m hm hr
  have hlive : recoveryStateLive (w m).2 := by
    by_contra hh
    exact hs.2.2 m hm hh
  exact (recovery_live_iff_floor_nonready _).mp hlive |>.2 hr

def physicalActualDivisionAt (w : RecoveryPath) (t : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ t = arrivalTime n w ∧ recoveryStateDivision (w n).2

theorem attained_division_first_physical (w : RecoveryPath) (n : ℕ)
    (hpos : ∀ k : ℕ, 0 < (w (k+1)).1)
    (hstop : w ∈ eventIndexStopSlice (renewalSlices false) n) :
    0 < arrivalTime n w ∧ arrivalTime n w ≤ 2 ∧
      physicalActualDivisionAt w (arrivalTime n w) ∧
        ∀ t : ℝ, 0 < t → t < arrivalTime n w → ¬physicalActualDivisionAt w t := by
  have hs := (bounded_source_slices_pullback freshDivisionPredicate 2 w n).mp hstop
  have hn : 0 < n := hs.2.1.1
  have hmono := positive_holds_arrival_strictMono w hpos
  have ha0 : arrivalTime 0 w = 0 := by simp only [arrivalTime,Finset.sum_range_zero]
  refine ⟨?_,hs.1,⟨n,hn,rfl,hs.2.1.2⟩,?_⟩
  · simpa only [ha0] using hmono hn
  · rintro t _ ht ⟨m,hm,rfl,hd⟩
    have hmn : m < n := by
      by_contra hh
      exact (not_le_of_gt ht) ((arrivalTime_mono w) (Nat.le_of_not_gt hh))
    exact hs.2.2 m hmn ⟨hm,hd⟩

end
end P161Formal
