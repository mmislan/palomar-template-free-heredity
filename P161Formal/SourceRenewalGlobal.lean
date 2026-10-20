module

public import P161Formal.SourceRenewalPhysical

/-! Physical renewal on one uninterrupted post-switch marked path. The
relative horizon25.5 becomes the absolute deadline55.5 after the fixed
withdrawal time30. Floor safety is used for deterministic interpretation,
never to condition the fresh future probability law. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open scoped ENNReal Classical
noncomputable section

local instance renewalGlobalMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalGlobalMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

def coreFirstReadyAtOrAfter (w : RecoveryPath) (start hit : ℝ) : Prop :=
  start ≤ hit ∧ recoveryStateReady (timedState hit w) ∧
    ∀ t : ℝ, start ≤ t → t < hit → ¬recoveryStateReady (timedState t w)

def coreFirstDivisionAfter (w : RecoveryPath) (start division : ℝ) : Prop :=
  start < division ∧ physicalActualDivisionAt w division ∧
    ∀ t : ℝ, start < t → t < division → ¬physicalActualDivisionAt w t

theorem normalized_suffix_comp (w : RecoveryPath) (n m : ℕ) :
    normalizedEventSuffix m (normalizedEventSuffix n w) = normalizedEventSuffix (n+m) w := by
  funext k
  cases k with
  | zero => exact congrArg (fun z => ((0 : ℝ),z)) (normalized_suffix_state w n m)
  | succ k => simp only [normalizedEventSuffix,Nat.add_assoc]

theorem physical_division_suffix_iff (w : RecoveryPath) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    physicalActualDivisionAt (normalizedEventSuffix n w) t ↔
      physicalActualDivisionAt w (arrivalTime n w+t) := by
  constructor
  · rintro ⟨k,hk,he,hd⟩
    refine ⟨n+k,by omega,?_,?_⟩
    · rw [he,normalized_suffix_arrival]
    · simpa only [normalized_suffix_state] using hd
  · rintro ⟨m,_,he,hd⟩
    have hm : n < m := by
      by_contra hh
      have hle := (arrivalTime_mono w) (Nat.le_of_not_gt hh)
      linarith
    have ha := normalized_suffix_arrival w n (m-n)
    rw [Nat.add_sub_of_le hm.le] at ha
    refine ⟨m-n,by omega,by linarith,?_⟩
    simpa only [normalized_suffix_state,Nat.add_sub_of_le hm.le] using hd

theorem core_first_ready_suffix (w : RecoveryPath)
    (hclock : ∀ t : ℝ, ∃ k : ℕ, t < arrivalTime k w) (n : ℕ)
    {start hit : ℝ} (hstart : 0 ≤ start)
    (hfirst : coreFirstReadyAtOrAfter (normalizedEventSuffix n w) start hit) :
    coreFirstReadyAtOrAfter w (arrivalTime n w+start) (arrivalTime n w+hit) := by
  refine ⟨by linarith [hfirst.1],?_,?_⟩
  · rw [normalized_suffix_timed_state w hclock n (hstart.trans hfirst.1)]
    exact hfirst.2.1
  · intro t hts hth
    have ht : 0 ≤ t-arrivalTime n w := by linarith
    have hp := hfirst.2.2 (t-arrivalTime n w) (by linarith) (by linarith)
    have he : arrivalTime n w+(t-arrivalTime n w) = t := by ring
    rw [←normalized_suffix_timed_state w hclock n ht,he] at hp
    exact hp

theorem core_first_division_suffix (w : RecoveryPath) (n : ℕ)
    {start division : ℝ} (hstart : 0 ≤ start)
    (hfirst : coreFirstDivisionAfter (normalizedEventSuffix n w) start division) :
    coreFirstDivisionAfter w (arrivalTime n w+start) (arrivalTime n w+division) := by
  have hd : 0 < division := lt_of_le_of_lt hstart hfirst.1
  refine ⟨by linarith [hfirst.1],(physical_division_suffix_iff w n hd).mp hfirst.2.1,?_⟩
  intro t hts htd hdiv
  have ht : 0 < t-arrivalTime n w := by linarith
  apply hfirst.2.2 (t-arrivalTime n w) (by linarith) (by linarith)
  apply (physical_division_suffix_iff w n ht).mpr
  have he : arrivalTime n w+(t-arrivalTime n w) = t := by ring
  simpa only [he] using hdiv

def renewalHorizon (n : ℕ) : ℝ := (5*(n : ℝ)+1)/2

def coreRenewalSequence (n : ℕ) (w : RecoveryPath) : Prop :=
  ∃ (τ : Fin (n+1) → ℝ) (σ : Fin n → ℝ),
    (∀ i, 0 ≤ τ i) ∧ (∀ r, 0 ≤ σ r) ∧
    coreFirstReadyAtOrAfter w 0 (τ 0) ∧ τ 0 ≤ 1/2 ∧
    (∀ r : Fin n, coreFirstDivisionAfter w (τ r.castSucc) (σ r) ∧
      σ r-τ r.castSucc ≤ 2 ∧ coreFirstReadyAtOrAfter w (σ r) (τ r.succ) ∧
      τ r.succ-σ r ≤ 1/2) ∧ τ (Fin.last n) ≤ renewalHorizon n

theorem nonfailure_gives_physical_renewal (n : ℕ) (w : RecoveryPath)
    (hpos : ∀ k : ℕ, 0 < (w (k+1)).1)
    (hclock : ∀ t : ℝ, ∃ k : ℕ, t < arrivalTime k w)
    (hfloor : ∀ t : ℝ, 0 ≤ t → t ≤ renewalHorizon n → recoveryStateFloor (timedState t w))
    (hw : w ∉ renewalFailure (renewalSchedule n)) : coreRenewalSequence n w := by
  induction n generalizing w with
  | zero =>
    obtain ⟨r,hr,_⟩ := renewal_nonfailure_cons true [] w hw
    have hf : ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 → recoveryStateFloor (timedState t w) := by
      simpa only [renewalHorizon,Nat.cast_zero,mul_zero,zero_add] using hfloor
    have ht := attained_recovery_first_physical w r hpos hr hf
    refine ⟨fun _ => arrivalTime r w,fun i => Fin.elim0 i,
      fun _ => arrivalTime_nonneg r w,fun i => Fin.elim0 i,ht.2,ht.1,fun i => Fin.elim0 i,?_⟩
    simpa only [renewalHorizon,Nat.cast_zero,mul_zero,zero_add] using ht.1
  | succ n ih =>
    obtain ⟨r,hr,hrest⟩ := renewal_nonfailure_cons true (false::renewalSchedule n) w hw
    obtain ⟨d,hd,hfuture⟩ := renewal_nonfailure_cons false (renewalSchedule n)
      (normalizedEventSuffix r w) hrest
    have hf0 : ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 → recoveryStateFloor (timedState t w) := by
      intro t ht htT
      apply hfloor t ht
      have hn : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
      dsimp [renewalHorizon]
      nlinarith
    have hready := attained_recovery_first_physical w r hpos hr hf0
    have hdiv := attained_division_first_physical (normalizedEventSuffix r w) d
      (normalized_suffix_positive w hpos r) hd
    have ha : arrivalTime (r+d) w = arrivalTime r w+
        arrivalTime d (normalizedEventSuffix r w) := normalized_suffix_arrival w r d
    have habound : arrivalTime (r+d) w ≤ 5/2 := by linarith [hready.1,hdiv.2.1]
    have ha0 : 0 ≤ arrivalTime (r+d) w := arrivalTime_nonneg _ _
    have hfFuture : ∀ t : ℝ, 0 ≤ t → t ≤ renewalHorizon n →
        recoveryStateFloor (timedState t (normalizedEventSuffix (r+d) w)) := by
      intro t ht htT
      rw [←normalized_suffix_timed_state w hclock (r+d) ht]
      apply hfloor _ (add_nonneg ha0 ht)
      dsimp [renewalHorizon] at htT ⊢
      rw [Nat.cast_add,Nat.cast_one]
      linarith
    have hfuture' : normalizedEventSuffix (r+d) w ∉ renewalFailure (renewalSchedule n) := by
      simpa only [normalized_suffix_comp] using hfuture
    obtain ⟨τ,σ,hτ,hσ,hτ0,hτhalf,hsteps,hlast⟩ := ih
      (normalizedEventSuffix (r+d) w) (normalized_suffix_positive w hpos (r+d))
      (normalized_suffix_unbounded w hclock (r+d)) hfFuture hfuture'
    have hdiv0 : coreFirstDivisionAfter w (arrivalTime r w) (arrivalTime (r+d) w) := by
      have hh : coreFirstDivisionAfter (normalizedEventSuffix r w) 0
          (arrivalTime d (normalizedEventSuffix r w)) := ⟨hdiv.1,hdiv.2.2⟩
      have hs := core_first_division_suffix w r (by norm_num : (0 : ℝ) ≤ 0) hh
      simpa only [add_zero,←ha] using hs
    refine ⟨Fin.cons (arrivalTime r w) (fun i => arrivalTime (r+d) w+τ i),
      Fin.cons (arrivalTime (r+d) w) (fun i => arrivalTime (r+d) w+σ i),?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases (arrivalTime_nonneg r w) (fun j => ?_) i
      exact add_nonneg ha0 (hτ j)
    · intro i
      refine Fin.cases ha0 (fun j => ?_) i
      exact add_nonneg ha0 (hσ j)
    · exact hready.2
    · exact hready.1
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change coreFirstDivisionAfter w (arrivalTime r w) (arrivalTime (r+d) w) ∧
          arrivalTime (r+d) w-arrivalTime r w ≤ 2 ∧
          coreFirstReadyAtOrAfter w (arrivalTime (r+d) w) (arrivalTime (r+d) w+τ 0) ∧
          (arrivalTime (r+d) w+τ 0)-arrivalTime (r+d) w ≤ 1/2
        refine ⟨hdiv0,by linarith [hdiv.2.1],?_,by linarith⟩
        simpa only [add_zero] using core_first_ready_suffix w hclock (r+d)
          (by norm_num : (0 : ℝ) ≤ 0) hτ0
      · change coreFirstDivisionAfter w (arrivalTime (r+d) w+τ j.castSucc)
          (arrivalTime (r+d) w+σ j) ∧
          (arrivalTime (r+d) w+σ j)-(arrivalTime (r+d) w+τ j.castSucc) ≤ 2 ∧
          coreFirstReadyAtOrAfter w (arrivalTime (r+d) w+σ j)
            (arrivalTime (r+d) w+τ j.succ) ∧
          (arrivalTime (r+d) w+τ j.succ)-(arrivalTime (r+d) w+σ j) ≤ 1/2
        exact ⟨core_first_division_suffix w (r+d) (hτ j.castSucc) (hsteps j).1,
          by linarith [(hsteps j).2.1],
          core_first_ready_suffix w hclock (r+d) (hσ j) (hsteps j).2.2.1,
          by linarith [(hsteps j).2.2.2]⟩
    · change arrivalTime (r+d) w+τ (Fin.last n) ≤ renewalHorizon (n+1)
      dsimp [renewalHorizon] at hlast ⊢
      rw [Nat.cast_add,Nat.cast_one]
      linarith

theorem physical_renewal_failure_bound (x : RecoveryCore) (old : Option RecoveryMark) :
    CF3MarkedKernel.eventLaw recoveryValid x old
      {w | (∀ t : ℝ, 0 ≤ t → t ≤ 51/2 → recoveryStateFloor (timedState t w)) ∧
        ¬coreRenewalSequence 10 w} ≤
      ENNReal.ofReal ((11/100000 : ℝ)+10*Real.exp (-8)) := by
  refine (measure_mono_ae ?_).trans (eleven_recovery_ten_division_failure_bound x old)
  filter_upwards [(CF3MarkedKernel.kernel recoveryValid).ae_holding_pos
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old),
    ae_arrivals_unbounded (CF3MarkedKernel.kernel recoveryValid)
      (CF3MarkedKernel.rate_positive recoveryValid) (x,old)] with w hpos hclock
  rintro ⟨hf,hbad⟩
  by_contra hw
  apply hbad
  apply nonfailure_gives_physical_renewal 10 w hpos hclock _ hw
  have hH : renewalHorizon 10 = (51/2 : ℝ) := by norm_num [renewalHorizon]
  simpa only [hH] using hf

end
end P161Formal
