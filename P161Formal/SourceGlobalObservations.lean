module

public import P161Formal.SourceRenewalObservation

/-! Absolute-time current-population renewal from the actual global count
path and executed off-phase division labels. The deterministic switch is at30;
its incoming sentinel is excluded and state-null actual divisions are kept. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped ENNReal Classical
noncomputable section

local instance globalObsRawMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (SourceState p) := ⊤
local instance globalObsRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance globalObsMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance globalObsMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

local instance globalObsRecoveryMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance globalObsRecoveryMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

theorem closed_grid_covers {P : ℝ → Prop} (n : ℕ) (d : ℝ)
    (hP : ∀ b : Fin (n+1), ∀ u : ℝ, 0 ≤ u → u ≤ d → P ((b.val : ℝ)*d+u)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ (n+1 : ℕ)*d → P t := by
  induction n with
  | zero =>
    intro t ht htT
    simpa only [Fin.val_zero,Nat.cast_zero,zero_mul,zero_add] using
      hP 0 t ht (by simpa only [Nat.zero_add,Nat.cast_one,one_mul] using htT)
  | succ n ih =>
    intro t ht htT
    by_cases hh : t ≤ (n+1 : ℕ)*d
    · exact ih (fun b => hP b.castSucc) t ht hh
    · have hlow : 0 ≤ t-(n+1 : ℕ)*d := by linarith
      have hhi : t-(n+1 : ℕ)*d ≤ d := by
        push_cast at htT ⊢
        linarith
      have hp := hP (Fin.last (n+1)) (t-(n+1 : ℕ)*d) hlow hhi
      have he : ((Fin.last (n+1)).val : ℝ)*d+(t-(n+1 : ℕ)*d) = t := by
        simp only [Fin.val_last]
        ring
      simpa only [he] using hp

def globalReadyAt (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : Prop :=
  V2.RecoveryStops.rawReady512 (p := literalSourcePar 0) (globalState x z t)

def globalFirstReadyAtOrAfter (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (start hit : ℝ) : Prop :=
  start ≤ hit ∧ globalReadyAt x z hit ∧
    ∀ t : ℝ, start ≤ t → t < hit → ¬globalReadyAt x z t

def globalFirstDivisionAfter (z : V4.TwoPhaseLaw.Completion) (start division : ℝ) : Prop :=
  start < division ∧ physicalActualDivisionAt (offPath z) (division-30) ∧
    ∀ t : ℝ, start < t → t < division → ¬physicalActualDivisionAt (offPath z) (t-30)

def globalRenewalMission (x : Raw) (z : V4.TwoPhaseLaw.Completion) : Prop :=
  ∃ (τ : Fin 11 → ℝ) (σ : Fin 10 → ℝ),
    (∀ i, 30 ≤ τ i) ∧ (∀ r, 30 ≤ σ r) ∧
    globalFirstReadyAtOrAfter x z 30 (τ 0) ∧ τ 0 ≤ 30+1/2 ∧
    (∀ r : Fin 10, globalFirstDivisionAfter z (τ r.castSucc) (σ r) ∧
      σ r-τ r.castSucc ≤ 2 ∧ globalFirstReadyAtOrAfter x z (σ r) (τ r.succ) ∧
      τ r.succ-σ r ≤ 1/2) ∧ τ 10 ≤ 111/2

set_option backward.isDefEq.respectTransparency false in
theorem global_ready_core_iff (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hc : ∀ t : ℝ, 0 ≤ t → coreProject (p := literalSourcePar 0)
      (globalState x z (30+t)) = (timedState t (offPath z)).1)
    (t : ℝ) (ht : 0 ≤ t) :
    globalReadyAt x z (30+t) ↔ recoveryStateReady (timedState t (offPath z)) := by
  have h := (V2.RecoveryStops.ready512_coreProject (p := literalSourcePar 0)
    (globalState x z (30+t))).symm
  simpa only [globalReadyAt,recoveryStateReady,hc t ht] using h

theorem global_first_ready_from_core (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hc : ∀ t : ℝ, 0 ≤ t → coreProject (p := literalSourcePar 0)
      (globalState x z (30+t)) = (timedState t (offPath z)).1)
    {a b : ℝ} (ha : 0 ≤ a) (hfirst : coreFirstReadyAtOrAfter (offPath z) a b) :
    globalFirstReadyAtOrAfter x z (30+a) (30+b) := by
  refine ⟨by linarith [hfirst.1],
    (global_ready_core_iff x z hc b (ha.trans hfirst.1)).mpr hfirst.2.1,?_⟩
  intro t hts htb hready
  have ht : 0 ≤ t-30 := by linarith
  have he : 30+(t-30) = t := by ring
  have hr : recoveryStateReady (timedState (t-30) (offPath z)) :=
    (global_ready_core_iff x z hc (t-30) ht).mp (by simpa only [he] using hready)
  exact hfirst.2.2 (t-30) (by linarith) (by linarith) hr

theorem global_first_division_from_core (z : V4.TwoPhaseLaw.Completion)
    {a b : ℝ} (hfirst : coreFirstDivisionAfter (offPath z) a b) :
    globalFirstDivisionAfter z (30+a) (30+b) := by
  have he : (30+b)-30 = b := by ring
  refine ⟨by linarith [hfirst.1],by simpa only [he] using hfirst.2.1,?_⟩
  intro t hts htb hdiv
  exact hfirst.2.2 (t-30) (by linarith) (by linarith) hdiv

theorem core_sequence_gives_global_renewal (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hc : ∀ t : ℝ, 0 ≤ t → coreProject (p := literalSourcePar 0)
      (globalState x z (30+t)) = (timedState t (offPath z)).1)
    (hseq : coreRenewalSequence 10 (offPath z)) : globalRenewalMission x z := by
  obtain ⟨τ,σ,hτ,hσ,hfirst,hhalf,hsteps,hlast⟩ := hseq
  refine ⟨fun i => 30+τ i,fun r => 30+σ r,fun i => by linarith [hτ i],
    fun r => by linarith [hσ r],?_,by linarith,?_,?_⟩
  · simpa only [add_zero] using global_first_ready_from_core x z hc (by norm_num : (0 : ℝ) ≤ 0) hfirst
  · intro r
    exact ⟨global_first_division_from_core z (hsteps r).1,by linarith [(hsteps r).2.1],
      global_first_ready_from_core x z hc (hσ r) (hsteps r).2.2.1,
      by linarith [(hsteps r).2.2.2]⟩
  · norm_num [renewalHorizon] at hlast
    change 30+τ (10 : Fin 11) ≤ 111/2
    linarith

set_option backward.isDefEq.respectTransparency false in
theorem continuous_event_off_floor (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hc : ∀ t : ℝ, 0 ≤ t → coreProject (p := literalSourcePar 0)
      (globalState x z (30+t)) = (timedState t (offPath z)).1)
    (hg : continuousEvent (globalRaw x z)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 51/2 → recoveryStateFloor (timedState t (offPath z)) := by
  have hblocks : ∀ b : Fin 300, ∀ u : ℝ, 0 ≤ u → u ≤ blockDuration →
      ¬sourceDead (p := literalSourcePar 0) 16 allSpecies
        (globalState x z (30+((b.val : ℝ)*blockDuration+u))) := by
    intro b u hu hud
    simpa only [globalState,offStart,onStart,add_assoc] using (hg.2.1 b).1 u hu hud
  have hcover := closed_grid_covers
    (P := fun t => ¬sourceDead (p := literalSourcePar 0) 16 allSpecies (globalState x z (30+t)))
    299 blockDuration hblocks
  intro t ht htT i j
  have ht30 : t ≤ (299+1 : ℕ)*blockDuration := by norm_num [blockDuration]; linarith
  have hsafe := hcover t ht ht30
  have hf : 16 ≤ ((globalState x z (30+t) i).a j).val := by
    by_contra hh
    exact hsafe ⟨i,j,Finset.mem_univ j,by omega⟩
  change 16 ≤ ((coreProject (p := literalSourcePar 0) (globalState x z (30+t)) i).1 j).val at hf
  rw [hc t ht] at hf
  exact hf

theorem g60_and_global_renewal_failure (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x
      {z | ¬continuousEvent (globalRaw x z) ∨ ¬globalRenewalMission x z} ≤
      ENNReal.ofReal ((9545923/9062500000 : ℝ)+11/100000+10*Real.exp (-8)) := by
  refine (measure_mono_ae ?_).trans (g60_and_renewal_protocol_failure x hx)
  filter_upwards [V4.TwoPhaseLaw.completedSwitchLaw_ae_clocks x,
    ae_global_after_switch_core x] with z hclocks hc
  intro hz
  by_cases hg : continuousEvent (globalRaw x z)
  · apply Or.inr
    by_contra hnon
    have hclock := offPath_clockSupport z hclocks.2.1 hclocks.2.2
    have hf : ∀ t : ℝ, 0 ≤ t → t ≤ renewalHorizon 10 →
        recoveryStateFloor (timedState t (offPath z)) := by
      have hH : renewalHorizon 10 = (51/2 : ℝ) := by norm_num [renewalHorizon]
      simpa only [hH] using continuous_event_off_floor x z hc hg
    have hseq := nonfailure_gives_physical_renewal 10 (offPath z) hclock.1 hclock.2.1 hf hnon
    have hbad := hz.resolve_left (fun hh => hh hg)
    exact hbad (core_sequence_gives_global_renewal x z hc hseq)
  · exact Or.inl hg

end
end P161Formal
