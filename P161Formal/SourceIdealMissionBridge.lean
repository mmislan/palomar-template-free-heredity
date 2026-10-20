module

public import P161Formal.SourceMissionObservations

/-! The complete explicit observation event for the ideal switched source.
The finite-stock transfer consumes this event and the already proved shared
gross-ledger coupling; this module alone is not the finite-stock flagship. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped Classical ENNReal
noncomputable section

local instance idealBridgeRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance idealBridgeRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance idealBridgeMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance idealBridgeMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

theorem old_species_mem_of_lt_two (j : SpeciesId) (hj : j.val < 2) : j ∈ oldSpecies := by
  fin_cases j <;> simp [oldSpecies]
  norm_num at hj

set_option backward.isDefEq.respectTransparency false in
theorem continuous_event_observations_floors (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hg : continuousEvent (globalRaw x z)) : protectedFloors (sourcePhysicalObservations x z) := by
  have hon : ∀ b : Fin 300, ∀ u : ℝ, 0 ≤ u → u ≤ blockDuration →
      ¬sourceDead (p := literalSourcePar 0) 16 oldSpecies
        (globalState x z ((b.val : ℝ)*blockDuration+u)) := by
    intro b u hu hud
    simpa only [globalState,onStart] using (hg.1 b).1 u hu hud
  have hoff : ∀ b : Fin 300, ∀ u : ℝ, 0 ≤ u → u ≤ blockDuration →
      ¬sourceDead (p := literalSourcePar 0) 16 allSpecies
        (globalState x z (30+((b.val : ℝ)*blockDuration+u))) := by
    intro b u hu hud
    simpa only [globalState,offStart,onStart,add_assoc] using (hg.2.1 b).1 u hu hud
  have hOld := closed_grid_covers
    (P := fun t => ¬sourceDead (p := literalSourcePar 0) 16 oldSpecies (globalState x z t))
    299 blockDuration hon
  have hAll := closed_grid_covers
    (P := fun t => ¬sourceDead (p := literalSourcePar 0) 16 allSpecies (globalState x z (30+t)))
    299 blockDuration hoff
  constructor
  · intro t ht ht30 i j hj
    have hT : t ≤ ((299+1 : ℕ) : ℝ)*blockDuration := by norm_num [blockDuration]; exact ht30
    have hs := hOld t ht hT
    change 16 ≤ ((globalState x z t i).a j).val
    by_contra hlow
    exact hs ⟨i,j,old_species_mem_of_lt_two j hj,by omega⟩
  · intro t ht30 ht60 i j _
    have hT : t-30 ≤ ((299+1 : ℕ) : ℝ)*blockDuration := by norm_num [blockDuration]; linarith
    have hs := hAll (t-30) (by linarith) hT
    rw [show (30 : ℝ)+(t-30) = t by ring] at hs
    change 16 ≤ ((globalState x z t i).a j).val
    by_contra hlow
    exact hs ⟨i,j,Finset.mem_univ j,by omega⟩

set_option backward.isDefEq.respectTransparency false in
theorem continuous_event_observations_service (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hg : continuousEvent (globalRaw x z)) : fixedGridService (sourcePhysicalObservations x z) := by
  constructor
  · intro b i j hj
    have h := (hg.1 b).2 i j (old_species_mem_of_lt_two j hj)
    have h0 : onStart b = (b.val : ℝ)/10 := by unfold onStart blockDuration; ring
    have h1 : onStart b+blockDuration = ((b.val : ℝ)+1)/10 := by unfold onStart blockDuration; ring
    change (globalState x z (onStart b) i).q j+500 ≤
      (globalState x z (onStart b+blockDuration) i).q j at h
    rw [h1,h0] at h
    exact h
  · intro b i j
    have h := (hg.2.1 b).2 i j (Finset.mem_univ j)
    have h0 : offStart b = 30+(b.val : ℝ)/10 := by unfold offStart onStart blockDuration; ring
    have h1 : offStart b+blockDuration = 30+((b.val : ℝ)+1)/10 := by unfold offStart onStart blockDuration; ring
    change (globalState x z (offStart b) i).q j+500 ≤
      (globalState x z (offStart b+blockDuration) i).q j at h
    rw [h1,h0] at h
    exact h

theorem global_first_ready_to_observations (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    {a b : ℝ} (h : globalFirstReadyAtOrAfter x z a b) :
    firstReadyAtOrAfter (sourcePhysicalObservations x z) a b := h

theorem global_first_division_to_observations (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    {a b : ℝ} (ha : 30 ≤ a) (h : globalFirstDivisionAfter z a b) :
    firstDivisionAfter (sourcePhysicalObservations x z) a b := by
  refine ⟨h.1,?_,?_⟩
  · change globalSourceDivisionAt z b
    rw [globalSourceDivisionAt,ite_eq_right (show ¬b < 30 by linarith [h.1])]
    exact h.2.1
  · intro t hat htb hd
    change globalSourceDivisionAt z t at hd
    rw [globalSourceDivisionAt,ite_eq_right (show ¬t < 30 by linarith)] at hd
    exact h.2.2 t hat htb hd

theorem global_renewal_to_observations (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hg : globalRenewalMission x z) : renewalMission (sourcePhysicalObservations x z) := by
  obtain ⟨τ,σ,hτ,_hσ,hfirst,hhalf,hsteps,hlast⟩ := hg
  refine ⟨τ,σ,global_first_ready_to_observations x z hfirst,hhalf,?_,hlast⟩
  intro r
  exact ⟨global_first_division_to_observations x z (hτ r.castSucc) (hsteps r).1,
    (hsteps r).2.1,global_first_ready_to_observations x z (hsteps r).2.2.1,(hsteps r).2.2.2⟩

theorem ae_ideal_candidate_completeMission (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      idealCandidateMission x z → completeMission (sourcePhysicalObservations x z) := by
  filter_upwards [ae_source_observations_stock x] with z hs
  intro hg
  exact ⟨continuous_event_observations_floors x z hg.1,
    continuous_event_observations_service x z hg.1,global_renewal_to_observations x z hg.2.1,
    hs hg.2.2,hg.1.2.2⟩

theorem ideal_completeMission_failure_probability (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬completeMission (sourcePhysicalObservations x z)} ≤
      ENNReal.ofReal failureCeiling := by
  refine (measure_mono_ae ?_).trans (ideal_candidate_failure_probability x hx)
  filter_upwards [ae_ideal_candidate_completeMission x] with z hz
  intro hbad hgood
  exact hbad (hz hgood)

end
end P161Formal
