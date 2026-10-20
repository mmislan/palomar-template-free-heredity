module

public import P161Formal.SourceStoppedObservations
public import P161Formal.SourceIdealMissionBridge
public import Mathlib.Order.Fin.Basic

/-! Entire bounded mission transfer to the concrete stopped process. The
agreement is proved under the actual shared-stock event, never assumed as a
success law. First-divison witnesses remain actual positive-index labels. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped Classical ENNReal
noncomputable section

local instance stoppedMissionGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stoppedMissionGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance stoppedMissionGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stoppedMissionGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance stoppedMissionRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance stoppedMissionRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stoppedMissionMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance stoppedMissionMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

structure MissionAgreementThrough (a b : MissionObservations) : Prop where
  state : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.state t = b.state t
  credits : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.credits t = b.credits t
  initiatingDivisions : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.initiatingDivisions t = b.initiatingDivisions t
  feed : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.feed t = b.feed t
  seeds : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.seeds t = b.seeds t
  consumedFuel : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.consumedFuel t = b.consumedFuel t
  precursors : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.precursors t = b.precursors t
  divisions : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.divisions t = b.divisions t
  victimSlots : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.victimSlots t = b.victimSlots t
  victimFuel : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → a.victimFuel t = b.victimFuel t
  divisionEvent : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → (a.isDivision t ↔ b.isDivision t)

set_option backward.isDefEq.respectTransparency false in
theorem source_stopped_observations_agree (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 60 → sourceStockStateAt x z t =
      some (sourceStockAtPrefix x z (sourceGlobalPrefix z t))) :
    MissionAgreementThrough (sourceStoppedObservations x z) (sourcePhysicalObservations x z) := by
  constructor <;> intro t ht ht60
  all_goals simp only [sourceStoppedObservations,sourcePhysicalObservations,h t ht ht60,
    Option.map_some,Option.getD_some]
  case state =>
    exact congrArg (fun y : SourceState (literalSourcePar 6) => sourcePopulation (seed := 6) y)
      (source_stock_prefix_raw_time x z t)
  case credits =>
    exact congrArg (fun y : SourceState (literalSourcePar 6) => fun i j => (y i).q j)
      (source_stock_prefix_raw_time x z t)
  case initiatingDivisions =>
    exact congrArg (fun y : SourceState (literalSourcePar 6) => fun i => (y i).nd)
      (source_stock_prefix_raw_time x z t)
  case divisionEvent =>
    exact ⟨fun hd => hd.1,fun hd => ⟨hd,by simp⟩⟩
  all_goals rfl

namespace MissionAgreementThrough
variable {a b : MissionObservations} (h : MissionAgreementThrough a b)
include h

theorem firstReady {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 60)
    (hb : firstReadyAtOrAfter b s t) : firstReadyAtOrAfter a s t := by
  refine ⟨hb.1,?_,?_⟩
  · rw [h.state t (hs.trans hb.1) ht]
    exact hb.2.1
  · intro u hsu hut hu
    rw [h.state u (hs.trans hsu) (by linarith)] at hu
    exact hb.2.2 u hsu hut hu

theorem firstDivision {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 60)
    (hb : firstDivisionAfter b s t) : firstDivisionAfter a s t := by
  refine ⟨hb.1,(h.divisionEvent t (by linarith [hb.1]) ht).mpr hb.2.1,?_⟩
  intro u hsu hut hu
  exact hb.2.2 u hsu hut ((h.divisionEvent u (by linarith) (by linarith)).mp hu)

theorem renewal (hb : renewalMission b) : renewalMission a := by
  obtain ⟨τ,σ,hfirst,hhalf,hsteps,hlast⟩ := hb
  have hinc (r : Fin 10) : τ r.castSucc ≤ τ r.succ := by
    linarith [(hsteps r).1.1,(hsteps r).2.2.1.1]
  have hm : Monotone τ := Fin.monotone_iff_le_succ.mpr hinc
  have hτlower (i : Fin 11) : 0 ≤ τ i := by
    have hi := hm (show (0 : Fin 11) ≤ i by omega)
    linarith [hfirst.1]
  have hτupper (i : Fin 11) : τ i ≤ 60 := by
    have hi := hm (show i ≤ (10 : Fin 11) by have hi := i.isLt; omega)
    linarith
  have hσlower (r : Fin 10) : 0 ≤ σ r := by linarith [hτlower r.castSucc,(hsteps r).1.1]
  have hσupper (r : Fin 10) : σ r ≤ 60 := by linarith [hτupper r.succ,(hsteps r).2.2.1.1]
  refine ⟨τ,σ,h.firstReady (by norm_num) (hτupper 0) hfirst,hhalf,?_,hlast⟩
  intro r
  exact ⟨h.firstDivision (hτlower r.castSucc) (hσupper r) (hsteps r).1,
    (hsteps r).2.1,h.firstReady (hσlower r) (hτupper r.succ) (hsteps r).2.2.1,(hsteps r).2.2.2⟩

theorem complete (hb : completeMission b) : completeMission a := by
  refine ⟨?_,?_,h.renewal hb.2.2.1,?_,?_⟩
  · constructor
    · intro t ht ht30
      rw [h.state t ht (by linarith)]
      exact hb.1.1 t ht ht30
    · intro t ht30 ht60
      rw [h.state t (by linarith) ht60]
      exact hb.1.2 t ht30 ht60
  · constructor
    · intro n i j hj
      have hn0 : (0 : ℝ) ≤ n.val := Nat.cast_nonneg _
      have hn : (n.val : ℝ) ≤ 299 := by
        exact_mod_cast (show n.val ≤ 299 by have hn := n.isLt; omega)
      rw [h.credits ((n.val : ℝ)/10) (by positivity) (by linarith),
        h.credits (((n.val : ℝ)+1)/10) (by positivity) (by linarith)]
      exact hb.2.1.1 n i j hj
    · intro n i j
      have hn0 : (0 : ℝ) ≤ n.val := Nat.cast_nonneg _
      have hn : (n.val : ℝ) ≤ 299 := by
        exact_mod_cast (show n.val ≤ 299 by have hn := n.isLt; omega)
      rw [h.credits (30+(n.val : ℝ)/10) (by positivity) (by linarith),
        h.credits (30+((n.val : ℝ)+1)/10) (by positivity) (by linarith)]
      exact hb.2.1.2 n i j
  · intro t ht ht60
    rw [h.feed t ht ht60,h.seeds t ht ht60,h.consumedFuel t ht ht60,h.precursors t ht ht60,
      h.divisions t ht ht60,h.victimSlots t ht ht60,h.victimFuel t ht ht60]
    exact hb.2.2.2.1 t ht ht60
  · intro i
    rw [h.initiatingDivisions 30 (by norm_num) (by norm_num),
      h.initiatingDivisions 60 (by norm_num) (by norm_num)]
    exact hb.2.2.2.2 i

end MissionAgreementThrough

theorem ae_source_stopped_completeMission (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      idealCandidateMission x z → completeMission (sourceStoppedObservations x z) := by
  filter_upwards [ae_source_stock_matches_through_sixty x,ae_ideal_candidate_completeMission x] with z hs hi
  intro hg
  exact (source_stopped_observations_agree x z (hs hg.2.2)).complete (hi hg)

theorem source_stopped_completeMission_failure (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    V4.TwoPhaseLaw.completedSwitchLaw x {z | ¬completeMission (sourceStoppedObservations x z)} ≤
      ENNReal.ofReal failureCeiling := by
  refine (measure_mono_ae ?_).trans (ideal_candidate_failure_probability x hx)
  filter_upwards [ae_source_stopped_completeMission x] with z hz
  intro hbad hgood
  exact hbad (hz hgood)

end
end P161Formal
