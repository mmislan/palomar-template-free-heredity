module

public import P161Formal.SourceFiniteStockLaw

/-! Actual physical observations and cumulative gross ledgers. Unit counters
read executed positive labels; victim losses read their complete prestates.
Victim handling charges all3N catalyst positions per overwritten compartment.
The support theorem pays these charges from one initial fuel inventory. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators Classical
noncomputable section

local instance missionObsLiteralRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance missionObsLiteralRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance missionObsLiteralMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance missionObsLiteralMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩

theorem prefix_indicator_count {S : Type*} (P : S → Prop) (w : ℕ → ℝ × S) (n : ℕ) :
    (∑ k ∈ Finset.range n, if P (w (k+1)).2 then 1 else 0) = countAll P (statePrefix n w).tail := by
  induction n with
  | zero => simp [statePrefix_zero,countAll]
  | succ n ih =>
      rw [Finset.sum_range_succ,statePrefix_succ]
      cases hp : statePrefix n w with
      | nil =>
          have hl := congrArg List.length hp
          simp [statePrefix] at hl
      | cons a xs =>
          simp only [hp,List.cons_append,List.tail_cons,countAll_append,countAll,Nat.add_zero] at ih ⊢
          exact congrArg (fun k : ℕ => k+(if P (w (n+1)).2 then 1 else 0)) ih

theorem source_prefix_count_eq_selected (seed : ℝ)
    (f : Option (Mark (literalSourcePar seed)) → ℕ)
    (P : CF3MarkedKernel.State (literalSourcePar seed) → Prop)
    (hunit : ∀ y : CF3MarkedKernel.State (literalSourcePar seed), f y.2 = if P y then 1 else 0)
    (w : MarkedPath (literalSourcePar seed)) (t : ℝ) :
    sourcePrefixCount seed f w (clockIndex t w) = selectedCount P t w := by
  calc
    _ = ∑ k ∈ Finset.range (clockIndex t w), if P (w (k+1)).2 then 1 else 0 :=
      Finset.sum_congr rfl (fun k _ => hunit (w (k+1)).2)
    _ = _ := prefix_indicator_count P w (clockIndex t w)

theorem source_feed_unit (seed : ℝ) (y : CF3MarkedKernel.State (literalSourcePar seed)) :
    sourceMarkFeed y.2 = if sourceFeedState seed y then 1 else 0 := by
  rcases y with ⟨core,mark⟩
  cases mark with
  | none => simp [sourceMarkFeed,sourceFeedState,sourceFeedMark]
  | some m =>
      cases m with
      | inr d => simp [sourceMarkFeed,sourceFeedState,sourceFeedMark]
      | inl ik =>
          rcases ik with ⟨i,k⟩
          cases k with
          | inl tj => simp [sourceMarkFeed,sourceChemFeed,sourceFeedState,sourceFeedMark]
          | inr b => cases b <;> simp [sourceMarkFeed,sourceChemFeed,sourceFeedState,sourceFeedMark]

theorem source_seed_unit (seed : ℝ) (y : CF3MarkedKernel.State (literalSourcePar seed)) :
    sourceMarkSeeds y.2 = if sourceSeedState seed y then 1 else 0 := by
  rcases y with ⟨core,mark⟩
  cases mark with
  | none => simp [sourceMarkSeeds,sourceSeedState,sourceSeedMark]
  | some m =>
      cases m with
      | inr d => simp [sourceMarkSeeds,sourceSeedState,sourceSeedMark]
      | inl ik =>
          rcases ik with ⟨i,k⟩
          cases k with
          | inl tj =>
              rcases tj with ⟨t,j⟩
              by_cases ht : t = 0 <;> simp [sourceMarkSeeds,sourceSeedState,sourceSeedMark,ht]
          | inr b => cases b <;> simp [sourceMarkSeeds,sourceSeedState,sourceSeedMark]

theorem source_division_unit (seed : ℝ) (y : CF3MarkedKernel.State (literalSourcePar seed)) :
    sourceMarkDivision y.2 = if divisionState y then 1 else 0 := by
  rcases y with ⟨core,mark⟩
  cases mark with
  | none => simp [sourceMarkDivision,divisionState,isDivision]
  | some m => cases m <;> simp [sourceMarkDivision,divisionState,isDivision]

def sourceGlobalInitial (x : Raw) : SourceState (literalSourcePar 6) := sourceResetAll x

def sourceGlobalPrefix (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : ℕ := clockIndex t (wholePath z)

def globalSourceDivisionAt (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : Prop :=
  if t < 30 then physicalActualDivisionAt (wholePath z) t else physicalActualDivisionAt (offPath z) (t-30)

def sourcePhysicalObservations (x : Raw) (z : V4.TwoPhaseLaw.Completion) : MissionObservations where
  state t := sourcePopulation (seed := 0) (globalState x z t)
  credits t i j := (globalState x z t i).q j
  initiatingDivisions t i := (globalState x z t i).nd
  feed t := sourcePrefixCount 6 sourceMarkFeed (wholePath z) (sourceGlobalPrefix z t)
  seeds t := sourcePrefixCount 6 sourceMarkSeeds (wholePath z) (sourceGlobalPrefix z t)
  consumedFuel t := sourcePrefixCount 6 sourceMarkConsumed (wholePath z) (sourceGlobalPrefix z t)+
    sourcePrefixVictimFuel 6 (sourceGlobalInitial x) (wholePath z) (sourceGlobalPrefix z t)
  precursors t := sourcePrefixCount 6 sourceMarkBirths (wholePath z) (sourceGlobalPrefix z t)+
    sourcePrefixCount 6 sourceMarkSeeds (wholePath z) (sourceGlobalPrefix z t)
  divisions t := sourcePrefixCount 6 sourceMarkDivision (wholePath z) (sourceGlobalPrefix z t)
  victimSlots t := 3*2048*sourcePrefixCount 6 sourceMarkDivision (wholePath z) (sourceGlobalPrefix z t)
  victimFuel t := sourcePrefixVictimFuel 6 (sourceGlobalInitial x) (wholePath z) (sourceGlobalPrefix z t)
  isDivision t := globalSourceDivisionAt z t

theorem source_observations_feed (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) :
    (sourcePhysicalObservations x z).feed t = globalFeedCount z t :=
  source_prefix_count_eq_selected 6 sourceMarkFeed (sourceFeedState 6) (source_feed_unit 6) (wholePath z) t

theorem source_observations_seed (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) :
    (sourcePhysicalObservations x z).seeds t = globalSeedCount z t :=
  source_prefix_count_eq_selected 6 sourceMarkSeeds (sourceSeedState 6) (source_seed_unit 6) (wholePath z) t

theorem source_observations_division (x : Raw) (z : V4.TwoPhaseLaw.Completion) (t : ℝ) :
    (sourcePhysicalObservations x z).divisions t = globalDivisionCount z t :=
  source_prefix_count_eq_selected 6 sourceMarkDivision divisionState (source_division_unit 6) (wholePath z) t

theorem ae_source_observations_stock (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      idealResourceGood z.1 → stockMission (sourcePhysicalObservations x z) := by
  filter_upwards [ae_global_resource_prefix_caps x,completedSwitchLaw_ae_global_supported x] with z hc hs
  intro hg t ht ht60
  have hcap := hc hg t ht ht60
  have ha : sourcePrefixCount 6 sourceMarkFeed (wholePath z) (sourceGlobalPrefix z t) ≤ 800000000 := by
    rw [←source_observations_feed x z t] at hcap
    exact hcap.1
  have he : sourcePrefixCount 6 sourceMarkSeeds (wholePath z) (sourceGlobalPrefix z t) ≤ 5000 := by
    rw [←source_observations_seed x z t] at hcap
    exact hcap.2.1
  have hd : sourcePrefixCount 6 sourceMarkDivision (wholePath z) (sourceGlobalPrefix z t) ≤ 1200 := by
    rw [←source_observations_division x z t] at hcap
    exact hcap.2.2
  have hb := source_prefix_gross_caps 6 (by norm_num) (sourceGlobalInitial x) (wholePath z) hs
    (sourceGlobalPrefix z t) ha he hd
  exact ⟨ha,he,hb.1,hb.2.1,hd,hb.2.2.2,hb.2.2.1⟩

end
end P161Formal
