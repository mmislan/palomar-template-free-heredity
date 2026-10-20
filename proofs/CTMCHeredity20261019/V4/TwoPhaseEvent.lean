module

public import proofs.CTMCHeredity20261019.V4.TwoPhaseIdentity
public import proofs.CTMCHeredity20261019.V4.TwoPhaseLaw
public import proofs.CTMCHeredity20261019.V4.WindowSafety
public import proofs.CTMCHeredity20261019.V3.Observations

@[expose] public section

/-! # One actual global observation event for the canonical switched source

The path law is the pushforward of the normalized completed V2 switched law.
Its measurable event covers every old-species window before30, every all-species
window after30, credit increments500, and nd(30)+5<=nd(60) at each spatial slot.
The counted-window predicate is exactly all physical times on the proved clock
support. Its probability equals the existing literal two-source blocks value;
no lower bound or common-clock/finite-stock identification is asserted.
-/

namespace CTMCHeredity20261019.V4.TwoPhaseEvent

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V2.LedgerOffsets V2.NoBoundaryArrival
open TwoPhaseIdentity WindowSafety
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

abbrev RawPath := RawOperated.RawPath seedOff

def onStart (b : Fin 300) : ℝ := (b.val : ℝ)*blockDuration
def offStart (b : Fin 300) : ℝ := 30 + onStart b

def windowService (req : Finset (Fin 3)) (a b : ℝ) (w : RawPath) : Prop :=
  ∀ i, ∀ j ∈ req,
    (timedState a w i).q j + 500 ≤ (timedState b w i).q j

def pathPhase (req : Finset (Fin 3)) (start : Fin 300 → ℝ) (w : RawPath) : Prop :=
  ∀ b, windowSafe (fun y : Raw => ¬sourceDead 16 req y)
      (start b) (start b + blockDuration) w ∧
    windowService req (start b) (start b + blockDuration) w

/-- One measurable global-path event: all windows and the post-switch division
increment. Absolute cumulative terminal nd>=5 is not substituted. -/
def pathEvent (w : RawPath) : Prop :=
  pathPhase oldSpecies onStart w ∧ pathPhase allSpecies offStart w ∧
    ∀ i, (timedState 30 w i).nd + 5 ≤ (timedState 60 w i).nd

def continuousPhase (req : Finset (Fin 3)) (start : Fin 300 → ℝ) (w : RawPath) : Prop :=
  ∀ b, (∀ u : ℝ, 0 ≤ u → u ≤ blockDuration →
      ¬sourceDead 16 req (timedState (start b + u) w)) ∧
    windowService req (start b) (start b + blockDuration) w

def continuousEvent (w : RawPath) : Prop :=
  continuousPhase oldSpecies onStart w ∧ continuousPhase allSpecies offStart w ∧
    ∀ i, (timedState 30 w i).nd + 5 ≤ (timedState 60 w i).nd

theorem measurableSet_windowService (req : Finset (Fin 3)) (a b : ℝ) :
    MeasurableSet {w : RawPath | windowService req a b w} := by
  have hs : MeasurableSet {y : Raw × Raw | ∀ i, ∀ j ∈ req,
      (y.1 i).q j + 500 ≤ (y.2 i).q j} := (Set.to_countable _).measurableSet
  exact hs.preimage ((measurable_timedState a).prodMk (measurable_timedState b))

theorem measurableSet_pathPhase (req : Finset (Fin 3)) (start : Fin 300 → ℝ) :
    MeasurableSet {w : RawPath | pathPhase req start w} := by
  have he : {w : RawPath | pathPhase req start w} = ⋂ b : Fin 300,
      {w : RawPath | windowSafe (fun y : Raw => ¬sourceDead 16 req y)
        (start b) (start b + blockDuration) w ∧
        windowService req (start b) (start b + blockDuration) w} := by
    ext w
    simp [pathPhase]
  rw [he]
  apply MeasurableSet.iInter
  intro b
  exact (measurableSet_windowSafe (fun y : Raw => ¬sourceDead 16 req y)
    (Set.to_countable _).measurableSet (start b) (start b + blockDuration)).inter
      (measurableSet_windowService req (start b) (start b + blockDuration))

theorem measurableSet_pathEvent : MeasurableSet {w : RawPath | pathEvent w} := by
  have hd : MeasurableSet {y : Raw × Raw | ∀ i, (y.1 i).nd + 5 ≤ (y.2 i).nd} :=
    (Set.to_countable _).measurableSet
  exact (measurableSet_pathPhase oldSpecies onStart).inter
    ((measurableSet_pathPhase allSpecies offStart).inter
      (hd.preimage ((measurable_timedState 30).prodMk (measurable_timedState 60))))

theorem measurable_offPath : Measurable offPath := by
  exact (PhysicalOperated.measurable_stitch seedOff blockDuration 300).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem measurable_wholePath : Measurable wholePath := by
  exact (PhysicalOperated.measurable_stitch canonicalSeedOnCF3 blockDuration 300).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_offPath)

theorem measurable_globalRaw (x : Raw) : Measurable (globalRaw x) :=
  (measurable_rawSequence canonicalSeedOnCF3 (sourceResetAll x)).comp measurable_wholePath

theorem globalRaw_clockSupport (z : TwoPhaseIdentity.Completion)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) (x : Raw) :
    ClockBoundarySupport ∅ (globalRaw x z) := by
  change ClockBoundarySupport ∅ (wholePath z)
  exact OperatedObservations.stitch_clockSupport canonicalSeedOnCF3 blockDuration
    blockDuration_nonneg 300 z.1.1 (offPath z) hon (offPath_clockSupport z hoff hv)

theorem pathPhase_iff_continuous (req : Finset (Fin 3)) (start : Fin 300 → ℝ)
    (w : RawPath) (ha : ∀ b, 0 ≤ start b) (hw : ClockBoundarySupport ∅ w) :
    pathPhase req start w ↔ continuousPhase req start w := by
  apply forall_congr'
  intro b
  exact and_congr (windowSafe_iff_local _ _ _ w (ha b) blockDuration_nonneg hw) Iff.rfl

theorem pathEvent_iff_continuous (w : RawPath) (hw : ClockBoundarySupport ∅ w) :
    pathEvent w ↔ continuousEvent w := by
  have ha (b : Fin 300) : 0 ≤ onStart b :=
    mul_nonneg (Nat.cast_nonneg b.val) blockDuration_nonneg
  have hb (b : Fin 300) : 0 ≤ offStart b := add_nonneg (by norm_num) (ha b)
  exact and_congr (pathPhase_iff_continuous oldSpecies onStart w ha hw)
    (and_congr (pathPhase_iff_continuous allSpecies offStart w hb hw) Iff.rfl)

/-- A generic logical corollary of the already proved exact state identity.
Zero local q is separately established from actual compatible initialization. -/
theorem physicalPhase_iff_pathPhase (req : Finset (Fin 3))
    (h : RawOperated.History seedOff 300) (w : RawPath) (start : Fin 300 → ℝ)
    (oq : Fin 300 → Fin 4 → Fin 3 → ℕ) (ond : Fin 4 → ℕ)
    (hw : ClockBoundarySupport ∅ w) (ha : ∀ b, 0 ≤ start b)
    (hs : ∀ b : Fin 300, ∀ u : ℝ, 0 ≤ u → u ≤ blockDuration →
      timedState (start b + u) w =
        addLedgers seedOff (timedState u (h.1 b).2) (oq b) ond)
    (hz : ∀ b : Fin 300, ∀ i j, (timedState 0 (h.1 b).2 i).q j = 0) :
    physicalPhase req h ↔ pathPhase req start w := by
  constructor <;> intro hp b
  · refine ⟨(windowSafe_iff_local _ _ _ w (ha b) blockDuration_nonneg hw).mpr ?_, ?_⟩
    · intro u hu hud
      rw [hs b u hu hud]
      exact (hp b).1 u hu hud
    · intro i j hj
      have he := congrArg (fun y : Raw => (y i).q j) (hs b blockDuration blockDuration_nonneg le_rfl)
      have hb := congrArg (fun y : Raw => (y i).q j) (hs b 0 le_rfl blockDuration_nonneg)
      change (timedState (start b+blockDuration) w i).q j =
        (timedState blockDuration (h.1 b).2 i).q j + oq b i j at he
      change (timedState (start b+0) w i).q j =
        (timedState 0 (h.1 b).2 i).q j + oq b i j at hb
      rw [hz b i j, zero_add, add_zero] at hb
      change (timedState (start b) w i).q j + 500 ≤ _
      rw [he, hb]
      have hv := (hp b).2 i j hj
      omega
  · refine ⟨?_, ?_⟩
    · intro u hu hud
      have hv := (windowSafe_iff_local _ _ _ w (ha b) blockDuration_nonneg hw).mp (hp b).1 u hu hud
      rw [hs b u hu hud] at hv
      exact hv
    · intro i j hj
      have he := congrArg (fun y : Raw => (y i).q j) (hs b blockDuration blockDuration_nonneg le_rfl)
      have hb := congrArg (fun y : Raw => (y i).q j) (hs b 0 le_rfl blockDuration_nonneg)
      change (timedState (start b+blockDuration) w i).q j =
        (timedState blockDuration (h.1 b).2 i).q j + oq b i j at he
      change (timedState (start b+0) w i).q j =
        (timedState 0 (h.1 b).2 i).q j + oq b i j at hb
      rw [hz b i j, zero_add, add_zero] at hb
      have hv := (hp b).2 i j hj
      change (timedState (start b) w i).q j + 500 ≤ _ at hv
      rw [he, hb] at hv
      omega

private theorem added_nd (y : Raw) (oq : Fin 4 → Fin 3 → ℕ)
    (ond : Fin 4 → ℕ) (i : Fin 4) :
    (addLedgers seedOff y oq ond i).nd = (y i).nd + ond i := rfl

theorem physicalSwitch_iff_pathEvent (x : Raw) (z : TwoPhaseIdentity.Completion)
    (hc : jointCompatible x z.1) (hf : jointFaithful z.1)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) :
    physicalSwitch z.1 ↔ pathEvent (globalRaw x z) := by
  have hi := two_phase_windows_and_terminal x z hc hf hon hoff hv
  have hcut := (on_windows_and_switch x z hc hf hon hoff hv).2
  have hw := globalRaw_clockSupport z hon hoff hv x
  have hzOn (b : Fin 300) (i : Fin 4) (j : Fin 3) :
      (timedState 0 (z.1.1.1 b).2 i).q j = 0 := by
    exact (congrArg (fun y : SourceState canonicalSeedOnCF3 => (y i).q j)
      (V3.Observations.faithful_timed_zero _ _ (hf.1 b) (hon b))).trans
        (V3.Observations.compatible_start_q_zero canonicalSeedOnCF3 blockDuration 300
          (sourceResetAll x) z.1.1 hc.1 (fun _ _ => rfl) b i j)
  have hzOff (b : Fin 300) (i : Fin 4) (j : Fin 3) :
      (timedState 0 (z.1.2.1 b).2 i).q j = 0 := by
    exact (congrArg (fun y : Raw => (y i).q j)
      (V3.Observations.faithful_timed_zero _ _ (hf.2 b) (hoff b))).trans
        (V3.Observations.compatible_start_q_zero seedOff blockDuration 300
          (sourceResetAll z.1.1.2) z.1.2 hc.2 (fun _ _ => rfl) b i j)
  have ha (b : Fin 300) : 0 ≤ onStart b :=
    mul_nonneg (Nat.cast_nonneg b.val) blockDuration_nonneg
  have hb (b : Fin 300) : 0 ≤ offStart b := add_nonneg (by norm_num) (ha b)
  have hOn := physicalPhase_iff_pathPhase oldSpecies z.1.1 (globalRaw x z) onStart
    (fun b => onOffset z.1 b.val) (fun _ => 0) hw ha hi.1 hzOn
  have hOffState (b : Fin 300) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ blockDuration) :
      timedState (offStart b + u) (globalRaw x z) =
        addLedgers seedOff (timedState u (z.1.2.1 b).2)
          (offOffset z.1 b.val) (switchDivisions z.1) := by
    have ht : offStart b + u = 30 + ((b.val : ℝ)*blockDuration+u) := by
      unfold offStart onStart
      ring
    rw [ht]
    exact hi.2.1 b u hu hud
  have hOff := physicalPhase_iff_pathPhase allSpecies z.1.2 (globalRaw x z) offStart
    (fun b => offOffset z.1 b.val) (switchDivisions z.1) hw hb hOffState hzOff
  have hd : (∀ i, 5 ≤ (z.1.2.2 i).nd) ↔
      ∀ i, (timedState 30 (globalRaw x z) i).nd+5 ≤ (timedState 60 (globalRaw x z) i).nd := by
    apply forall_congr'
    intro i
    change 5 ≤ (z.1.2.2 i).nd ↔ (globalState x z 30 i).nd+5 ≤ (globalState x z 60 i).nd
    have hcN : (globalState x z 30 i).nd = (z.1.1.2 i).nd :=
      (congrArg (fun y : Raw => (y i).nd) hcut).trans (Nat.add_zero _)
    have hfN : (globalState x z 60 i).nd = (z.1.2.2 i).nd + (z.1.1.2 i).nd :=
      (congrArg (fun y : Raw => (y i).nd) hi.2.2).trans
        (added_nd z.1.2.2 (offOffset z.1 300) (switchDivisions z.1) i)
    rw [hcN, hfN]
    omega
  exact and_congr hOn (and_congr hOff hd)

/-- One actual joint draw simultaneously satisfies all deterministic window
identities, the restored switch state, and the full global event equivalence. -/
theorem completedSwitchLaw_ae_event_iff (x : Raw) :
    ∀ᵐ z ∂TwoPhaseLaw.completedSwitchLaw x,
      physicalSwitch z.1 ↔ pathEvent (globalRaw x z) := by
  filter_upwards [TwoPhaseLaw.completedSwitchLaw_ae_support x] with z hs
  exact physicalSwitch_iff_pathEvent x z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

theorem completedSwitchLaw_ae_continuous_event_iff (x : Raw) :
    ∀ᵐ z ∂TwoPhaseLaw.completedSwitchLaw x,
      pathEvent (globalRaw x z) ↔ continuousEvent (globalRaw x z) := by
  filter_upwards [TwoPhaseLaw.completedSwitchLaw_ae_clocks x] with z hs
  exact pathEvent_iff_continuous _ (globalRaw_clockSupport z hs.1 hs.2.1 hs.2.2 x)

/-- All observation identities and the single physical event hold on one joint
full-measure set. q offsets remain spatial; nd is carried once at the switch. -/
def observationContract (x : Raw) (z : TwoPhaseIdentity.Completion) : Prop :=
  (∀ b : Fin 300, ∀ t : ℝ, 0 ≤ t → t ≤ blockDuration →
    globalState x z ((b.val : ℝ)*blockDuration+t) =
      addLedgers seedOff (timedState t (z.1.1.1 b).2) (onOffset z.1 b.val) (fun _ => 0)) ∧
  (∀ b : Fin 300, ∀ t : ℝ, 0 ≤ t → t ≤ blockDuration →
    globalState x z (30+((b.val : ℝ)*blockDuration+t)) =
      addLedgers seedOff (timedState t (z.1.2.1 b).2)
        (offOffset z.1 b.val) (switchDivisions z.1)) ∧
  globalState x z 30 = switchState z.1 ∧
  globalState x z 60 = addLedgers seedOff z.1.2.2 (offOffset z.1 300) (switchDivisions z.1) ∧
  (physicalSwitch z.1 ↔ continuousEvent (globalRaw x z))

theorem completedSwitchLaw_ae_observationContract (x : Raw) :
    ∀ᵐ z ∂TwoPhaseLaw.completedSwitchLaw x, observationContract x z := by
  filter_upwards [TwoPhaseLaw.completedSwitchLaw_ae_support x] with z hs
  have hi := two_phase_windows_and_terminal x z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hcut := (on_windows_and_switch x z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2).2
  have he := physicalSwitch_iff_pathEvent x z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hk := globalRaw_clockSupport z hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 x
  exact ⟨hi.1, hi.2.1, hcut, hi.2.2, he.trans (pathEvent_iff_continuous _ hk)⟩

/-- The actual global source path law, built from both sampled phase vectors
and the actual seed-free terminal path. Initial counters are reset explicitly. -/
def pathLaw (x : Raw) : Measure RawPath :=
  (TwoPhaseLaw.completedSwitchLaw x).map (globalRaw x)

instance pathLaw_probability (x : Raw) : IsProbabilityMeasure (pathLaw x) := by
  unfold pathLaw
  infer_instance

theorem pathLaw_ae_clockSupport (x : Raw) :
    ∀ᵐ w ∂pathLaw x, ClockBoundarySupport ∅ w := by
  apply (ae_map_iff (measurable_globalRaw x).aemeasurable
    (measurableSet_clockBoundarySupport ∅ Set.countable_empty)).mpr
  filter_upwards [TwoPhaseLaw.completedSwitchLaw_ae_clocks x] with z hs
  exact globalRaw_clockSupport z hs.1 hs.2.1 hs.2.2 x

theorem pathLaw_event_probability (x : Raw) :
    pathLaw x {w | pathEvent w} = ENNReal.ofReal (switchedSourceValue x) := by
  have hg := goodSwitch_ae_physical x
  rw [← TwoPhaseLaw.completedSwitchLaw_fst x] at hg
  have hg' := ae_of_ae_map measurable_fst.aemeasurable hg
  rw [pathLaw, Measure.map_apply (measurable_globalRaw x) measurableSet_pathEvent]
  calc
    _ = TwoPhaseLaw.completedSwitchLaw x {z | goodSwitch z.1} := by
      apply measure_congr
      filter_upwards [completedSwitchLaw_ae_event_iff x, hg'] with z he hh
      exact propext (he.symm.trans (Iff.of_eq hh).symm)
    _ = (TwoPhaseLaw.completedSwitchLaw x).map Prod.fst {h | goodSwitch h} :=
      (Measure.map_apply measurable_fst measurableSet_goodSwitch).symm
    _ = _ := by rw [TwoPhaseLaw.completedSwitchLaw_fst, switchedLaw_good_probability]

theorem pathLaw_nullMeasurableSet_continuousEvent (x : Raw) :
    NullMeasurableSet {w : RawPath | continuousEvent w} (pathLaw x) := by
  apply measurableSet_pathEvent.nullMeasurableSet.congr
  filter_upwards [pathLaw_ae_clockSupport x] with w hw
  exact propext (pathEvent_iff_continuous w hw)

/-- Literal all-time floors, every500-credit window, and the post-switch nd
increment form one event with exactly the existing two-source blocks value. -/
theorem pathLaw_continuous_event_probability (x : Raw) :
    pathLaw x {w | continuousEvent w} = ENNReal.ofReal (switchedSourceValue x) := by
  calc
    _ = pathLaw x {w | pathEvent w} := by
      apply measure_congr
      filter_upwards [pathLaw_ae_clockSupport x] with w hw
      exact propext (pathEvent_iff_continuous w hw).symm
    _ = _ := pathLaw_event_probability x

end
end CTMCHeredity20261019.V4.TwoPhaseEvent
