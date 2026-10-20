module

public import proofs.CTMCHeredity20261019.V2.OperatedKernel
public import proofs.CTMCHeredity20261019.V2.NoBoundaryArrival
public import proofs.CTMCHeredity20261019.CF3CappedPathLaw

@[expose] public section

/-!
# Version 2: joint operated original-ledger CF3 histories

Every segment retains both the original marked path and its exact raw source
fold, with unchanged holding times. Ordinary block boundaries reset only q at
the actual raw physical endpoint. Initial resetAll is supplied explicitly by
callers. There is no hidden stock reset or fresh gross-resource allocation.
Each phase uses its actual source envelope; equality with a common-clock
seed-erasure proposal construction remains a separate owned obligation.
-/

namespace CTMCHeredity20261019.V2.RawOperated

open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Natural-valued service/division ledgers make the source countable, not finite. -/
instance countableSite (c N : ℕ) : Countable (Site c N) := by
  have hi : Function.Injective (fun s : Site c N => (s.a, s.R, s.q, s.nd)) := by
    intro s t h
    cases s
    cases t
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  exact hi.countable

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) (Q D : ℕ) : MeasurableSpace (CappedState p Q D) := ⊤
local instance (p : Par) (Q D : ℕ) : MeasurableSingletonClass (CappedState p Q D) :=
  ⟨fun _ => trivial⟩

abbrev RawPath (p : Par) := ℕ → ℝ × SourceState p
abbrev Segment (p : Par) := MarkedPath p × RawPath p
abbrev History (p : Par) (n : ℕ) := Operated.History (SourceState p) (Segment p) n

def rawPair (p : Par) (x : SourceState p) (w : MarkedPath p) : Segment p :=
  (w, rawSequence p x w)

theorem measurable_rawPair (p : Par) (x : SourceState p) : Measurable (rawPair p x) :=
  measurable_id.prodMk (measurable_rawSequence p x)

/-- The actual finite marked law, paired with its original natural-ledger fold.
The fresh coordinate-zero last-mark sentinel is explicitly none. -/
def segmentKernel {p : Par} (hp : p.Valid) : ProbabilityTheory.Kernel (SourceState p) (Segment p) where
  toFun x := (CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x)
  measurable' := measurable_of_countable _

instance segmentKernel_markov {p : Par} (hp : p.Valid) : IsMarkovKernel (segmentKernel hp) where
  isProbabilityMeasure x := by
    constructor
    change ((CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x)) Set.univ = 1
    rw [Measure.map_apply (measurable_rawPair p x) MeasurableSet.univ]
    simp

/-- The next ordinary service block starts at the output-reset actual endpoint.
Counts, fuel, and division ledgers retain their source values. -/
def nextState (p : Par) (T : ℝ) (s : Segment p) : SourceState p :=
  sourceResetQ (timedState T s.2)

theorem measurable_nextState (p : Par) (T : ℝ) : Measurable (nextState p T) := by
  change Measurable (fun s : Segment p => sourceResetQ (timedState T s.2))
  simpa only [Function.comp_def] using
    (measurable_of_countable (sourceResetQ (p := p))).comp
      ((measurable_timedState (S := SourceState p) T).comp measurable_snd)

def rawLaw {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    Measure (History p n) :=
  Operated.law (segmentKernel hp) (nextState p T) (measurable_nextState p T) n x

instance rawLaw_probability {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    IsProbabilityMeasure (rawLaw hp T n x) := by unfold rawLaw; infer_instance

def rawKernel {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) :
    ProbabilityTheory.Kernel (SourceState p) (History p n) :=
  Operated.kernel (segmentKernel hp) (nextState p T) (measurable_nextState p T) n

instance rawKernel_markov {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) :
    IsMarkovKernel (rawKernel hp T n) := by unfold rawKernel; infer_instance

theorem rawLaw_lintegral_step {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p)
    (F : History p (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F h ∂rawLaw hp T (n + 1) x) =
      ∫⁻ s, ∫⁻ h, F (Operated.prepend n (s, h))
        ∂rawLaw hp T n (nextState p T s) ∂segmentKernel hp x :=
  Operated.law_lintegral_step (segmentKernel hp) (nextState p T)
    (measurable_nextState p T) n x F hF

def capPath (p : Par) (Q D : ℕ) (w : RawPath p) : SourceBlockProtocol.Path (CappedState p Q D) :=
  fun k => ((w k).1, capProject Q D (w k).2)

theorem measurable_capPath (p : Par) (Q D : ℕ) : Measurable (capPath p Q D) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) k).fst.prodMk
    ((measurable_of_countable (capProject (p := p) Q D)).comp
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) k).snd)

def cappedSegment (p : Par) (Q D : ℕ) (s : Segment p) :
    SourceBlockProtocol.Path (CappedState p Q D) := capPath p Q D s.2

theorem measurable_cappedSegment (p : Par) (Q D : ℕ) : Measurable (cappedSegment p Q D) := by
  change Measurable (fun s : Segment p => capPath p Q D s.2)
  simpa only [Function.comp_def] using
    (measurable_capPath p Q D).comp (measurable_snd : Measurable (fun s : Segment p => s.2))

@[simp] theorem capPath_timedState (p : Par) (Q D : ℕ) (w : RawPath p) (t : ℝ) :
    timedState t (capPath p Q D w) = capProject Q D (timedState t w) := rfl

/-- The source output reset and physical endpoint commute with the cap on every
segment, independently of any probability-one support assertion. -/
theorem nextState_cap (p : Par) (T : ℝ) (Q D : ℕ) (s : Segment p) :
    capProject Q D (nextState p T s) =
      cappedResetQ (timedState T (cappedSegment p Q D s)) :=
  sourceResetQ_project Q D (timedState T s.2)

/-- Source-instantiated whole segment projection, with the raw fold and all
holds retained. This discharges the generic history theorem's segment premise. -/
theorem segmentKernel_capped {p : Par} (hp : p.Valid) (Q D : ℕ) (x : SourceState p) :
    ((segmentKernel hp) x).map (cappedSegment p Q D) =
      (CF3CappedPathLaw.cappedKernel hp Q D).eventLaw (cf3Rate p)
        (CF3MarkedKernel.rate_positive hp) (capProject Q D x) := by
  change ((CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x)).map
      (cappedSegment p Q D) = _
  rw [Measure.map_map (measurable_cappedSegment p Q D) (measurable_rawPair p x)]
  exact CF3CappedPathLaw.eventLaw_cappedSequence hp x none Q D

def capHistory (p : Par) (Q D n : ℕ) :
    History p n → SourceBlockProtocol.History (CappedState p Q D) n :=
  Operated.historyMap (capProject Q D) (cappedSegment p Q D) n

theorem measurable_capHistory (p : Par) (Q D n : ℕ) : Measurable (capHistory p Q D n) :=
  Operated.measurable_historyMap (measurable_of_countable _) (measurable_cappedSegment p Q D) n

/-- Full finite-vector equality: every retained marked/raw block and the final
raw state project to the sealed capped ambient operated law. -/
theorem rawLaw_capHistory {p : Par} (hp : p.Valid) (T : ℝ) (Q D n : ℕ) (x : SourceState p) :
    (rawLaw hp T n x).map (capHistory p Q D n) =
      SourceBlockAmbient.ambientLaw (CF3CappedPathLaw.cappedKernel hp Q D)
        (CF3MarkedKernel.rate_positive hp) T cappedResetQ n (capProject Q D x) := by
  have h := Operated.law_map (segmentKernel hp)
    (Operated.eventSegmentKernel (CF3CappedPathLaw.cappedKernel hp Q D)
      (CF3MarkedKernel.rate_positive hp))
    (nextState p T) (measurable_nextState p T)
    (fun w => cappedResetQ (timedState T w)) (Operated.measurable_resetEndpoint T cappedResetQ)
    (capProject Q D) (measurable_of_countable _) (cappedSegment p Q D)
    (measurable_cappedSegment p Q D) (segmentKernel_capped hp Q D)
    (nextState_cap p T Q D) n x
  exact h.trans (Operated.law_event_eq_ambient (CF3CappedPathLaw.cappedKernel hp Q D)
    (CF3MarkedKernel.rate_positive hp) T cappedResetQ n (capProject Q D x))

theorem rawLaw_capHistory_lintegral {p : Par} (hp : p.Valid) (T : ℝ) (Q D n : ℕ)
    (x : SourceState p) (F : SourceBlockProtocol.History (CappedState p Q D) n → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ h, F (capHistory p Q D n h) ∂rawLaw hp T n x) =
      ∫⁻ h, F h ∂SourceBlockAmbient.ambientLaw (CF3CappedPathLaw.cappedKernel hp Q D)
        (CF3MarkedKernel.rate_positive hp) T cappedResetQ n (capProject Q D x) := by
  rw [← lintegral_map hF (measurable_capHistory p Q D n), rawLaw_capHistory hp T Q D n x]

/-- The raw start state is the actual supplied state; the zero hold is retained. -/
theorem segmentKernel_ae_start {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ s ∂segmentKernel hp x, s.2 0 = (0, x) := by
  have hs : MeasurableSet {s : Segment p | s.2 0 = (0, x)} :=
    measurableSet_eq_fun
      ((measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) 0).comp measurable_snd)
      measurable_const
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x), _
  apply (ae_map_iff (measurable_rawPair p x).aemeasurable hs).mpr
  exact ae_rawSequence_initial hp x none

theorem segmentKernel_ae_marked_start {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ s ∂segmentKernel hp x, s.1 0 = (0, (coreProject x, none)) := by
  have hs : MeasurableSet {s : Segment p | s.1 0 = (0, (coreProject x, none))} :=
    measurableSet_eq_fun
      ((measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) 0).comp measurable_fst)
      measurable_const
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x), _
  apply (ae_map_iff (measurable_rawPair p x).aemeasurable hs).mpr
  exact (CF3MarkedKernel.kernel hp).ae_event_initial (CF3MarkedKernel.rate_positive hp)
    (coreProject x, none)

/-- Every recorded raw path is the exact original complete-mark fold from its
initial raw state; no gross counters are inferred from projected state changes. -/
def faithful (p : Par) (s : Segment p) : Prop :=
  ∃ x : SourceState p, s.2 0 = (0, x) ∧ s.2 = rawSequence p x s.1

theorem measurableSet_faithful (p : Par) : MeasurableSet {s : Segment p | faithful p s} := by
  have hx (x : SourceState p) : MeasurableSet
      {s : Segment p | s.2 0 = (0, x) ∧ s.2 = rawSequence p x s.1} :=
    (measurableSet_eq_fun
      ((measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) 0).comp measurable_snd)
      measurable_const).inter
      (measurableSet_eq_fun measurable_snd ((measurable_rawSequence p x).comp measurable_fst))
  have hm : MeasurableSet (⋃ x : SourceState p,
      {s : Segment p | s.2 0 = (0, x) ∧ s.2 = rawSequence p x s.1}) :=
    MeasurableSet.iUnion hx
  have he : {s : Segment p | faithful p s} = ⋃ x : SourceState p,
      {s : Segment p | s.2 0 = (0, x) ∧ s.2 = rawSequence p x s.1} := by
    ext s
    simp [faithful]
  rw [he]
  exact hm

theorem segmentKernel_ae_faithful {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ s ∂segmentKernel hp x, faithful p s := by
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x), _
  apply (ae_map_iff (measurable_rawPair p x).aemeasurable (measurableSet_faithful p)).mpr
  filter_upwards [ae_rawSequence_initial hp x none] with w hw
  exact ⟨x, hw, rfl⟩

/-- Recursively records every start/reset boundary and the final returned state.
It includes all blocks regardless of their success or failure. -/
def compatible (p : Par) (T : ℝ) : (n : ℕ) → SourceState p → History p n → Prop
  | 0, x, h => h.2 = x
  | n + 1, x, h =>
      (h.1 0).2 0 = (0, x) ∧
        compatible p T n (nextState p T (h.1 0)) (Operated.tail h)

theorem measurableSet_compatible_joint (p : Par) (T : ℝ) (n : ℕ) :
    MeasurableSet {z : SourceState p × History p n | compatible p T n z.1 z.2} := by
  induction n with
  | zero => exact measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_fst
  | succ n ih =>
      have hs : Measurable (fun z : SourceState p × History p (n + 1) => z.2.1 0) := by
        simpa only [Function.comp_def] using
          (measurable_pi_apply (X := fun _ : Fin (n + 1) => Segment p) 0).comp
            (measurable_fst.comp measurable_snd)
      have hzero : Measurable (fun z : SourceState p × History p (n + 1) => (z.2.1 0).2 0) := by
        simpa only [Function.comp_def] using
          (measurable_pi_apply (X := fun _ : ℕ => ℝ × SourceState p) 0).comp
            (measurable_snd.comp hs)
      have hinit : Measurable (fun z : SourceState p × History p (n + 1) => ((0 : ℝ), z.1)) :=
        (measurable_const : Measurable (fun _ : SourceState p × History p (n + 1) => (0 : ℝ))).prodMk
          measurable_fst
      have hstart := measurableSet_eq_fun hzero hinit
      have htail : Measurable (fun z : SourceState p × History p (n + 1) =>
          (nextState p T (z.2.1 0), Operated.tail z.2)) := by
        simpa only [Function.comp_def] using
          ((measurable_nextState p T).comp hs).prodMk
            ((Operated.measurable_tail n).comp measurable_snd)
      exact hstart.inter (ih.preimage htail)

theorem measurableSet_compatible (p : Par) (T : ℝ) (n : ℕ) (x : SourceState p) :
    MeasurableSet {h : History p n | compatible p T n x h} := by
  have hm : Measurable (fun h : History p n => (x, h)) := measurable_const.prodMk measurable_id
  exact (measurableSet_compatible_joint p T n).preimage hm

/-- Actual reset-start and terminal compatibility under the one normalized
joint raw operated law, with no successful-history premise. -/
theorem rawLaw_ae_compatible {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T n x, compatible p T n x h := by
  induction n generalizing x with
  | zero => simp [rawLaw, Operated.law, compatible]
  | succ n ih =>
      let : IsMarkovKernel (Operated.tailKernel (nextState p T) (measurable_nextState p T)
          (rawLaw hp T n)) :=
        Operated.tailKernel_markov _ _ _ (fun y => inferInstance)
      change ∀ᵐ h ∂((segmentKernel hp x).compProd
        (Operated.tailKernel (nextState p T) (measurable_nextState p T) (rawLaw hp T n))).map
          (Operated.prepend n), compatible p T (n + 1) x h
      apply (ae_map_iff (Operated.measurable_prepend n).aemeasurable
        (measurableSet_compatible p T (n + 1) x)).mpr
      apply Measure.ae_compProd_of_ae_ae
        ((measurableSet_compatible p T (n + 1) x).preimage (Operated.measurable_prepend n))
      filter_upwards [segmentKernel_ae_start hp x] with s hs
      filter_upwards [ih (nextState p T s)] with h hh
      change s.2 0 = (0, x) ∧
        compatible p T n (nextState p T s) (Operated.tail (Operated.prepend n (s, h)))
      rw [Operated.tail_prepend]
      exact ⟨hs, hh⟩

theorem compatible_first (p : Par) (T : ℝ) (n : ℕ) (x : SourceState p)
    (h : History p (n + 1)) (hc : compatible p T (n + 1) x h) :
    (h.1 0).2 0 = (0, x) := hc.1

/-- The returned state is exactly the q-reset endpoint of the final executed
block. It is not a fresh resource state or an unexecuted infinite-tail state. -/
theorem compatible_final_last (p : Par) (T : ℝ) (n : ℕ) (x : SourceState p)
    (h : History p (n + 1)) (hc : compatible p T (n + 1) x h) :
    h.2 = nextState p T (h.1 (Fin.last n)) := by
  induction n generalizing x with
  | zero => exact hc.2
  | succ n ih =>
      exact ih (nextState p T (h.1 0)) (Operated.tail h) hc.2

theorem rawLaw_ae_first {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T (n + 1) x, (h.1 0).2 0 = (0, x) := by
  filter_upwards [rawLaw_ae_compatible hp T (n + 1) x] with h hh
  exact compatible_first p T n x h hh

theorem rawLaw_ae_final {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T (n + 1) x, h.2 = nextState p T (h.1 (Fin.last n)) := by
  filter_upwards [rawLaw_ae_compatible hp T (n + 1) x] with h hh
  exact compatible_final_last p T n x h hh

def allSegments {p : Par} {n : ℕ} (P : Segment p → Prop) (h : History p n) : Prop :=
  ∀ i : Fin n, P (h.1 i)

theorem measurableSet_allSegments {p : Par} (P : Segment p → Prop)
    (hP : MeasurableSet {s | P s}) (n : ℕ) :
    MeasurableSet {h : History p n | allSegments P h} := by
  have hm : MeasurableSet (⋂ i : Fin n, {h : History p n | P (h.1 i)}) := by
    apply MeasurableSet.iInter
    intro i
    have hi : Measurable (fun h : History p n => h.1 i) := by
      simpa only [Function.comp_def] using
        (measurable_pi_apply (X := fun _ : Fin n => Segment p) i).comp measurable_fst
    exact hP.preimage hi
  have he : {h : History p n | allSegments P h} = ⋂ i : Fin n, {h : History p n | P (h.1 i)} := by
    ext h
    simp [allSegments]
  rw [he]
  exact hm

theorem allSegments_prepend {p : Par} {n : ℕ} (P : Segment p → Prop)
    (s : Segment p) (h : History p n) :
    allSegments P (Operated.prepend n (s, h)) ↔ P s ∧ allSegments P h := by
  constructor
  · intro ha
    exact ⟨by simpa only [Operated.prepend, Fin.cons_zero] using ha 0,
      fun i => by simpa only [Operated.prepend, Fin.cons_succ] using ha i.succ⟩
  · rintro ⟨hs, hh⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Operated.prepend, Fin.cons_zero] using hs
    · simpa only [Operated.prepend, Fin.cons_succ] using hh j

/-- A measurable actual one-segment support theorem propagates through every
recorded segment of the actual joint controlled law. In particular this admits
the separate clock/boundary support theorem without redoing the recursion. -/
theorem rawLaw_ae_allSegments {p : Par} (hp : p.Valid) (T : ℝ)
    (P : Segment p → Prop) (hP : MeasurableSet {s | P s})
    (ha : ∀ x, ∀ᵐ s ∂segmentKernel hp x, P s) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T n x, allSegments P h := by
  induction n generalizing x with
  | zero => exact Filter.Eventually.of_forall (fun h i => Fin.elim0 i)
  | succ n ih =>
      let : IsMarkovKernel (Operated.tailKernel (nextState p T) (measurable_nextState p T)
          (rawLaw hp T n)) :=
        Operated.tailKernel_markov _ _ _ (fun y => inferInstance)
      change ∀ᵐ h ∂((segmentKernel hp x).compProd
        (Operated.tailKernel (nextState p T) (measurable_nextState p T) (rawLaw hp T n))).map
          (Operated.prepend n), allSegments P h
      apply (ae_map_iff (Operated.measurable_prepend n).aemeasurable
        (measurableSet_allSegments P hP (n + 1))).mpr
      apply Measure.ae_compProd_of_ae_ae
        ((measurableSet_allSegments P hP (n + 1)).preimage (Operated.measurable_prepend n))
      filter_upwards [ha x] with s hs
      filter_upwards [ih (nextState p T s)] with h hh
      exact (allSegments_prepend P s h).mpr ⟨hs, hh⟩

theorem rawLaw_ae_faithful {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T n x, allSegments (faithful p) h :=
  rawLaw_ae_allSegments hp T (faithful p) (measurableSet_faithful p)
    (segmentKernel_ae_faithful hp) n x

def fresh (p : Par) (s : Segment p) : Prop :=
  (s.1 0).1 = 0 ∧ (s.1 0).2.2 = none

theorem measurableSet_fresh (p : Par) : MeasurableSet {s : Segment p | fresh p s} := by
  have h0 : Measurable (fun s : Segment p => s.1 0) :=
    (measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) 0).comp measurable_fst
  have hm : Measurable (fun s : Segment p => (s.1 0).2.2) :=
    (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.2)).comp h0.snd
  exact (measurableSet_eq_fun h0.fst measurable_const).inter
    (measurableSet_eq_fun hm measurable_const)

theorem segmentKernel_ae_fresh {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ s ∂segmentKernel hp x, fresh p s := by
  filter_upwards [segmentKernel_ae_marked_start hp x] with s hs
  exact ⟨congrArg Prod.fst hs, congrArg (fun z : ℝ × CF3MarkedKernel.State p => z.2.2) hs⟩

theorem rawLaw_ae_fresh {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂rawLaw hp T n x, allSegments (fresh p) h :=
  rawLaw_ae_allSegments hp T (fresh p) (measurableSet_fresh p) (segmentKernel_ae_fresh hp) n x

theorem segmentKernel_ae_clocks {p : Par} (hp : p.Valid) (x : SourceState p)
    (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ s ∂segmentKernel hp x,
      NoBoundaryArrival.ClockBoundarySupport B s.1 ∧ NoBoundaryArrival.ClockBoundarySupport B s.2 := by
  have hm : MeasurableSet {s : Segment p |
      NoBoundaryArrival.ClockBoundarySupport B s.1 ∧ NoBoundaryArrival.ClockBoundarySupport B s.2} :=
    ((NoBoundaryArrival.measurableSet_clockBoundarySupport B hB).preimage measurable_fst).inter
      ((NoBoundaryArrival.measurableSet_clockBoundarySupport B hB).preimage measurable_snd)
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x), _
  apply (ae_map_iff (measurable_rawPair p x).aemeasurable hm).mpr
  filter_upwards [NoBoundaryArrival.cf3_marked_ae_clockBoundarySupport hp (coreProject x) none B hB,
    NoBoundaryArrival.cf3_rawSequence_ae_clockBoundarySupport hp x none B hB] with w hw hr
  exact ⟨hw, hr⟩

/-- Positive holds, unbounded clocks, and exclusion of every chosen countable
boundary hold simultaneously for both paths in every recorded actual segment. -/
theorem rawLaw_ae_clocks {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p)
    (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ h ∂rawLaw hp T n x, allSegments (fun s =>
      NoBoundaryArrival.ClockBoundarySupport B s.1 ∧ NoBoundaryArrival.ClockBoundarySupport B s.2) h := by
  have hm : MeasurableSet {s : Segment p |
      NoBoundaryArrival.ClockBoundarySupport B s.1 ∧ NoBoundaryArrival.ClockBoundarySupport B s.2} :=
    ((NoBoundaryArrival.measurableSet_clockBoundarySupport B hB).preimage measurable_fst).inter
      ((NoBoundaryArrival.measurableSet_clockBoundarySupport B hB).preimage measurable_snd)
  exact rawLaw_ae_allSegments hp T _ hm (fun y => segmentKernel_ae_clocks hp y B hB) n x

theorem nextState_counts (p : Par) (T : ℝ) (s : Segment p) (i : Fin p.M) :
    (nextState p T s i).a = ((timedState T s.2) i).a := rfl

theorem nextState_fuel (p : Par) (T : ℝ) (s : Segment p) (i : Fin p.M) :
    (nextState p T s i).R = ((timedState T s.2) i).R := rfl

theorem nextState_divisions (p : Par) (T : ℝ) (s : Segment p) (i : Fin p.M) :
    (nextState p T s i).nd = ((timedState T s.2) i).nd := rfl

theorem nextState_output (p : Par) (T : ℝ) (s : Segment p) (i : Fin p.M) (j : Fin p.c) :
    (nextState p T s i).q j = 0 := rfl

end
end CTMCHeredity20261019.V2.RawOperated
