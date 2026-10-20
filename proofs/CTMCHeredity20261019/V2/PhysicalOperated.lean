module

public import proofs.CTMCHeredity20261019.V2.RawOperated
public import proofs.CTMCHeredity20261019.V2.PhysicalSplice
public import proofs.CTMCHeredity20261019.V2.SentinelErasure

@[expose] public section

/-!
# Version 2: the continuous physical marked law behind raw operated blocks

Append an actual fresh terminal marked path to the normalized raw operated
history. Backward stitching retains only each segment's executed prefix.
The resulting entire marked-path law is the original fixed-kinetics law.
Core/reset compatibility is discharged under the actual segment law, never
asserted for arbitrary off-support marked/raw pairs. Fresh none sentinels are
ignored by the splice, using the independently proved sentinel map law.

Global raw reconstruction from these stitched marks has the original raw lift
law. Comparing its cumulative ledgers with locally reset segment ledgers is a
separate offset theorem. No common-clock seeded/seed-free equality is claimed.
-/

namespace CTMCHeredity20261019.V2.PhysicalOperated

open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CoreState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CoreState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def rightNoneKernel {p : Par} (hp : p.Valid) (T : ℝ) :
    ProbabilityTheory.Kernel (MarkedPath p) (MarkedPath p) where
  toFun w := CF3MarkedKernel.eventLaw hp (timedState T w).1 none
  measurable' := (measurable_of_countable
      (fun z : CF3MarkedKernel.State p => CF3MarkedKernel.eventLaw hp z.1 none)).comp
    (measurable_timedState T)

instance rightNoneKernel_markov {p : Par} (hp : p.Valid) (T : ℝ) :
    IsMarkovKernel (rightNoneKernel hp T) where
  isProbabilityMeasure w := by
    change IsProbabilityMeasure (CF3MarkedKernel.eventLaw hp (timedState T w).1 none)
    infer_instance

def spliceNoneValue {p : Par} (hp : p.Valid) (T : ℝ) (F : MarkedPath p → ℝ≥0∞)
    (w : MarkedPath p) : ℝ≥0∞ :=
  ∫⁻ v, F (PhysicalSplice.splice T (w, v)) ∂rightNoneKernel hp T w

theorem measurable_spliceNoneValue {p : Par} (hp : p.Valid) (T : ℝ)
    (F : MarkedPath p → ℝ≥0∞) (hF : Measurable F) : Measurable (spliceNoneValue hp T F) := by
  have hcomp : Measurable (fun z : MarkedPath p × MarkedPath p =>
      F (PhysicalSplice.splice T z)) := by
    simpa only [Function.comp_def] using hF.comp (PhysicalSplice.measurable_splice T)
  exact hcomp.lintegral_kernel_prod_right'

/-- A fresh none sentinel changes no positive right coordinate, and the splice
never executes that sentinel. This is derived from the actual sentinel law. -/
theorem splice_none_inner {p : Par} (hp : p.Valid) (T : ℝ) (w : MarkedPath p)
    (F : MarkedPath p → ℝ≥0∞) (hF : Measurable F) :
    spliceNoneValue hp T F w =
      ∫⁻ v, F (PhysicalSplice.splice T (w, v))
        ∂(CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (timedState T w) := by
  have hreward : Measurable (fun v : MarkedPath p => F (PhysicalSplice.splice T (w, v))) := by
    simpa only [Function.comp_def, id_eq] using
      hF.comp ((PhysicalSplice.measurable_splice T).comp (measurable_const.prodMk measurable_id))
  have hs := SentinelErasure.cf3_eventLaw_replaceSentinel hp (timedState T w).1
    (timedState T w).2 none
  calc
    _ = ∫⁻ v, F (PhysicalSplice.splice T (w, v))
        ∂(CF3MarkedKernel.eventLaw hp (timedState T w).1 (timedState T w).2).map
          (SentinelErasure.replaceSentinel none) :=
      congrArg (fun μ : Measure (MarkedPath p) =>
        ∫⁻ v, F (PhysicalSplice.splice T (w, v)) ∂μ) hs.symm
    _ = ∫⁻ v, F (PhysicalSplice.splice T (w, SentinelErasure.replaceSentinel none v))
        ∂CF3MarkedKernel.eventLaw hp (timedState T w).1 (timedState T w).2 :=
      lintegral_map hreward (SentinelErasure.measurable_replaceSentinel none)
    _ = _ := by
      apply lintegral_congr
      intro v
      apply congrArg F
      apply PhysicalSplice.prefixSplice_congr_positive
      intro k hk
      cases k with
      | zero => exact False.elim (Nat.lt_irrefl 0 hk)
      | succ k => rfl

theorem cf3_splice_none_reward {p : Par} (hp : p.Valid) (x : CoreState p)
    (old : Option (Mark p)) (T : ℝ) (hT : 0 ≤ T)
    (F : MarkedPath p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, spliceNoneValue hp T F w ∂CF3MarkedKernel.eventLaw hp x old) =
      ∫⁻ w, F w ∂CF3MarkedKernel.eventLaw hp x old := by
  have hcomp : Measurable (fun z : MarkedPath p × MarkedPath p =>
      F (PhysicalSplice.splice T z)) := by
    simpa only [Function.comp_def] using hF.comp (PhysicalSplice.measurable_splice T)
  calc
    _ = ∫⁻ w, ∫⁻ v, F (PhysicalSplice.splice T (w, v))
        ∂(CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (timedState T w) ∂CF3MarkedKernel.eventLaw hp x old :=
      lintegral_congr (fun w => splice_none_inner hp T w F hF)
    _ = ∫⁻ z, F (PhysicalSplice.splice T z)
        ∂((CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (x, old)).compProd
            (PhysicalSplice.continuationKernel (CF3MarkedKernel.kernel hp)
              (CF3MarkedKernel.rate_positive hp) T) :=
      (Measure.lintegral_compProd
        (μ := CF3MarkedKernel.eventLaw hp x old)
        (κ := PhysicalSplice.continuationKernel (CF3MarkedKernel.kernel hp)
          (CF3MarkedKernel.rate_positive hp) T) hcomp).symm
    _ = _ := PhysicalSplice.eventLaw_splice_lintegral (CF3MarkedKernel.kernel hp)
      (CF3MarkedKernel.rate_positive hp) (x, old) T hT F hF

/-- The source reset preserves the actual core at the physical endpoint, under
the actual segment law. Arbitrary marked/raw pairs need not satisfy this. -/
theorem segmentKernel_ae_nextCore {p : Par} (hp : p.Valid) (T : ℝ) (x : SourceState p) :
    ∀ᵐ s ∂RawOperated.segmentKernel hp x,
      coreProject (RawOperated.nextState p T s) = (timedState T s.1).1 := by
  have hl : Measurable (fun s : RawOperated.Segment p =>
      coreProject (RawOperated.nextState p T s)) :=
    (measurable_of_countable (coreProject (p := p))).comp (RawOperated.measurable_nextState p T)
  have hr : Measurable (fun s : RawOperated.Segment p => (timedState T s.1).1) :=
    (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.1)).comp
      ((measurable_timedState T).comp measurable_fst)
  have hm := measurableSet_eq_fun hl hr
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (RawOperated.rawPair p x), _
  apply (ae_map_iff (RawOperated.measurable_rawPair p x).aemeasurable hm).mpr
  filter_upwards [ae_rawSequence_timed_project hp x none] with w hw
  exact hw T

/-- Backward stitching uses only each recorded segment's executed marked
prefix and, after the last block, the appended actual fresh terminal tail. -/
def stitch (p : Par) (T : ℝ) : (n : ℕ) → RawOperated.History p n × MarkedPath p → MarkedPath p
  | 0, z => z.2
  | n + 1, z => PhysicalSplice.splice T
      ((z.1.1 0).1, stitch p T n (Operated.tail z.1, z.2))

theorem stitch_prepend (p : Par) (T : ℝ) (n : ℕ) (s : RawOperated.Segment p)
    (h : RawOperated.History p n) (v : MarkedPath p) :
    stitch p T (n + 1) (Operated.prepend n (s, h), v) =
      PhysicalSplice.splice T (s.1, stitch p T n (h, v)) := by
  change PhysicalSplice.splice T
    (s.1, stitch p T n (Operated.tail (Operated.prepend n (s, h)), v)) = _
  rw [Operated.tail_prepend]

theorem measurable_stitch (p : Par) (T : ℝ) (n : ℕ) : Measurable (stitch p T n) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
      have hs : Measurable (fun z : RawOperated.History p (n + 1) × MarkedPath p =>
          (z.1.1 0).1) := by
        simpa only [Function.comp_def] using
          ((measurable_pi_apply (X := fun _ : Fin (n + 1) => RawOperated.Segment p) 0).comp
            (measurable_fst.comp measurable_fst)).fst
      have ht : Measurable (fun z : RawOperated.History p (n + 1) × MarkedPath p =>
          (Operated.tail z.1, z.2)) :=
        ((Operated.measurable_tail n).comp measurable_fst).prodMk measurable_snd
      change Measurable (fun z : RawOperated.History p (n + 1) × MarkedPath p => PhysicalSplice.splice T
        ((z.1.1 0).1, stitch p T n (Operated.tail z.1, z.2)))
      exact (PhysicalSplice.measurable_splice T).comp (hs.prodMk (ih.comp ht))

def terminalKernel {p : Par} (hp : p.Valid) (n : ℕ) :
    ProbabilityTheory.Kernel (RawOperated.History p n) (MarkedPath p) where
  toFun h := CF3MarkedKernel.eventLaw hp (coreProject h.2) none
  measurable' := (measurable_of_countable
    (fun x : SourceState p => CF3MarkedKernel.eventLaw hp (coreProject x) none)).comp measurable_snd

instance terminalKernel_markov {p : Par} (hp : p.Valid) (n : ℕ) :
    IsMarkovKernel (terminalKernel hp n) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (CF3MarkedKernel.eventLaw hp (coreProject h.2) none)
    infer_instance

def completionValue {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (F : MarkedPath p → ℝ≥0∞) (h : RawOperated.History p n) : ℝ≥0∞ :=
  ∫⁻ v, F (stitch p T n (h, v)) ∂terminalKernel hp n h

theorem measurable_completionValue {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ)
    (F : MarkedPath p → ℝ≥0∞) (hF : Measurable F) : Measurable (completionValue hp T n F) := by
  have hm : Measurable (fun z : RawOperated.History p n × MarkedPath p => F (stitch p T n z)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_stitch p T n)
  exact hm.lintegral_kernel_prod_right'

/-- All source states, kernels, resets, and conditional laws in this induction
are actual constructions. Core agreement is used only on its actual AE set. -/
theorem rawLaw_stitch_value {p : Par} (hp : p.Valid) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (x : SourceState p) (F : MarkedPath p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, completionValue hp T n F h ∂RawOperated.rawLaw hp T n x) =
      ∫⁻ w, F w ∂CF3MarkedKernel.eventLaw hp (coreProject x) none := by
  induction n generalizing x F with
  | zero =>
      change (∫⁻ h, completionValue hp T 0 F h
        ∂Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)) = _
      exact lintegral_dirac' _ (measurable_completionValue hp T 0 F hF)
  | succ n ih =>
      have hreduce (s : RawOperated.Segment p) :
          (∫⁻ h, completionValue hp T (n + 1) F (Operated.prepend n (s, h))
            ∂RawOperated.rawLaw hp T n (RawOperated.nextState p T s)) =
            ∫⁻ v, F (PhysicalSplice.splice T (s.1, v))
              ∂CF3MarkedKernel.eventLaw hp (coreProject (RawOperated.nextState p T s)) none := by
        have hFs : Measurable (fun v : MarkedPath p => F (PhysicalSplice.splice T (s.1, v))) := by
          simpa only [Function.comp_def, id_eq] using
            hF.comp ((PhysicalSplice.measurable_splice T).comp
              (measurable_const.prodMk measurable_id))
        calc
          _ = ∫⁻ h, completionValue hp T n
              (fun v => F (PhysicalSplice.splice T (s.1, v))) h
              ∂RawOperated.rawLaw hp T n (RawOperated.nextState p T s) := by
            apply lintegral_congr
            intro h
            change (∫⁻ v, F (stitch p T (n + 1) (Operated.prepend n (s, h), v))
              ∂CF3MarkedKernel.eventLaw hp (coreProject h.2) none) = _
            apply lintegral_congr
            intro v
            exact congrArg F (stitch_prepend p T n s h v)
          _ = _ := ih (RawOperated.nextState p T s)
            (fun v => F (PhysicalSplice.splice T (s.1, v))) hFs
      calc
        _ = ∫⁻ s, ∫⁻ h, completionValue hp T (n + 1) F (Operated.prepend n (s, h))
            ∂RawOperated.rawLaw hp T n (RawOperated.nextState p T s)
            ∂RawOperated.segmentKernel hp x :=
          RawOperated.rawLaw_lintegral_step hp T n x (completionValue hp T (n + 1) F)
            (measurable_completionValue hp T (n + 1) F hF)
        _ = ∫⁻ s, ∫⁻ v, F (PhysicalSplice.splice T (s.1, v))
            ∂CF3MarkedKernel.eventLaw hp (coreProject (RawOperated.nextState p T s)) none
            ∂RawOperated.segmentKernel hp x := lintegral_congr hreduce
        _ = ∫⁻ s, spliceNoneValue hp T F s.1 ∂RawOperated.segmentKernel hp x := by
          apply lintegral_congr_ae
          filter_upwards [segmentKernel_ae_nextCore hp T x] with s hs
          change (∫⁻ v, F (PhysicalSplice.splice T (s.1, v))
            ∂CF3MarkedKernel.eventLaw hp (coreProject (RawOperated.nextState p T s)) none) =
            ∫⁻ v, F (PhysicalSplice.splice T (s.1, v))
              ∂CF3MarkedKernel.eventLaw hp (timedState T s.1).1 none
          rw [hs]
        _ = ∫⁻ w, spliceNoneValue hp T F w ∂CF3MarkedKernel.eventLaw hp (coreProject x) none := by
          have hm : Measurable (fun s : RawOperated.Segment p => spliceNoneValue hp T F s.1) := by
            simpa only [Function.comp_def] using (measurable_spliceNoneValue hp T F hF).comp
              (measurable_fst : Measurable (fun s : RawOperated.Segment p => s.1))
          exact lintegral_map hm (RawOperated.measurable_rawPair p x)
        _ = _ := cf3_splice_none_reward hp (coreProject x) none T hT F hF

def completedLaw {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    Measure (RawOperated.History p n × MarkedPath p) :=
  (RawOperated.rawLaw hp T n x).compProd (terminalKernel hp n)

instance completedLaw_probability {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    IsProbabilityMeasure (completedLaw hp T n x) := by unfold completedLaw; infer_instance

/-- The entire stitched physical marked path, not a scalar marginal, has the
original actual fixed-parameter CF3 law. Segment tails are discarded. -/
theorem completedLaw_stitch {p : Par} (hp : p.Valid) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (x : SourceState p) :
    (completedLaw hp T n x).map (stitch p T n) =
      CF3MarkedKernel.eventLaw hp (coreProject x) none := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_stitch p T n)]
  have hm : Measurable (fun z : RawOperated.History p n × MarkedPath p => F (stitch p T n z)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_stitch p T n)
  calc
    _ = ∫⁻ h, completionValue hp T n F h ∂RawOperated.rawLaw hp T n x :=
      Measure.lintegral_compProd
        (μ := RawOperated.rawLaw hp T n x) (κ := terminalKernel hp n) hm
    _ = _ := rawLaw_stitch_value hp T hT n x F hF

/-- Global reconstruction from stitched complete marks is the original raw
lift. Local q/nd reset offsets are not silently identified with global ledgers. -/
theorem completedLaw_stitch_rawSequence {p : Par} (hp : p.Valid) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (x : SourceState p) :
    (completedLaw hp T n x).map (fun z => rawSequence p x (stitch p T n z)) =
      rawLiftLaw hp x none := by
  have h := congrArg (fun μ : Measure (MarkedPath p) => μ.map (rawSequence p x))
    (completedLaw_stitch hp T hT n x)
  rw [Measure.map_map (measurable_rawSequence p x) (measurable_stitch p T n)] at h
  exact h

end
end CTMCHeredity20261019.V2.PhysicalOperated
