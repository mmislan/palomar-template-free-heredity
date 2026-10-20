module

public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import proofs.CTMCHeredity20261019.EventIndexStoppedLaw
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-!
# V2: whole raw-ledger futures at observable event-index slices

The raw source state is the exact finite fold of the complete sampled proposal
marks, including state-null operations. The deterministic cocycle and the
already proved whole marked suffix law identify its conditional future with
`rawLiftLaw` started at the reconstructed raw prefix state and actual last-mark
sentinel. Complete marked prefixes are retained jointly with the entire raw
future. No raw Markov-law premise, eventual-hit premise, reset, stock estimate,
or seed-switch certificate is introduced.
-/

namespace CTMCHeredity20261019.V2.RawStoppedFuture

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical

abbrev RawPath (p : Par) := ℕ → ℝ × SourceState p
abbrev Prefix (p : Par) (n : ℕ) := EventPrefix (CF3MarkedKernel.State p) n
abbrev MarkVector (p : Par) (n : ℕ) := Fin n → Option (Mark p)

/-- The exact source update fold restarts at its actual raw prefix state.
No sampled coherence or stochastic premise is needed for this cocycle. -/
theorem rawAt_normalized_suffix (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n k : ℕ) :
    rawAt p (rawAt p x w n) (normalizedEventSuffix n w) k = rawAt p x w (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change sourceProposalNext p
        (rawAt p (rawAt p x w n) (normalizedEventSuffix n w) k) (w (n + k + 1)).2.2 =
          sourceProposalNext p (rawAt p x w (n + k)) (w (n + k + 1)).2.2
      rw [ih]

/-- Every later hold is copied verbatim; only the incoming coordinate-zero
hold is replaced by zero. All original natural-valued ledgers are preserved. -/
theorem rawSequence_normalized_suffix (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) :
    rawSequence p (rawAt p x w n) (normalizedEventSuffix n w) =
      normalizedEventSuffix n (rawSequence p x w) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      change ((w (n + k + 1)).1,
        rawAt p (rawAt p x w n) (normalizedEventSuffix n w) (k + 1)) =
          ((w (n + k + 1)).1, rawAt p x w (n + k + 1))
      rw [rawAt_normalized_suffix, Nat.add_assoc]

/- The same discrete sigma algebras as the sealed actual marked/raw laws. -/
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

/-- The finite mark vector contained in the complete observed prefix. -/
def prefixMarks (p : Par) (n : ℕ) (u : Prefix p n) : MarkVector p n :=
  fun i => (u ⟨i.val + 1, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩).2.2

/-- Actual unbounded source state, reconstructed from the observed prefix. -/
def prefixRaw (p : Par) (x : SourceState p) (n : ℕ) (u : Prefix p n) : SourceState p :=
  rawPrefixAt p x n (prefixMarks p n u)

theorem prefixRaw_frestrict (p : Par) (x : SourceState p) (n : ℕ) (w : MarkedPath p) :
    prefixRaw p x n (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
      rawAt p x w n := by
  exact (rawAt_eq_prefix p x w n).symm

theorem measurable_prefixMarks (p : Par) (n : ℕ) : Measurable (prefixMarks p n) := by
  apply measurable_pi_iff.mpr
  intro i
  have hm : Measurable (fun z : ℝ × CF3MarkedKernel.State p => z.2.2) :=
    (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.2)).comp measurable_snd
  exact hm.comp (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p)
    ⟨i.val + 1, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩)

theorem measurable_prefixRaw (p : Par) (x : SourceState p) (n : ℕ) :
    Measurable (prefixRaw p x n) :=
  (measurable_of_countable (rawPrefixAt p x n)).comp (measurable_prefixMarks p n)

def lastMarked (p : Par) (n : ℕ) (u : Prefix p n) : CF3MarkedKernel.State p :=
  (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2

theorem measurable_lastMarked (p : Par) (n : ℕ) : Measurable (lastMarked p n) :=
  (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p)
    ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd

/-- Reconstruct a fresh raw sequence with the raw state encoded by the prefix. -/
def prefixRawSequence (p : Par) (x : SourceState p) (n : ℕ)
    (z : Prefix p n × MarkedPath p) : RawPath p :=
  rawSequence p (prefixRaw p x n z.1) z.2

theorem measurable_prefixRawSequence (p : Par) (x : SourceState p) (n : ℕ) :
    Measurable (prefixRawSequence p x n) := by
  have hm : Measurable (fun z : MarkVector p n × MarkedPath p =>
      rawSequence p (rawPrefixAt p x n z.1) z.2) :=
    measurable_from_prod_countable_right (fun m => measurable_rawSequence p (rawPrefixAt p x n m))
  exact hm.comp (((measurable_prefixMarks p n).comp measurable_fst).prodMk measurable_snd)

def markedPrefixLaw {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (n : ℕ) : Measure (Prefix p n) :=
  (CF3MarkedKernel.eventLaw hp (coreProject x) old).map
    (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)

instance markedPrefixLaw_probability {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) : IsProbabilityMeasure (markedPrefixLaw hp x old n) := by
  unfold markedPrefixLaw
  infer_instance

/-- Actual raw-prefix/core coherence is supplied by the sampled marked law. -/
theorem ae_prefixRaw_project {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) :
    ∀ᵐ u ∂markedPrefixLaw hp x old n,
      coreProject (prefixRaw p x n u) = (lastMarked p n u).1 := by
  have hl : Measurable (fun u : Prefix p n => coreProject (prefixRaw p x n u)) :=
    (measurable_of_countable (fun m : MarkVector p n => coreProject (rawPrefixAt p x n m))).comp
      (measurable_prefixMarks p n)
  have hr : Measurable (fun u : Prefix p n => (lastMarked p n u).1) :=
    (measurable_of_countable (fun y : CF3MarkedKernel.State p => y.1)).comp (measurable_lastMarked p n)
  unfold markedPrefixLaw
  apply (ae_map_iff (measurable_frestrictLe n).aemeasurable (measurableSet_eq_fun hl hr)).mpr
  filter_upwards [ae_rawAt_project hp x old] with w hw
  rw [prefixRaw_frestrict]
  exact hw n

/-- The raw future is an actual fresh lift from the full reconstructed state;
the last sampled mark is preserved as its coordinate-zero sentinel. -/
def rawFreshKernel {p : Par} (hp : p.Valid) (x : SourceState p) (n : ℕ) :
    ProbabilityTheory.Kernel (Prefix p n) (RawPath p) where
  toFun u := rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2
  measurable' := by
    have hc : Measurable (fun u : Prefix p n =>
        (prefixMarks p n u, (lastMarked p n u).2)) :=
      (measurable_prefixMarks p n).prodMk
        ((measurable_of_countable (fun y : CF3MarkedKernel.State p => y.2)).comp
          (measurable_lastMarked p n))
    exact (measurable_of_countable (fun c : MarkVector p n × Option (Mark p) =>
      rawLiftLaw hp (rawPrefixAt p x n c.1) c.2)).comp hc

instance rawFreshKernel_markov {p : Par} (hp : p.Valid) (x : SourceState p) (n : ℕ) :
    IsMarkovKernel (rawFreshKernel hp x n) where
  isProbabilityMeasure u := by
    change IsProbabilityMeasure (rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2)
    infer_instance

def markedJointSource {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (n : ℕ) (A : Set (Prefix p n)) : Measure (Prefix p n × MarkedPath p) :=
  ((CF3MarkedKernel.eventLaw hp (coreProject x) old).restrict
    (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n ⁻¹' A)).map
      (fun w => (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        normalizedEventSuffix n w))

def markedJointMixture {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (n : ℕ) (A : Set (Prefix p n)) : Measure (Prefix p n × MarkedPath p) :=
  ((markedPrefixLaw hp x old n).restrict A).compProd
    (prefixFreshEventKernel (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp) n)

/-- The whole marked suffix law retains the complete prefix jointly. This is
rectangle uniqueness applied to the sealed event-index theorem. -/
theorem marked_joint_law {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (A : Set (Prefix p n)) (hA : MeasurableSet A) :
    markedJointSource hp x old n A = markedJointMixture hp x old n A := by
  let μ := markedJointSource hp x old n A
  let : IsFiniteMeasure μ := by unfold μ markedJointSource; infer_instance
  apply Measure.ext_prod
  intro B C hB hC
  have hs : markedJointSource hp x old n A (B ×ˢ C) =
      eventIndexPrefixSource (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
        (coreProject x, old) n (B ∩ A) C := by
    have hm := (measurable_frestrictLe (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n).prodMk
      (measurable_normalizedEventSuffix n)
    unfold markedJointSource eventIndexPrefixSource CF3MarkedKernel.eventLaw
    rw [Measure.map_apply hm (hB.prod hC),
      Measure.map_apply (measurable_normalizedEventSuffix n) hC,
      Measure.restrict_apply ((hB.prod hC).preimage hm),
      Measure.restrict_apply (hC.preimage (measurable_normalizedEventSuffix n))]
    congr 1
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto
  have hm : markedJointMixture hp x old n A (B ×ˢ C) =
      eventIndexPrefixMixture (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
        (coreProject x, old) n (B ∩ A) C := by
    unfold markedJointMixture markedPrefixLaw eventIndexPrefixMixture CF3MarkedKernel.eventLaw
    rw [Measure.compProd_apply_prod hB hC,
      Measure.bind_apply hC
        (prefixFreshEventKernel (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp) n).aemeasurable,
      Measure.restrict_restrict hB]
  exact hs.trans ((congrArg (fun ν : Measure (MarkedPath p) => ν C)
    (eventIndex_prefix_event_law (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
      (coreProject x, old) n (B ∩ A) (hB.inter hA))).trans hm.symm)

def rawJointMap (p : Par) (x : SourceState p) (n : ℕ)
    (z : Prefix p n × MarkedPath p) : Prefix p n × RawPath p :=
  (z.1, prefixRawSequence p x n z)

theorem measurable_rawJointMap (p : Par) (x : SourceState p) (n : ℕ) :
    Measurable (rawJointMap p x n) :=
  measurable_fst.prodMk (measurable_prefixRawSequence p x n)

theorem measurable_rawJointSource_map (p : Par) (x : SourceState p) (n : ℕ) :
    Measurable (fun w : MarkedPath p =>
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        normalizedEventSuffix n (rawSequence p x w))) := by
  have hm := (measurable_frestrictLe (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n).prodMk
    ((measurable_normalizedEventSuffix n).comp (measurable_rawSequence p x))
  have he : (fun w : MarkedPath p =>
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        (normalizedEventSuffix n ∘ rawSequence p x) w)) =
      (fun w : MarkedPath p =>
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
          normalizedEventSuffix n (rawSequence p x w))) := by
    funext w
    rfl
  rw [← he]
  exact hm

/-- Actual complete marked prefix jointly with the normalized raw future. -/
def rawJointSource {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (n : ℕ) (A : Set (Prefix p n)) : Measure (Prefix p n × RawPath p) :=
  ((CF3MarkedKernel.eventLaw hp (coreProject x) old).restrict
    (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n ⁻¹' A)).map
      (fun w => (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        normalizedEventSuffix n (rawSequence p x w)))

def rawJointMixture {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (n : ℕ) (A : Set (Prefix p n)) : Measure (Prefix p n × RawPath p) :=
  ((markedPrefixLaw hp x old n).restrict A).compProd (rawFreshKernel hp x n)

theorem rawJointSource_eq_map {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (A : Set (Prefix p n)) :
    rawJointSource hp x old n A =
      (markedJointSource hp x old n A).map (rawJointMap p x n) := by
  unfold rawJointSource markedJointSource
  rw [Measure.map_map (measurable_rawJointMap p x n)
    ((measurable_frestrictLe (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n).prodMk
      (measurable_normalizedEventSuffix n))]
  congr 1
  funext w
  dsimp only [Function.comp_def, rawJointMap, prefixRawSequence]
  have hsecond : normalizedEventSuffix n (rawSequence p x w) =
      rawSequence p (prefixRaw p x n (frestrictLe n w)) (normalizedEventSuffix n w) := by
    rw [prefixRaw_frestrict]
    exact (rawSequence_normalized_suffix p x w n).symm
  exact congrArg (fun v : RawPath p =>
    (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, v)) hsecond

/-- Actual raw whole-suffix law conditional on every measurable complete
marked prefix event. Core coherence is discharged from the actual sampled law. -/
theorem raw_joint_law {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (A : Set (Prefix p n)) (hA : MeasurableSet A) :
    rawJointSource hp x old n A = rawJointMixture hp x old n A := by
  rw [rawJointSource_eq_map, marked_joint_law hp x old n A hA]
  apply Measure.ext_of_lintegral
  intro F hF
  unfold markedJointMixture rawJointMixture
  have he : F ∘ rawJointMap p x n =
      (fun z : Prefix p n × MarkedPath p => F (rawJointMap p x n z)) := by
    funext z
    rfl
  have hFm : Measurable (fun z : Prefix p n × MarkedPath p => F (rawJointMap p x n z)) := by
    rw [← he]
    exact hF.comp (measurable_rawJointMap p x n)
  rw [lintegral_map hF (measurable_rawJointMap p x n),
    Measure.lintegral_compProd hFm,
    Measure.lintegral_compProd hF]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_prefixRaw_project hp x old n)] with u hu
  change (∫⁻ v, F (u, rawSequence p (prefixRaw p x n u) v)
      ∂(CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
        (lastMarked p n u)) =
    ∫⁻ r, F (u, r) ∂rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2
  have hFu : Measurable (fun r : RawPath p => F (u, r)) := by
    have he' : F ∘ Prod.mk u = (fun r : RawPath p => F (u, r)) := by
      funext r
      rfl
    rw [← he']
    exact hF.comp measurable_prodMk_left
  rw [rawLiftLaw, lintegral_map hFu
    (measurable_rawSequence p (prefixRaw p x n u))]
  have hz : (coreProject (prefixRaw p x n u), (lastMarked p n u).2) = lastMarked p n u :=
    Prod.ext hu rfl
  change (∫⁻ v, F (u, rawSequence p (prefixRaw p x n u) v)
      ∂(CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
        (lastMarked p n u)) =
    ∫⁻ v, F (u, rawSequence p (prefixRaw p x n u) v)
      ∂(CF3MarkedKernel.kernel hp).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
        (coreProject (prefixRaw p x n u), (lastMarked p n u).2)
  rw [hz]

/-- Arbitrary jointly measurable nonnegative raw-future reward, with the
entire marked past retained, on a deterministic observable index slice. -/
theorem raw_prefix_slice_reward {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (A : Set (Prefix p n)) (hA : MeasurableSet A)
    (F : Prefix p n × RawPath p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ A then
        F (frestrictLe n w, normalizedEventSuffix n (rawSequence p x w)) else 0
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∫⁻ u in A, ∫⁻ r, F (u, r) ∂rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2
        ∂markedPrefixLaw hp x old n := by
  have hm := measurable_rawJointSource_map p x n
  calc
    _ = ∫⁻ z, F z ∂rawJointSource hp x old n A := by
      unfold rawJointSource
      rw [lintegral_map hF hm, ← lintegral_indicator (hA.preimage (measurable_frestrictLe n))]
      apply lintegral_congr
      intro w
      by_cases hw : frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ A <;>
        simp [Set.indicator, hw]
    _ = ∫⁻ z, F z ∂rawJointMixture hp x old n A := by rw [raw_joint_law hp x old n A hA]
    _ = _ := by
      unfold rawJointMixture
      rw [Measure.lintegral_compProd hF]
      rfl

/-! The indexed reward family below keeps the complete marked prefix on every
possible stop slice. No coverage of the source probability space is required.
Disjointness is needed only to interpret the slice sum as a subprobability
stopped law, and is not used for the nonnegative Tonelli identities. -/

/-- Whole raw future submeasure from all proposed finite stopping slices. -/
def rawStoppedSource {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (A : ∀ n : ℕ, Set (Prefix p n)) : Measure (RawPath p) :=
  Measure.sum (fun n => (rawJointSource hp x old n (A n)).snd)

/-- Actual fresh raw lifts from every observed stopping prefix, with original
prefix probabilities and no normalization by an assumed hitting probability. -/
def rawStoppedMixture {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (A : ∀ n : ℕ, Set (Prefix p n)) : Measure (RawPath p) :=
  Measure.sum (fun n => ((markedPrefixLaw hp x old n).restrict (A n)).bind (rawFreshKernel hp x n))

/-- The whole raw future law at a partial observable event-index stop is a
mixture of the constructed raw lifts. No raw Markov property is assumed. -/
theorem raw_stopped_law {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (A : ∀ n : ℕ, Set (Prefix p n)) (hA : ∀ n, MeasurableSet (A n)) :
    rawStoppedSource hp x old A = rawStoppedMixture hp x old A := by
  apply congrArg (fun M : ℕ → Measure (RawPath p) => Measure.sum M)
  funext n
  rw [raw_joint_law hp x old n (A n) (hA n)]
  exact Measure.snd_compProd _ _

/-- A complete marked-past/raw-future reward may depend on the selected index
and on every prefix coordinate. Nonnegative sums remain exact even if slices
overlap; disjoint families are the stopping-time specialization. -/
theorem raw_stop_family_joint_reward {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (A : ∀ n : ℕ, Set (Prefix p n))
    (hA : ∀ n, MeasurableSet (A n))
    (F : ∀ n : ℕ, Prefix p n × RawPath p → ℝ≥0∞) (hF : ∀ n, Measurable (F n)) :
    (∫⁻ w, ∑' n : ℕ,
      if frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ A n then
        F n (frestrictLe n w, normalizedEventSuffix n (rawSequence p x w)) else 0
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∑' n : ℕ, ∫⁻ u in A n, ∫⁻ r, F n (u, r)
        ∂rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2
        ∂markedPrefixLaw hp x old n := by
  have hm (n : ℕ) : Measurable (fun w : MarkedPath p =>
      if frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ A n then
        F n (frestrictLe n w, normalizedEventSuffix n (rawSequence p x w)) else 0) :=
    Measurable.ite ((hA n).preimage (measurable_frestrictLe n))
      ((hF n).comp ((measurable_frestrictLe n).prodMk
        ((measurable_normalizedEventSuffix n).comp (measurable_rawSequence p x)))) measurable_const
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  apply tsum_congr
  intro n
  exact raw_prefix_slice_reward hp x old n (A n) (hA n) (F n) (hF n)

/-- Disjoint observable stopping slices retain their exact hit probability.
Raw q/nd may be unbounded and a positive nonhitting probability is permitted. -/
theorem raw_stopped_mass {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p))
    (A : ∀ n : ℕ, Set (Prefix p n)) (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    rawStoppedSource hp x old A Set.univ =
      CF3MarkedKernel.eventLaw hp (coreProject x) old (eventIndexHitEvent A) := by
  unfold rawStoppedSource
  rw [Measure.sum_apply _ MeasurableSet.univ]
  calc
    _ = ∑' n : ℕ, CF3MarkedKernel.eventLaw hp (coreProject x) old (eventIndexStopSlice A n) := by
      apply tsum_congr
      intro n
      rw [Measure.snd_univ]
      unfold rawJointSource
      rw [Measure.map_apply
        (measurable_rawJointSource_map p x n)
        MeasurableSet.univ]
      simp only [Set.preimage_univ, Measure.restrict_apply_univ, eventIndexStopSlice]
    _ = _ := (measure_iUnion hDisj (measurableSet_eventIndexStopSlice A hA)).symm

theorem raw_stopped_subprobability {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (A : ∀ n : ℕ, Set (Prefix p n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    rawStoppedSource hp x old A Set.univ ≤ 1 := by
  rw [raw_stopped_mass hp x old A hA hDisj]
  exact (measure_mono (subset_univ (eventIndexHitEvent A))).trans_eq measure_univ

/-- The missing mass of the partial stopped law is exactly nonhitting, not
silently assigned to a successful finite Ready or division index. -/
theorem raw_stopped_nonhit_mass {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (A : ∀ n : ℕ, Set (Prefix p n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    rawStoppedSource hp x old A Set.univ +
      CF3MarkedKernel.eventLaw hp (coreProject x) old (eventIndexHitEvent A)ᶜ = 1 := by
  rw [raw_stopped_mass hp x old A hA hDisj]
  exact (measure_add_measure_compl (measurableSet_eventIndexHitEvent A hA)).trans measure_univ

end
end CTMCHeredity20261019.V2.RawStoppedFuture
