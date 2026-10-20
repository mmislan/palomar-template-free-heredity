module

public import proofs.CTMCHeredity20261019.EventIndexLaw

@[expose] public section

/-!
# Partial event-index stopping laws from observable prefix slices

Each possible stopping index n is specified by a measurable event A_n of the
complete source prefix through n. No coverage or eventual-hit premise is made.
The sum of the actual slice laws equals the sum of actual fresh event-law
mixtures. If the pulled-back slices are disjoint, this is a subprobability
stopped law whose mass is exactly the probability of hitting some slice.
Positive nonhitting mass is retained explicitly.

Without disjointness, the reward identities remain valid and count slices with
multiplicity; they do not assert that the family selects a unique stopping
index. Arbitrary continuous-time stopping times are outside this interface.
-/

namespace CTMCHeredity20261019

noncomputable section
open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The event that the observed prefix belongs to the proposed n-th stopping
slice. The predicate can inspect all preceding holding times and states. -/
def eventIndexStopSlice (A : ∀ n : ℕ, Set (EventPrefix S n)) (n : ℕ) :
    Set (ℕ → ℝ × S) := frestrictLe (π := fun _ : ℕ => ℝ × S) n ⁻¹' A n

/-- The finite-stop event. Its complement is retained as nonhitting mass. -/
def eventIndexHitEvent (A : ∀ n : ℕ, Set (EventPrefix S n)) : Set (ℕ → ℝ × S) :=
  ⋃ n : ℕ, eventIndexStopSlice A n

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurableSet_eventIndexStopSlice (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) : MeasurableSet (eventIndexStopSlice A n) :=
  (hA n).preimage (measurable_frestrictLe n)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurableSet_eventIndexHitEvent (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n)) : MeasurableSet (eventIndexHitEvent A) :=
  MeasurableSet.iUnion (measurableSet_eventIndexStopSlice A hA)

/-- Sum of the actual source slice laws. Disjoint slices give a partial
stopped law; uncovered paths contribute no mass. -/
def eventIndexSliceFamilySource (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  Measure.sum (fun n => eventIndexPrefixSource K hLam x n (A n))

/-- The corresponding sum of original prefix marginals restricted to A_n,
followed by the actual fresh event law from their last state. -/
def eventIndexSliceFamilyMixture (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  Measure.sum (fun n => eventIndexPrefixMixture K hLam x n (A n))

/-- Whole infinite future-law identity for an arbitrary measurable prefix
slice family, with no eventual-hit or coverage assumption. -/
theorem eventIndex_stop_family_law (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n)) :
    eventIndexSliceFamilySource K hLam x A = eventIndexSliceFamilyMixture K hLam x A := by
  exact congrArg (fun M : ℕ → Measure (ℕ → ℝ × S) => Measure.sum M)
    (funext (fun n => eventIndex_prefix_event_law K hLam x n (A n) (hA n)))

/-- Tonelli connects the slice-sum source measure to the actual source paths.
No disjointness or finiteness premise is needed for nonnegative rewards. -/
theorem eventIndexSliceFamilySource_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂eventIndexSliceFamilySource K hLam x A) =
      ∫⁻ w, ∑' n : ℕ, if w ∈ eventIndexStopSlice A n then
        F (normalizedEventSuffix n w) else 0 ∂K.eventLaw Lam hLam x := by
  unfold eventIndexSliceFamilySource
  rw [lintegral_sum_measure]
  calc
    _ = ∑' n : ℕ, ∫⁻ w, if w ∈ eventIndexStopSlice A n then
        F (normalizedEventSuffix n w) else 0 ∂K.eventLaw Lam hLam x := by
      apply tsum_congr
      intro n
      exact eventIndexPrefixSource_lintegral K hLam x n (A n) (hA n) F hF
    _ = _ := (lintegral_tsum (fun n =>
      (Measurable.ite (measurableSet_eventIndexStopSlice A hA n)
        (hF.comp (measurable_normalizedEventSuffix n)) measurable_const).aemeasurable)).symm

/-- The exact partial-stopping reward is the sum of actual fresh event-law
expectations over the measurable stopping prefixes. -/
theorem eventLaw_eventIndex_stop_family_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, ∑' n : ℕ, if w ∈ eventIndexStopSlice A n then
        F (normalizedEventSuffix n w) else 0 ∂K.eventLaw Lam hLam x) =
      ∑' n : ℕ, ∫⁻ u, if u ∈ A n then
        (∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  rw [← eventIndexSliceFamilySource_lintegral K hLam x A hA F hF,
    eventIndex_stop_family_law K hLam x A hA]
  unfold eventIndexSliceFamilyMixture
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  exact eventIndexPrefixMixture_lintegral K hLam x n (A n) (hA n) F hF

/-- Disjoint observable slices produce exactly the probability of a finite
hit, rather than silently assuming that some slice is reached. -/
theorem eventIndex_stopped_law_mass (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    eventIndexSliceFamilySource K hLam x A Set.univ =
      K.eventLaw Lam hLam x (eventIndexHitEvent A) := by
  unfold eventIndexSliceFamilySource
  rw [Measure.sum_apply _ MeasurableSet.univ]
  calc
    _ = ∑' n : ℕ, K.eventLaw Lam hLam x (eventIndexStopSlice A n) := by
      apply tsum_congr
      intro n
      unfold eventIndexPrefixSource
      rw [Measure.map_apply (measurable_normalizedEventSuffix n) MeasurableSet.univ]
      simp [eventIndexStopSlice]
    _ = _ := (measure_iUnion hDisj (measurableSet_eventIndexStopSlice A hA)).symm

/-- The partial stopped law has total mass at most one; nonhitting is allowed. -/
theorem eventIndex_stopped_law_subprobability (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    eventIndexSliceFamilySource K hLam x A Set.univ ≤ 1 := by
  rw [eventIndex_stopped_law_mass K hLam x A hA hDisj]
  exact (measure_mono (subset_univ (eventIndexHitEvent A))).trans_eq (measure_univ)

/-- Positive nonhitting mass is explicitly the missing mass of the stopped
future law. No almost-sure finiteness assumption occurs. -/
theorem eventIndex_stopped_nonhit_mass (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m))) :
    eventIndexSliceFamilySource K hLam x A Set.univ +
      K.eventLaw Lam hLam x (eventIndexHitEvent A)ᶜ = 1 := by
  rw [eventIndex_stopped_law_mass K hLam x A hA hDisj]
  exact (measure_add_measure_compl (measurableSet_eventIndexHitEvent A hA)).trans (measure_univ)

end
end CTMCHeredity20261019
