module

public import proofs.CTMCHeredity20261019.PhysicalCutLaw

@[expose] public section

/-!
# Whole normalized suffix law at a deterministic source event index

The finite-cylinder identities of `EventIndexSuffix` determine the entire
infinite sequence law. Coordinate zero discards the incoming hold and installs
`(0,last state)`, exactly as in a fresh actual event law. All measurable prefix
events are retained. No Markov-law premise is introduced.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical
noncomputable section

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem fullCylinderWeight_succ (k : ℕ) (b : ℕ → ℝ × S → ℝ≥0∞)
    (v : ℕ → ℝ × S) :
    fullCylinderWeight (k + 1) b v =
      b 0 (v 0) * futureCylinderWeight 0 k (fun i => b (i + 1)) v := by
  unfold fullCylinderWeight
  rw [show k + 1 = 1 + k by omega, Finset.prod_range_add]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold futureCylinderWeight
  apply congrArg (fun r => b 0 (v 0) * r)
  apply Finset.prod_congr rfl
  intro i _
  have h1 : 1 + i = i + 1 := by omega
  have h2 : 0 + i + 1 = i + 1 := by omega
  rw [h1, h2]

/-- The finite-cylinder law including coordinate zero and an arbitrary
measurable event of the complete prefix through the cut index. -/
theorem eventIndex_fullCylinder_prefix (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ)
    (A : Set (EventPrefix S n)) (hA : MeasurableSet A)
    (b : ℕ → ℝ × S → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) :
    (∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then
        fullCylinderWeight (k + 1) b (normalizedEventSuffix n w) else 0
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if u ∈ A then
        (∫⁻ v, fullCylinderWeight (k + 1) b v
          ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let B : EventPrefix S n → ℝ≥0∞ := fun u =>
    if u ∈ A then b 0 (0, (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
  have hB : Measurable B := Measurable.ite hA
    ((hb 0).comp (measurable_const.prodMk
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
        ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd)) measurable_const
  have h := eventLaw_futureCylinder_disintegrate K hLam x n k B hB
    (fun i => b (i + 1)) (fun i => hb (i + 1)) (fun _ => 1)
  simp only [mul_one] at h
  calc
    _ = ∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderWeight n k (fun i => b (i + 1)) w ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      by_cases ha : frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A
      · simp only [ha, ite_true, B]
        rw [fullCylinderWeight_succ, futureCylinderWeight_normalizedSuffix]
        rfl
      · simp [ha, B]
    _ = _ := h
    _ = _ := by
      apply lintegral_congr
      intro u
      by_cases ha : u ∈ A
      · simp only [ha, ite_true, B]
        rw [← lintegral_const_mul _
          (measurable_futureCylinderWeight 0 k (fun i => b (i + 1)) (fun i => hb (i + 1)))]
        apply lintegral_congr_ae
        filter_upwards [K.ae_event_initial hLam
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2] with v hv
        rw [fullCylinderWeight_succ, hv]
      · simp [ha, B]

/-- Actual normalized suffix law, retaining a fixed measurable prefix event. -/
def eventIndexPrefixSource (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (A : Set (EventPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  ((K.eventLaw Lam hLam x).restrict
    (frestrictLe (π := fun _ : ℕ => ℝ × S) n ⁻¹' A)).map (normalizedEventSuffix n)

/-- The original prefix marginal restricted to A, followed by the actual
fresh event law from the last prefix state. -/
def eventIndexPrefixMixture (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (A : Set (EventPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  (((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).restrict A).bind
    (prefixFreshEventKernel K hLam n)

theorem eventIndexPrefixSource_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ)
    (A : Set (EventPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂eventIndexPrefixSource K hLam x n A) =
      ∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then
        F (normalizedEventSuffix n w) else 0 ∂K.eventLaw Lam hLam x := by
  unfold eventIndexPrefixSource
  rw [lintegral_map hF (measurable_normalizedEventSuffix n),
    ← lintegral_indicator (hA.preimage (measurable_frestrictLe n))]
  apply lintegral_congr
  intro w
  by_cases hw : frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A <;>
    simp [Set.indicator, hw]

theorem eventIndexPrefixMixture_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ)
    (A : Set (EventPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂eventIndexPrefixMixture K hLam x n A) =
      ∫⁻ u, if u ∈ A then
        (∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  unfold eventIndexPrefixMixture
  rw [Measure.lintegral_bind (prefixFreshEventKernel K hLam n).aemeasurable hF.aemeasurable,
    ← lintegral_indicator hA]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ A <;> simp [Set.indicator, hu, prefixFreshEventKernel]

/-- Whole infinite normalized suffix equality at a deterministic source event
index, retaining every measurable prefix event. -/
theorem eventIndex_prefix_event_law (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ)
    (A : Set (EventPrefix S n)) (hA : MeasurableSet A) :
    eventIndexPrefixSource K hLam x n A = eventIndexPrefixMixture K hLam x n A := by
  let μ := eventIndexPrefixSource K hLam x n A
  let ν := eventIndexPrefixMixture K hLam x n A
  let : IsFiniteMeasure μ := by unfold μ eventIndexPrefixSource; infer_instance
  have hbox (I : Finset ℕ) (t : ℕ → Set (ℝ × S)) (ht : ∀ i, MeasurableSet (t i)) :
      μ ((I : Set ℕ).pi t) = ν ((I : Set ℕ).pi t) := by
    let b : ℕ → ℝ × S → ℝ≥0∞ := fun i z =>
      if i ∈ I then (if z ∈ t i then 1 else 0) else 1
    have hb (i : ℕ) : Measurable (b i) := by
      by_cases hi : i ∈ I
      · simp only [b, hi, ite_true]
        exact Measurable.ite (ht i) measurable_const measurable_const
      · simpa only [b, hi, ite_false] using
          (measurable_const : Measurable (fun _ : ℝ × S => (1 : ℝ≥0∞)))
    have hm := measurable_fullCylinderWeight (I.sup id + 2) b hb
    have hset : MeasurableSet ((I : Set ℕ).pi t) :=
      MeasurableSet.pi I.countable_toSet (fun i _ => ht i)
    have he : fullCylinderWeight (I.sup id + 2) b =
        ((I : Set ℕ).pi t).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext v
      exact paddedBoxWeight_indicator I t v
    calc
      _ = ∫⁻ v, fullCylinderWeight (I.sup id + 2) b v ∂μ := by
        rw [he, lintegral_indicator hset]
        simp
      _ = _ := eventIndexPrefixSource_lintegral K hLam x n A hA _ hm
      _ = _ := eventIndex_fullCylinder_prefix K hLam x n (I.sup id + 1) A hA b hb
      _ = ∫⁻ v, fullCylinderWeight (I.sup id + 2) b v ∂ν :=
        (eventIndexPrefixMixture_lintegral K hLam x n A hA _ hm).symm
      _ = _ := by rw [he, lintegral_indicator hset]; simp
  apply ext_of_generate_finite
    (squareCylinders (fun _ : ℕ => {s : Set (ℝ × S) | MeasurableSet s}))
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (by
        intro i
        change MeasurableSet (Set.univ : Set (ℝ × S))
        exact MeasurableSet.univ))
  · rintro C ⟨I, t, ht, rfl⟩
    exact hbox I t (fun i => ht i (mem_univ i))
  · simpa using hbox ∅ (fun _ => univ) (fun _ => MeasurableSet.univ)

/-- Reward form of the entire deterministic event-index suffix law. -/
theorem eventLaw_eventIndex_full_suffix_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ)
    (A : Set (EventPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then
        F (normalizedEventSuffix n w) else 0 ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if u ∈ A then
        (∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  rw [← eventIndexPrefixSource_lintegral K hLam x n A hA F hF,
    eventIndex_prefix_event_law K hLam x n A hA,
    eventIndexPrefixMixture_lintegral K hLam x n A hA F hF]

end
end CTMCHeredity20261019
