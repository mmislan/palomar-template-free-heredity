module

public import proofs.CTMCHeredity20261019.PhysicalCutCylinders
public import proofs.CTMCHeredity20261019.PhysicalCutMeasurable
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

@[expose] public section

/-!
# Whole-suffix laws on one physical arrival slice

For every measurable prefix event A, the actual physical residual suffix,
restricted to A and one arrival slice, is the exact survival-weighted mixture
of fresh actual event laws from the current state. Square-cylinder uniqueness
extends the previously proved finite reward identities to every measurable
event of the entire infinite suffix. No suffix-law premise is introduced.

Keeping A explicit avoids product-space uniqueness bookkeeping while retaining
all measurable prefix tests. Summation over the random arrival index is not
performed here.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical
noncomputable section

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def fullCylinderWeight (m : ℕ) (b : ℕ → ℝ × S → ℝ≥0∞)
    (v : ℕ → ℝ × S) : ℝ≥0∞ := ∏ i ∈ Finset.range m, b i (v i)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_fullCylinderWeight (m : ℕ) (b : ℕ → ℝ × S → ℝ≥0∞)
    (hb : ∀ i, Measurable (b i)) : Measurable (fullCylinderWeight m b) := by
  unfold fullCylinderWeight
  exact Finset.measurable_prod _ (fun i _ => (hb i).comp (measurable_pi_apply i))

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem fullCylinderWeight_split (k : ℕ) (b : ℕ → ℝ × S → ℝ≥0∞)
    (v : ℕ → ℝ × S) :
    fullCylinderWeight (k + 2) b v =
      b 0 (v 0) * b 1 (v 1) * futureCylinderWeight 1 k (fun i => b (i + 2)) v := by
  unfold fullCylinderWeight
  rw [show k + 2 = 2 + k by omega, Finset.prod_range_add]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold futureCylinderWeight
  apply congrArg (fun r => b 0 (v 0) * b 1 (v 1) * r)
  apply Finset.prod_congr rfl
  intro i _
  have h1 : 2 + i = i + 2 := by omega
  have h2 : 1 + i + 1 = i + 2 := by omega
  rw [h1, h2]

/-- The finite-cylinder slice law including coordinate zero and a fixed
arbitrary measurable prefix event. -/
theorem physicalCut_fullCylinder_prefix (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (b : ℕ → ℝ × S → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) :
    (∫⁻ w, if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
          frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then
        fullCylinderWeight (k + 2) b (physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T ∧ u ∈ A then
        ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          (∫⁻ v, fullCylinderWeight (k + 2) b v
            ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let start : CutPrefix S n → ℝ≥0∞ := fun u =>
    b 0 (0, (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
  let H : CutPrefix S n × (ℝ × S) → ℝ≥0∞ := fun p =>
    if p.1 ∈ A then start p.1 * b 1 p.2 else 0
  have hstart : Measurable start :=
    (hb 0).comp (measurable_const.prodMk
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
        ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd)
  have hH : Measurable H := Measurable.ite (hA.preimage measurable_fst)
    ((hstart.comp measurable_fst).mul ((hb 1).comp measurable_snd)) measurable_const
  have h := eventLaw_physicalCut_cylinder_slice K hLam x n k T H hH
    (fun i => b (i + 2)) (fun i => hb (i + 2)) (fun _ => 1)
  calc
    _ = ∫⁻ w, if arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w then
        H (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T 1) *
          futureCylinderWeight 1 k (fun i => b (i + 2)) (physicalCut w n T) *
            (1 : ℝ≥0∞) else 0 ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      by_cases hs : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w
      · by_cases ha : frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A
        · simp only [hs, ha, true_and, ite_true, H, start, mul_one,
            fullCylinderWeight_split, physicalCut_zero, frestrictLe_apply]
        · simp [hs, ha, H]
      · simp [hs]
    _ = _ := h
    _ = _ := by
      apply lintegral_congr
      intro u
      by_cases hs : cutPrefixArrival n u ≤ T
      · by_cases ha : u ∈ A
        · simp only [hs, ha, true_and, ite_true]
          congr 1
          apply lintegral_congr_ae
          filter_upwards [K.ae_event_initial hLam
            (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2] with v hv
          simp only [H, ha, ite_true, start, mul_one, fullCylinderWeight_split, hv]
        · simp [hs, ha, H]
      · simp [hs]

/-- The actual fresh path law, measurably indexed by the last prefix state. -/
def prefixFreshEventKernel (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (n : ℕ) : ProbabilityTheory.Kernel (CutPrefix S n) (ℕ → ℝ × S) where
  toFun u := K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  measurable' := (measurable_of_countable (fun y : S => K.eventLaw Lam hLam y)).comp
    (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd

instance prefixFreshEventKernel_markov (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (n : ℕ) : IsMarkovKernel (prefixFreshEventKernel K hLam n) where
  isProbabilityMeasure u := by
    change IsProbabilityMeasure (K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
    infer_instance

def prefixCutDensity {n : ℕ} (T Lam : ℝ) (A : Set (CutPrefix S n))
    (u : CutPrefix S n) : ℝ≥0∞ :=
  if cutPrefixArrival n u ≤ T ∧ u ∈ A then
    ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) else 0

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_prefixCutDensity {n : ℕ} (T Lam : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A) :
    Measurable (prefixCutDensity T Lam A) := by
  unfold prefixCutDensity
  apply Measurable.ite
    ((measurableSet_le (measurable_cutPrefixArrival n) measurable_const).inter hA)
  · simpa only [Function.comp_def, Pi.sub_apply, neg_mul] using (ENNReal.measurable_ofReal.comp
      (((measurable_const.sub (measurable_cutPrefixArrival n)).const_mul (-Lam)).exp))
  · exact measurable_const

/-- Actual suffix law restricted to the chosen prefix event and arrival slice. -/
def physicalCutPrefixSource (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) (A : Set (CutPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  ((K.eventLaw Lam hLam x).restrict {w | (arrivalTime n w ≤ T ∧
    T < arrivalTime (n + 1) w) ∧ frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A}).map
      (fun w => physicalCut w n T)

/-- The exact survival-weighted mixture of actual fresh event laws. -/
def physicalCutPrefixMixture (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) (A : Set (CutPrefix S n)) :
    Measure (ℕ → ℝ × S) :=
  (((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).withDensity
    (prefixCutDensity T Lam A)).bind (prefixFreshEventKernel K hLam n)

theorem physicalCutPrefixSource_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂physicalCutPrefixSource K hLam x n T A) =
      ∫⁻ w, if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then F (physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x := by
  have hs : MeasurableSet {w : ℕ → ℝ × S |
      (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A} :=
    (measurableSet_physicalCut_segment (S := S) n T).inter
      (hA.preimage (measurable_frestrictLe n))
  unfold physicalCutPrefixSource
  rw [lintegral_map hF (measurable_physicalCut n T), ← lintegral_indicator hs]
  apply lintegral_congr
  intro w
  by_cases hw : (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
      frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A <;>
    simp [Set.indicator, hw]

theorem physicalCutPrefixMixture_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂physicalCutPrefixMixture K hLam x n T A) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T ∧ u ∈ A then
        ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          (∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  have hq : Measurable (fun u : CutPrefix S n =>
      ∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) :=
    (measurable_of_countable (fun y : S => ∫⁻ v, F v ∂K.eventLaw Lam hLam y)).comp
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
        ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd
  unfold physicalCutPrefixMixture
  rw [Measure.lintegral_bind
    (prefixFreshEventKernel K hLam n).aemeasurable hF.aemeasurable]
  change (∫⁻ u, (∫⁻ v, F v ∂K.eventLaw Lam hLam
      (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
      ∂(((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).withDensity
        (prefixCutDensity T Lam A))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_prefixCutDensity T Lam A hA) hq]
  apply lintegral_congr
  intro u
  by_cases hu : cutPrefixArrival n u ≤ T ∧ u ∈ A <;>
    simp [prefixCutDensity, hu, Pi.mul_apply]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- A finite box padded to an initial interval has exactly its indicator reward. -/
theorem paddedBoxWeight_indicator (I : Finset ℕ) (t : ℕ → Set (ℝ × S))
    (v : ℕ → ℝ × S) :
    fullCylinderWeight (I.sup id + 2)
      (fun i z => if i ∈ I then (if z ∈ t i then 1 else 0) else 1) v =
      ((I : Set ℕ).pi t).indicator (fun _ => (1 : ℝ≥0∞)) v := by
  unfold fullCylinderWeight
  calc
    _ = ∏ i ∈ Finset.range (I.sup id + 2),
        (if i ∈ I → v i ∈ t i then (1 : ℝ≥0∞) else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ I <;> simp [hi]
    _ = if ∀ i ∈ Finset.range (I.sup id + 2), i ∈ I → v i ∈ t i then 1 else 0 := by
      simp only [Finset.prod_boole]
      by_cases hc : ∀ i ∈ Finset.range (I.sup id + 2), i ∈ I → v i ∈ t i <;>
        simp
    _ = _ := by
      have hc : (∀ i ∈ Finset.range (I.sup id + 2), i ∈ I → v i ∈ t i) ↔
          v ∈ (I : Set ℕ).pi t := by
        change (∀ i ∈ Finset.range (I.sup id + 2), i ∈ I → v i ∈ t i) ↔
          ∀ i ∈ I, v i ∈ t i
        constructor
        · intro h i hi
          have hb : i ≤ I.sup id := Finset.le_sup (f := id) hi
          exact h i (Finset.mem_range.mpr (by omega)) hi
        · intro h i _ hi
          exact h i hi
      rw [hc]
      rfl

/-- Equality of the whole infinite suffix measures, for every measurable
prefix event, derived from finite cylinders by Mathlib's generating pi-system
uniqueness. This is the physical-cut law on one fixed arrival slice. -/
theorem physicalCut_prefix_event_law (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A) :
    physicalCutPrefixSource K hLam x n T A = physicalCutPrefixMixture K hLam x n T A := by
  let μ := physicalCutPrefixSource K hLam x n T A
  let ν := physicalCutPrefixMixture K hLam x n T A
  let : IsFiniteMeasure μ := by unfold μ physicalCutPrefixSource; infer_instance
  have hbox (I : Finset ℕ) (t : ℕ → Set (ℝ × S)) (ht : ∀ i, MeasurableSet (t i)) :
      μ ((I : Set ℕ).pi t) = ν ((I : Set ℕ).pi t) := by
    let b : ℕ → ℝ × S → ℝ≥0∞ := fun i z =>
      if i ∈ I then (if z ∈ t i then 1 else 0) else 1
    have hb (i : ℕ) : Measurable (b i) := by
      by_cases hi : i ∈ I
      · simp only [b, hi, ite_true]
        exact Measurable.ite (ht i) measurable_const measurable_const
      · simpa only [b, hi, ite_false] using (measurable_const : Measurable (fun _ : ℝ × S => (1 : ℝ≥0∞)))
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
      _ = _ := physicalCutPrefixSource_lintegral K hLam x n T A hA _ hm
      _ = _ := physicalCut_fullCylinder_prefix K hLam x n (I.sup id) T A hA b hb
      _ = ∫⁻ v, fullCylinderWeight (I.sup id + 2) b v ∂ν :=
        (physicalCutPrefixMixture_lintegral K hLam x n T A hA _ hm).symm
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

/-- Reward form for every measurable function of the entire infinite suffix,
with every measurable prefix event retained. Finite-cylinder restrictions have
been removed by the preceding measure equality. -/
theorem eventLaw_physicalCut_full_suffix_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then F (physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T ∧ u ∈ A then
        ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          (∫⁻ v, F v ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  rw [← physicalCutPrefixSource_lintegral K hLam x n T A hA F hF,
    physicalCut_prefix_event_law K hLam x n T A hA,
    physicalCutPrefixMixture_lintegral K hLam x n T A hA F hF]

end
end CTMCHeredity20261019
