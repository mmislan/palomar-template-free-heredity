module

public import proofs.CTMCHeredity20261019.PhysicalCutLaw
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# Joint past and whole-future law on an actual physical arrival slice

The past is the complete finite source prefix through the last arrival before
the physical cut. The future is the actual residual sequence, including its
zero initial hold and the residual first positive hold. Equality on measurable
rectangles follows from `physicalCut_prefix_event_law`; Mathlib's finite product
measure uniqueness then yields equality on every joint measurable event.

The right side is an actual composition-product with `eventLaw` from the last
prefix state. No conditional-law or Markov-law premise is added.
-/

namespace CTMCHeredity20261019

noncomputable section
open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The actual past and residual future, restricted to one arrival slice. -/
def physicalCutJointSource (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) :
    Measure (CutPrefix S n × (ℕ → ℝ × S)) :=
  ((K.eventLaw Lam hLam x).restrict {w | arrivalTime n w ≤ T ∧
    T < arrivalTime (n + 1) w}).map
      (fun w => (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T))

/-- Survival-weighted prefix marginal, followed by the actual fresh event law
from the state at the last prefix coordinate. -/
def physicalCutJointMixture (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) :
    Measure (CutPrefix S n × (ℕ → ℝ × S)) :=
  (((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).withDensity
    (prefixCutDensity T Lam Set.univ)).compProd (prefixFreshEventKernel K hLam n)

/-- On a rectangle, the joint source law is exactly the previously constructed
suffix law restricted by the measurable prefix event. -/
theorem physicalCutJointSource_apply_prod (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ × S)) (hB : MeasurableSet B) :
    physicalCutJointSource K hLam x n T (A ×ˢ B) =
      physicalCutPrefixSource K hLam x n T A B := by
  have hp := (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n).prodMk
    (measurable_physicalCut (S := S) n T)
  unfold physicalCutJointSource physicalCutPrefixSource
  rw [Measure.map_apply hp (hA.prod hB),
    Measure.map_apply (measurable_physicalCut n T) hB,
    Measure.restrict_apply ((hA.prod hB).preimage hp),
    Measure.restrict_apply (hB.preimage (measurable_physicalCut n T))]
  congr 1
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq]
  tauto

/-- The composition-product has the same rectangle value as the corresponding
fixed-prefix-event mixture. -/
theorem physicalCutJointMixture_apply_prod (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ × S)) (hB : MeasurableSet B) :
    physicalCutJointMixture K hLam x n T (A ×ˢ B) =
      physicalCutPrefixMixture K hLam x n T A B := by
  have hq : Measurable (fun u => prefixFreshEventKernel K hLam n u B) :=
    ProbabilityTheory.Kernel.measurable_coe _ hB
  unfold physicalCutJointMixture physicalCutPrefixMixture
  rw [Measure.compProd_apply_prod hA hB,
    Measure.bind_apply hB (prefixFreshEventKernel K hLam n).aemeasurable,
    ← lintegral_indicator hA,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_prefixCutDensity T Lam Set.univ MeasurableSet.univ) (hq.indicator hA),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_prefixCutDensity T Lam A hA) hq]
  apply lintegral_congr
  intro u
  by_cases hu : cutPrefixArrival n u ≤ T <;> by_cases ha : u ∈ A <;>
    simp [prefixCutDensity, hu, ha, Pi.mul_apply]

/-- The joint law of the full finite past and the whole infinite residual
future on one actual physical arrival slice. -/
theorem physicalCut_joint_law (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) :
    physicalCutJointSource K hLam x n T = physicalCutJointMixture K hLam x n T := by
  let μ := physicalCutJointSource K hLam x n T
  let : IsFiniteMeasure μ := by unfold μ physicalCutJointSource; infer_instance
  apply Measure.ext_prod
  intro A B hA hB
  calc
    _ = physicalCutPrefixSource K hLam x n T A B :=
      physicalCutJointSource_apply_prod K hLam x n T A hA B hB
    _ = physicalCutPrefixMixture K hLam x n T A B :=
      congrArg (fun ν : Measure (ℕ → ℝ × S) => ν B)
        (physicalCut_prefix_event_law K hLam x n T A hA)
    _ = _ := (physicalCutJointMixture_apply_prod K hLam x n T A hA B hB).symm

/-- The actual prefix marginal on the arrival slice is its original marginal
weighted by the probability that the next holding time crosses the cut. -/
theorem physicalCut_joint_prefix_marginal (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) :
    (physicalCutJointSource K hLam x n T).fst =
      ((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).withDensity
        (prefixCutDensity T Lam Set.univ) := by
  rw [physicalCut_joint_law]
  exact Measure.fst_compProd _ _

/-- Every jointly measurable reward of the entire prefix and entire future
factors through the concrete fresh event law from the last prefix state. -/
theorem eventLaw_physicalCut_joint_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (F : CutPrefix S n × (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w then
        F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T then
        ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          (∫⁻ v, F (u, v) ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
        else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  have hp := (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n).prodMk
    (measurable_physicalCut (S := S) n T)
  have hs := measurableSet_physicalCut_segment (S := S) n T
  have hunc : Function.uncurry
      (fun (u : CutPrefix S n) (v : ℕ → ℝ × S) => F (u, v)) = F := by
    funext p
    rcases p with ⟨u, v⟩
    rfl
  have hq : Measurable (fun u : CutPrefix S n =>
      ∫⁻ v, F (u, v) ∂prefixFreshEventKernel K hLam n u) :=
    Measurable.lintegral_kernel_prod_right
      (f := fun (u : CutPrefix S n) (v : ℕ → ℝ × S) => F (u, v))
      (by rw [hunc]; exact hF)
  calc
    _ = ∫⁻ p, F p ∂physicalCutJointSource K hLam x n T := by
      unfold physicalCutJointSource
      rw [lintegral_map hF hp, ← lintegral_indicator hs]
      apply lintegral_congr
      intro w
      by_cases hw : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w <;>
        simp [Set.indicator, hw]
    _ = ∫⁻ p, F p ∂physicalCutJointMixture K hLam x n T := by
      rw [physicalCut_joint_law]
    _ = _ := by
      unfold physicalCutJointMixture
      rw [Measure.lintegral_compProd hF,
        lintegral_withDensity_eq_lintegral_mul _
          (measurable_prefixCutDensity T Lam Set.univ MeasurableSet.univ) hq]
      apply lintegral_congr
      intro u
      by_cases hu : cutPrefixArrival n u ≤ T <;>
        simp [prefixCutDensity, hu, prefixFreshEventKernel, Pi.mul_apply]

end
end CTMCHeredity20261019
