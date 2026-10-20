module

public import P161Formal.SourceRenewalStops

/-! Quantitative composition through genuine observed-prefix partial stops.
The future estimate is applied to the unconditioned fresh actual law and
multiplied by attained stopping mass. Nonhitting mass remains explicit. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory Preorder HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019
open scoped BigOperators ENNReal Classical
noncomputable section

local instance renewalBoundMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalBoundMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩

section PartialStop
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem partial_stop_future_event_bound (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (hA : ∀ n, MeasurableSet (A n))
    (hDisj : Pairwise (fun n m => Disjoint (eventIndexStopSlice A n) (eventIndexStopSlice A m)))
    (B : Set (ℕ → ℝ × S)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hbound : ∀ z : S, K.eventLaw Lam hLam z B ≤ c) :
    eventIndexSliceFamilySource K hLam x A B ≤ c := by
  have hpart (n : ℕ) : eventIndexPrefixMixture K hLam x n (A n) B ≤
      c*eventIndexPrefixMixture K hLam x n (A n) Set.univ := by
    let ν := ((K.eventLaw Lam hLam x).map
      (frestrictLe (π := fun _ : ℕ => ℝ × S) n)).restrict (A n)
    change (ν.bind (prefixFreshEventKernel K hLam n)) B ≤
      c*(ν.bind (prefixFreshEventKernel K hLam n)) Set.univ
    rw [Measure.bind_apply hB (prefixFreshEventKernel K hLam n).aemeasurable,
      Measure.bind_apply MeasurableSet.univ (prefixFreshEventKernel K hLam n).aemeasurable]
    have hunit : (∫⁻ u, (prefixFreshEventKernel K hLam n) u Set.univ ∂ν) = ν Set.univ := by
      change (∫⁻ u, K.eventLaw Lam hLam (u ⟨n,Finset.mem_Iic.mpr le_rfl⟩).2 Set.univ ∂ν) = _
      simp only [measure_univ,lintegral_const,one_mul]
    rw [hunit]
    calc
      _ ≤ ∫⁻ _u, c ∂ν := lintegral_mono (fun u => hbound (u ⟨n,Finset.mem_Iic.mpr le_rfl⟩).2)
      _ = _ := lintegral_const c
  rw [eventIndex_stop_family_law K hLam x A hA]
  calc
    _ = ∑' n : ℕ, eventIndexPrefixMixture K hLam x n (A n) B :=
      Measure.sum_apply _ hB
    _ ≤ ∑' n : ℕ, c*eventIndexPrefixMixture K hLam x n (A n) Set.univ :=
      ENNReal.tsum_le_tsum hpart
    _ = c*(∑' n : ℕ, eventIndexPrefixMixture K hLam x n (A n) Set.univ) :=
      ENNReal.tsum_mul_left
    _ = c*eventIndexSliceFamilyMixture K hLam x A Set.univ := by
      rw [eventIndexSliceFamilyMixture,Measure.sum_apply _ MeasurableSet.univ]
    _ = c*eventIndexSliceFamilySource K hLam x A Set.univ := by
      rw [eventIndex_stop_family_law K hLam x A hA]
    _ ≤ c*1 := mul_le_mul_right
      (eventIndex_stopped_law_subprobability K hLam x A hA hDisj) c
    _ = c := mul_one c

theorem measure_stopped_future_union_le (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ∀ n : ℕ, Set (EventPrefix S n))
    (B : Set (ℕ → ℝ × S)) (hB : MeasurableSet B) :
    K.eventLaw Lam hLam x
      (⋃ n : ℕ, eventIndexStopSlice A n ∩ normalizedEventSuffix n ⁻¹' B) ≤
        eventIndexSliceFamilySource K hLam x A B := by
  calc
    _ ≤ ∑' n : ℕ, K.eventLaw Lam hLam x
        (eventIndexStopSlice A n ∩ normalizedEventSuffix n ⁻¹' B) := measure_iUnion_le _
    _ = _ := by
      rw [eventIndexSliceFamilySource,Measure.sum_apply _ hB]
      apply tsum_congr
      intro n
      rw [eventIndexPrefixSource,Measure.map_apply (measurable_normalizedEventSuffix n) hB,
        Measure.restrict_apply (hB.preimage (measurable_normalizedEventSuffix n))]
      congr 1
      exact Set.inter_comm _ _

end PartialStop

end
end P161Formal
