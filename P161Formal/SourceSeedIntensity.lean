module

public import P161Formal.SourceContractBridge
public import P161Formal.WeightedRawHistory
public import P161Formal.StockArithmetic

/-! Actual accepted seed labels, including the source intensity and one-step
exponential tilt. Unused proposal futures and the old sentinel are not entries. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance seedIntensityMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance seedIntensityMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def sourceSeedMark (seed : ℝ) : Option (Mark (literalSourcePar seed)) → Prop
  | some (Sum.inl (_,Sum.inl (t,_))) => t = 0
  | _ => False

def sourceSeedState (seed : ℝ) (z : CF3MarkedKernel.State (literalSourcePar seed)) : Prop :=
  sourceSeedMark seed z.2

set_option backward.isDefEq.respectTransparency false in
theorem source_seed_event_eq (seed : ℝ) (hseed : 0 ≤ seed)
    (z : CF3MarkedKernel.State (literalSourcePar seed)) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).event (sourceSeedState seed) z =
      (∑ i : SiteId, ∑ j : SpeciesId, sourceIntensity (literalSourcePar seed)
        (coreRepresent z.1) (Sum.inl (i,Sum.inl (0,j))))/
          FunctionalCapacity.cf3Rate (literalSourcePar seed) := by
  rw [Kernel.event,CF3MarkedKernel.kernel]
  let g : Option (Mark (literalSourcePar seed)) → ℝ := fun m => if sourceSeedMark seed m then 1 else 0
  change (MarkedKernel.kernel (coreChannels (literal_source_valid seed hseed))
    (CF3MarkedKernel.rate_positive (literal_source_valid seed hseed))
    (CF3MarkedKernel.core_channel_bound (literal_source_valid seed hseed))).expect
      (fun y => g y.2) z = _
  rw [MarkedKernel.kernel_expect_mark]
  have hgNone : g none = 0 := by simp [g,sourceSeedMark]
  have hgDiv (d : Fin 4 × (Option (Fin 3) × (FunctionalCapacity.Split 3 2048 × Fin 4))) :
      g (some (Sum.inr d)) = 0 := by simp [g,sourceSeedMark]
  have hgBool (i : Fin 4) (b : Bool) : g (some (Sum.inl (i,Sum.inr b))) = 0 := by
    simp [g,sourceSeedMark]
  have hgChem (i : Fin 4) (t : Fin 5) (j : Fin 3) :
      g (some (Sum.inl (i,Sum.inl (t,j)))) = if t = 0 then 1 else 0 := by
    by_cases ht : t = 0 <;> simp [g,sourceSeedMark,ht]
  unfold MarkedUniformization.expect
  rw [Fintype.sum_option]
  simp only [hgNone,mul_zero,zero_add,Fintype.sum_sum_type,Fintype.sum_prod_type,
    hgDiv,hgBool,hgChem,Finset.sum_const_zero,add_zero]
  change (∑ i : SiteId, ∑ t : Fin 5, ∑ j : SpeciesId,
    sourceIntensity (literalSourcePar seed) (coreRepresent z.1) (Sum.inl (i,Sum.inl (t,j)))/
      FunctionalCapacity.cf3Rate (literalSourcePar seed)*(if t = 0 then 1 else 0)) = _
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_div]

theorem source_seed_channel_le_six (seed : ℝ) (hseed6 : seed ≤ 6)
    (x : SourceState (literalSourcePar seed)) (i : SiteId) (j : SpeciesId) :
    sourceIntensity (literalSourcePar seed) x (Sum.inl (i,Sum.inl (0,j))) ≤ 6 := by
  have ha : (0 : ℝ) ≤ (((x i).a j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : (((x i).a j : ℕ) : ℝ) ≤ 2048 := by
    exact_mod_cast (show ((x i).a j : ℕ) ≤ 2048 by
      have hh := ((x i).a j).isLt
      change ((x i).a j : ℕ) < 2048+1 at hh
      omega)
  have hq : 0 ≤ 1-(((x i).a j : ℕ) : ℝ)/2048 := by linarith
  have hq1 : 1-(((x i).a j : ℕ) : ℝ)/2048 ≤ 1 := by linarith
  change seed*(1-(((x i).a j : ℕ) : ℝ)/2048) ≤ 6
  simpa only [mul_one] using mul_le_mul hseed6 hq1 hq (by norm_num : (0 : ℝ) ≤ 6)

theorem source_seed_event_le (seed : ℝ) (hseed : 0 ≤ seed) (hseed6 : seed ≤ 6)
    (z : CF3MarkedKernel.State (literalSourcePar seed)) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).event (sourceSeedState seed) z ≤
      72/FunctionalCapacity.cf3Rate (literalSourcePar seed) := by
  rw [source_seed_event_eq seed hseed z]
  apply div_le_div_of_nonneg_right _ (CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).le
  have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (j : SpeciesId) (_ : j ∈ Finset.univ) =>
      source_seed_channel_le_six seed hseed6 (coreRepresent z.1) i j))
  norm_num at h
  exact h

theorem source_seed_step_nonnegative (seed : ℝ) (hseed : 0 ≤ seed) :
    0 ≤ 1+(72/FunctionalCapacity.cf3Rate (literalSourcePar seed))*(Real.exp (1/10)-1) := by
  have he : (0 : ℝ) ≤ Real.exp (1/10)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  exact add_nonneg (by norm_num) (mul_nonneg
    (div_nonneg (by norm_num) (CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).le) he)

theorem source_seed_nn_step_bound (seed : ℝ) (hseed : 0 ≤ seed) (hseed6 : seed ≤ 6)
    (z : CF3MarkedKernel.State (literalSourcePar seed)) :
    nnReward ((CF3MarkedKernel.kernel (literal_source_valid seed hseed)).pmf z)
      (fun y => ENNReal.ofReal (tilt (sourceSeedState seed) (1/10) y)*ENNReal.ofReal (1 : ℝ)) ≤
      ENNReal.ofReal (1+(72/FunctionalCapacity.cf3Rate (literalSourcePar seed))*(Real.exp (1/10)-1))*
        ENNReal.ofReal (1 : ℝ) := by
  simp only [ENNReal.ofReal_one,mul_one]
  rw [pmf_nnReward_ofReal _ _ (tilt_nonneg _ _),expect_tilt]
  apply ENNReal.ofReal_le_ofReal
  have he : (0 : ℝ) ≤ Real.exp (1/10)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have h := mul_le_mul_of_nonneg_left (source_seed_event_le seed hseed hseed6 z) he
  nlinarith only [h]

end
end P161Formal
