module

public import P161Formal.SourceFeedGenerator
public import P161Formal.WeightedRawHistory

/-! The accepted-recharge tilt is docked to the actual finite marked source
kernel. Only positive-index labels will be counted by the checked history law;
the old last-mark sentinel supplies no feed entry. -/

@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance feedKernelRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance feedKernelRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance feedKernelMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance feedKernelMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def sourceFeedMark (seed : ℝ) : Option (Mark (literalSourcePar seed)) → Prop
  | some (Sum.inl (_,Sum.inr false)) => True
  | _ => False

def sourceFeedState (seed : ℝ) (z : CF3MarkedKernel.State (literalSourcePar seed)) : Prop :=
  sourceFeedMark seed z.2

theorem core_fuel_witness_positive (seed : ℝ) (x : CoreState (literalSourcePar seed)) :
    0 < coreFuelWitness seed x := fuel_occupation_positive _

theorem source_kernel_marked_fuel_expect (seed : ℝ) (hseed : 0 ≤ seed)
    (keep : Option (Mark (literalSourcePar seed)) → ℝ)
    (x : SourceState (literalSourcePar seed)) (old : Option (Mark (literalSourcePar seed))) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).expect
      (fun y => keep y.2*coreFuelWitness seed y.1) (coreProject x,old) =
      MarkedUniformization.expect (sourceChannels (literal_source_valid seed hseed))
        (FunctionalCapacity.cf3Rate (literalSourcePar seed)) x
        (fun m => keep m*sourceFuelWitness
          (MarkedUniformization.next (sourceChannels (literal_source_valid seed hseed)) x m)) := by
  rw [CF3MarkedKernel.kernel,MarkedKernel.kernel_expect]
  unfold MarkedUniformization.expect
  apply Finset.sum_congr rfl
  intro m _
  rw [←CF3MarkedKernel.proposalWeight_lump (literal_source_valid seed hseed)
    (FunctionalCapacity.cf3Rate (literalSourcePar seed)) x m]
  dsimp only
  rw [←CF3MarkedKernel.proposalNext_project (literal_source_valid seed hseed) x m,
    core_fuel_witness_project seed]

theorem source_kernel_feed_fuel_part (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (old : Option (Mark (literalSourcePar seed))) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).expect
      (fun y => (if sourceFeedMark seed y.2 then 1 else 0)*coreFuelWitness seed y.1)
        (coreProject x,old) = sourceFeedRechargePart seed x/
          FunctionalCapacity.cf3Rate (literalSourcePar seed) := by
  rw [source_kernel_marked_fuel_expect seed hseed
    (fun m => if sourceFeedMark seed m then (1 : ℝ) else 0) x old]
  have hs : MarkedUniformization.expect (sourceChannels (literal_source_valid seed hseed))
      (FunctionalCapacity.cf3Rate (literalSourcePar seed)) x
      (fun m => (if sourceFeedMark seed m then 1 else 0)*sourceFuelWitness
        (MarkedUniformization.next (sourceChannels (literal_source_valid seed hseed)) x m)) =
      ∑ i : SiteId, ((FunctionalCapacity.cf3 (literalSourcePar seed)).rc (x i) (Sum.inr false)/
        FunctionalCapacity.cf3Rate (literalSourcePar seed))*
          sourceFuelWitness (Function.update x i {x i with R := true}) := by
    simp [MarkedUniformization.expect,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_prod_type,
      sourceFeedMark,MarkedUniformization.weight,MarkedUniformization.next,
      sourceChannels,sourceIntensity,sourceNext,FunctionalCapacity.cf3,literalSourcePar]
  rw [hs,sourceFeedRechargePart,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have he : (FunctionalCapacity.cf3 (literalSourcePar seed)).rc (x i) (Sum.inr false) =
      if (x i).R then 0 else 4000000 := by
    cases hr : (x i).R <;> norm_num [FunctionalCapacity.cf3,literalSourcePar,FunctionalCapacity.Site.r,hr]
  rw [he]
  ring

theorem source_kernel_feed_tilt_expect (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (old : Option (Mark (literalSourcePar seed))) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).expect
      (fun y => tilt (sourceFeedState seed) stockEta y*coreFuelWitness seed y.1) (coreProject x,old) =
      sourceFuelWitness x+sourceFeedTiltedGenerator seed x/
        FunctionalCapacity.cf3Rate (literalSourcePar seed) := by
  have he : (fun y : CF3MarkedKernel.State (literalSourcePar seed) =>
      tilt (sourceFeedState seed) stockEta y*coreFuelWitness seed y.1) =
      (fun y => coreFuelWitness seed y.1+(Real.exp stockEta-1)*
        ((if sourceFeedMark seed y.2 then 1 else 0)*coreFuelWitness seed y.1)) := by
    funext y
    by_cases hy : sourceFeedMark seed y.2 <;> simp [tilt,sourceFeedState,hy]
    ring
  rw [he,Kernel.expect_add,Kernel.expect_scale,source_kernel_feed_fuel_part seed hseed x old]
  have hb := CF3MarkedKernel.kernel_source_expect (literal_source_valid seed hseed) (coreFuelWitness seed) x old
  change (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).expect
    (fun y => coreFuelWitness seed y.1) (coreProject x,old) =
    sourceFuelWitness x+FunctionalCapacity.cf3Gen (literalSourcePar seed) sourceFuelWitness x/
      FunctionalCapacity.cf3Rate (literalSourcePar seed) at hb
  rw [hb,sourceFeedTiltedGenerator]
  ring

theorem source_feed_real_step_bound (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (old : Option (Mark (literalSourcePar seed))) :
    (CF3MarkedKernel.kernel (literal_source_valid seed hseed)).expect
      (fun y => tilt (sourceFeedState seed) stockEta y*coreFuelWitness seed y.1) (coreProject x,old) ≤
        (1+(4*stockFeedK1+1)/FunctionalCapacity.cf3Rate (literalSourcePar seed))*sourceFuelWitness x := by
  rw [source_kernel_feed_tilt_expect seed hseed x old]
  have h := div_le_div_of_nonneg_right (source_feed_tilted_generator_bound seed hseed x)
    (CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).le
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

theorem source_feed_step_nonnegative (seed : ℝ) (hseed : 0 ≤ seed) :
    0 ≤ 1+(4*stockFeedK1+1)/FunctionalCapacity.cf3Rate (literalSourcePar seed) := by
  have hk : (0 : ℝ) ≤ 4*stockFeedK1+1 := by norm_num [stockFeedK1]
  exact add_nonneg (by norm_num) (div_nonneg hk (CF3MarkedKernel.rate_positive (literal_source_valid seed hseed)).le)

theorem source_feed_nn_step_bound (seed : ℝ) (hseed : 0 ≤ seed)
    (z : CF3MarkedKernel.State (literalSourcePar seed)) :
    nnReward ((CF3MarkedKernel.kernel (literal_source_valid seed hseed)).pmf z)
      (fun y => ENNReal.ofReal (tilt (sourceFeedState seed) stockEta y)*
        ENNReal.ofReal (coreFuelWitness seed y.1)) ≤
      ENNReal.ofReal (1+(4*stockFeedK1+1)/FunctionalCapacity.cf3Rate (literalSourcePar seed))*
        ENNReal.ofReal (coreFuelWitness seed z.1) := by
  have he : (fun y : CF3MarkedKernel.State (literalSourcePar seed) =>
      ENNReal.ofReal (tilt (sourceFeedState seed) stockEta y)*ENNReal.ofReal (coreFuelWitness seed y.1)) =
      (fun y => ENNReal.ofReal (tilt (sourceFeedState seed) stockEta y*coreFuelWitness seed y.1)) := by
    funext y
    rw [ENNReal.ofReal_mul (tilt_nonneg _ _ _)]
  rw [he]
  have hNN := nnReward_kernel_ofReal (CF3MarkedKernel.kernel (literal_source_valid seed hseed))
    (fun y : CF3MarkedKernel.State (literalSourcePar seed) =>
      tilt (sourceFeedState seed) stockEta y*coreFuelWitness seed y.1)
    (fun y => mul_nonneg (tilt_nonneg _ _ _) (core_fuel_witness_positive seed y.1).le) z
  rw [hNN]
  have h := source_feed_real_step_bound seed hseed (coreRepresent z.1) z.2
  simp only [coreProject_represent] at h
  change _ ≤ (1+(4*stockFeedK1+1)/FunctionalCapacity.cf3Rate (literalSourcePar seed))*coreFuelWitness seed z.1 at h
  exact (ENNReal.ofReal_le_ofReal h).trans_eq
    (ENNReal.ofReal_mul (source_feed_step_nonnegative seed hseed))

end
end P161Formal
