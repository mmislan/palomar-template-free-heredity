module

public import proofs.HybridCTMCInfrastructure.ClockCountSlice

@[expose] public section

/-! The full finite visited history of the actual continuous clock. -/
namespace HybridCTMC.Kernel
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical
noncomputable section
variable {S : Type*}

def timedHistory (T : ℝ) (w : ℕ → ℝ × S) : List S :=
  statePrefix (clockIndex T w) w

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem measurable_timedHistory_observable {E : Type*} [MeasurableSpace E]
    (T : ℝ) (ψ : List S → E) : Measurable (fun w : ℕ → ℝ × S => ψ (timedHistory T w)) := by
  have hm : Measurable (fun p : (ℕ → ℝ × S) × ℕ => ψ (statePrefix p.2 p.1)) :=
    measurable_from_prod_countable_left (fun n => measurable_statePrefix_observable n ψ)
  exact hm.comp (measurable_id.prodMk (measurable_clockIndex T))

theorem timedHistory_reward (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, ψ (timedHistory T w) ∂K.eventLaw Λ hΛ x) =
      nnReward (K.poissonTrajectory ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x) ψ := by
  have he (w : ℕ → ℝ × S) : ψ (timedHistory T w) =
      ∑' n : ℕ, if clockIndex T w = n then ψ (statePrefix n w) else 0 := by
    rw [tsum_eq_single (clockIndex T w) (fun n hn => ite_eq_right (Ne.symm hn))]
    simp [timedHistory]
  have hm (n : ℕ) : Measurable (fun w : ℕ → ℝ × S =>
      if clockIndex T w = n then ψ (statePrefix n w) else 0) :=
    Measurable.ite (measurableSet_eq_fun (measurable_clockIndex T) measurable_const)
      (measurable_statePrefix_observable n ψ) measurable_const
  calc
    _ = ∫⁻ w, ∑' n : ℕ, if clockIndex T w = n then ψ (statePrefix n w) else 0
        ∂K.eventLaw Λ hΛ x := lintegral_congr he
    _ = ∑' n : ℕ, ∫⁻ w, if clockIndex T w = n then ψ (statePrefix n w) else 0
        ∂K.eventLaw Λ hΛ x := lintegral_tsum (fun n => (hm n).aemeasurable)
    _ = ∑' n : ℕ, ENNReal.ofReal (poissonWeight ⟨Λ*T, mul_nonneg hΛ.le hT⟩ n)*
        nnReward (K.trajectory n x) ψ := by
      apply tsum_congr
      intro n
      exact K.clock_count_prefix_poisson hΛ hT x n ψ
    _ = _ := by
      let r : ℝ≥0 := ⟨Λ*T, mul_nonneg hΛ.le hT⟩
      change (∑' n : ℕ, ENNReal.ofReal (poissonWeight r n) *
        nnReward (K.trajectory n x) ψ) = nnReward (K.poissonTrajectory r x) ψ
      have hpmf (n : ℕ) : (poissonMeasure r).toPMF n =
          ENNReal.ofReal (poissonWeight r n) := by
        calc
          _ = poissonMeasure r {n} := (poissonMeasure r).toPMF_apply n
          _ = _ := poissonMeasure_singleton r n
      calc
        _ = nnReward (poissonMeasure r).toPMF
            (fun n => nnReward (K.trajectory n x) ψ) := by
          change (∑' n : ℕ, ENNReal.ofReal (poissonWeight r n) *
            nnReward (K.trajectory n x) ψ) =
              ∑' n : ℕ, (poissonMeasure r).toPMF n * nnReward (K.trajectory n x) ψ
          apply tsum_congr
          intro n
          exact congrArg (fun c : ℝ≥0∞ => c * nnReward (K.trajectory n x) ψ) (hpmf n).symm
        _ = nnReward ((poissonMeasure r).toPMF.bind (fun n => K.trajectory n x)) ψ :=
          (nnReward_bind (poissonMeasure r).toPMF (fun n => K.trajectory n x) ψ).symm
        _ = _ := rfl

theorem timedHistory_event (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (A : List S → Prop) :
    K.eventLaw Λ hΛ x {w | A (timedHistory T w)} =
      mass (K.poissonTrajectory ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x) A := by
  let ψ : List S → ℝ≥0∞ := fun xs => if A xs then 1 else 0
  have hm : MeasurableSet {w : ℕ → ℝ × S | A (timedHistory T w)} := by
    have he : {w : ℕ → ℝ × S | A (timedHistory T w)} =
        (fun w => ψ (timedHistory T w)) ⁻¹' {1} := by
      ext w
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, ψ]
      by_cases h : A (timedHistory T w) <;> simp [h]
    rw [he]
    exact (measurable_timedHistory_observable T ψ) (measurableSet_singleton 1)
  have hi : (fun w : ℕ → ℝ × S => ψ (timedHistory T w)) =
      {w : ℕ → ℝ × S | A (timedHistory T w)}.indicator (fun _ => (1:ℝ≥0∞)) := rfl
  have h := K.timedHistory_reward hΛ hT x ψ
  rw [hi, lintegral_indicator hm] at h
  simpa only [lintegral_one, Measure.restrict_apply_univ, nnReward, mass, ψ,
    mul_ite, mul_one, mul_zero] using h

end
end HybridCTMC.Kernel
