module

public import P161Formal.WeightedCountedHistory
public import P161Formal.CountedLivePoisson

/-! Poisson and physical-clock transfer of the retained terminal fuel tilt.
No independent firing compensator or source-law moment assumption is used. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped ENNReal NNReal Classical
noncomputable section
variable {S : Type*} [Fintype S]

theorem poisson_weighted_tail_bound (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (U : S → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hloc : ∀ x, nnReward (K.pmf x) (fun y => f y*ENNReal.ofReal (U y)) ≤
      ENNReal.ofReal a*ENNReal.ofReal (U x)) (r : ℝ≥0) (x : S) :
    nnReward (K.poissonTrajectory r x) (weightedTailHistory f U) ≤
      ENNReal.ofReal (Real.exp ((r : ℝ)*(a-1)))*ENNReal.ofReal (U x) := by
  have hpmf (n : ℕ) : (poissonMeasure r).toPMF n = ENNReal.ofReal (poissonWeight r n) := by
    calc
      _ = poissonMeasure r {n} := (poissonMeasure r).toPMF_apply n
      _ = _ := poissonMeasure_singleton r n
  rw [Kernel.poissonTrajectory,nnReward_bind]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (poissonWeight r n)*
        ((ENNReal.ofReal a)^n*ENNReal.ofReal (U x)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [hpmf]
      exact mul_le_mul_right (trajectory_weighted_tail_bound K f U _ hloc n x) _
    _ = (∑' n : ℕ, ENNReal.ofReal (poissonWeight r n)*(ENNReal.ofReal a)^n)*
        ENNReal.ofReal (U x) := by
      simp only [←mul_assoc,ENNReal.tsum_mul_right]
    _ = _ := by
      congr 1
      calc
        _ = ∑' n : ℕ, ENNReal.ofReal (poissonWeight r n*a^n) := by
          apply tsum_congr
          intro n
          rw [ENNReal.ofReal_mul (poissonWeight_nonneg r n),ENNReal.ofReal_pow ha]
        _ = _ := by
          rw [←ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg (poissonWeight_nonneg r n) (pow_nonneg ha n))
            (poisson_geometric_sum r a).summable,(poisson_geometric_sum r a).tsum_eq]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem timed_weighted_count_moment (K : HybridCTMC.Kernel S) (P : S → Prop)
    (θ : ℝ) (U : S → ℝ) {Lam a T : ℝ} (hLam : 0 < Lam) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hloc : ∀ x, nnReward (K.pmf x)
      (fun y => ENNReal.ofReal (tilt P θ y)*ENNReal.ofReal (U y)) ≤
        ENNReal.ofReal a*ENNReal.ofReal (U x)) (x : S) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (θ*(selectedCount P T w : ℝ)))*
      ENNReal.ofReal (U (timedState T w)) ∂K.eventLaw Lam hLam x) ≤
      ENNReal.ofReal (Real.exp (Lam*T*(a-1)))*ENNReal.ofReal (U x) := by
  have he (w : ℕ → ℝ × S) : ENNReal.ofReal (Real.exp (θ*(selectedCount P T w : ℝ)))*
      ENNReal.ofReal (U (timedState T w)) =
      weightedTailHistory (fun y => ENNReal.ofReal (tilt P θ y)) U (timedHistory T w) := by
    rw [weightedTailHistory,history_terminal_timed_history,tailWeight,wholeWeight_tilt]
    rfl
  simp_rw [he]
  rw [K.timedHistory_reward hLam hT]
  exact poisson_weighted_tail_bound K _ U ha hloc ⟨Lam*T,mul_nonneg hLam.le hT⟩ x

end
end P161Formal
