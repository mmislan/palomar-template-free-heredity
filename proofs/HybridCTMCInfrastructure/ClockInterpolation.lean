module

public import proofs.HybridCTMCInfrastructure.EventHorizon

@[expose] public section

/-! Deterministic bridge from event-index martingale bounds to a compensated
coordinate between successive clock arrivals. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section

theorem compensated_segment_bound {A B d H u j : ℝ} (hH : 0 < H)
    (hu0 : 0 ≤ u) (huH : u ≤ H) (hstep : B = A+j-d*H) :
    |A-d*u| ≤ max |A| |B|+|j| := by
  let q := u/H
  have hq0 : 0 ≤ q := div_nonneg hu0 hH.le
  have hq1 : q ≤ 1 := (div_le_one hH).mpr huH
  have habs : |B-j| ≤ |B|+|j| := by simpa using abs_sub_le B 0 j
  have he : A-d*u = (1-q)*A+q*(B-j) := by
    dsimp [q]
    rw [hstep]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ |(1-q)*A|+|q*(B-j)| := abs_add_le _ _
    _ = (1-q)*|A|+q*|B-j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hq1), abs_of_nonneg hq0]
    _ ≤ (1-q)*max |A| |B|+q*(max |A| |B|+|j|) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hq1))
        (mul_le_mul_of_nonneg_left (habs.trans
          (add_le_add (le_max_right |A| |B|) le_rfl)) hq0)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hq1 (abs_nonneg j)]

namespace Kernel
variable {S : Type*} [Fintype S]

omit [Fintype S] in
theorem arrivalTime_mono (w : ℕ → ℝ × S) : Monotone (fun n => arrivalTime n w) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [arrivalTime, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (le_max_left _ _)

theorem horizonSum_eq_eventCompensator (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (T : ℝ) (n : ℕ) (w : ℕ → ℝ × S) (hn : arrivalTime n w ≤ T) :
    K.horizonSum Λ f T n w = K.eventCompensator Λ f n w := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Set.indicator_of_mem
  exact ((arrivalTime_mono w) (Nat.le_of_lt (Finset.mem_range.mp hi))).trans hn

theorem horizonSum_next_eq_eventCompensator (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (T : ℝ) (n : ℕ) (w : ℕ → ℝ × S) (hn : arrivalTime n w ≤ T) :
    K.horizonSum Λ f T (n+1) w = K.eventCompensator Λ f (n+1) w := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Set.indicator_of_mem
  exact ((arrivalTime_mono w) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).trans hn

theorem clock_segment_bound (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (T : ℝ) (n : ℕ) (w : ℕ → ℝ × S) {u : ℝ} (hn : arrivalTime n w ≤ T)
    (hH : 0 < (w (n+1)).1) (hu0 : 0 ≤ u) (huH : u ≤ (w (n+1)).1) :
    |K.eventCompensator Λ f n w-Λ*(K.expect f (w n).2-f (w n).2)*u| ≤
      max |K.horizonSum Λ f T n w| |K.horizonSum Λ f T (n+1) w|+
        |f (w (n+1)).2-f (w n).2| := by
  rw [horizonSum_eq_eventCompensator K Λ f T n w hn,
    horizonSum_next_eq_eventCompensator K Λ f T n w hn]
  apply compensated_segment_bound hH hu0 huH
  have hs := congrFun (K.eventCompensator_succ_sub Λ f n) w
  simp only [Pi.sub_apply, eventIncrement, compensatedStep] at hs
  linarith
end Kernel
end
end HybridCTMC
