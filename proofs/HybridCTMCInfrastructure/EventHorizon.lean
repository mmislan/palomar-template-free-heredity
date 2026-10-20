module

public import proofs.HybridCTMCInfrastructure.EventVariance
public import proofs.HybridCTMCInfrastructure.EventArrival
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

@[expose] public section

/-! Predictable truncation at a deterministic clock horizon. The retained
increment is chosen from the history before its holding time is sampled. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators Classical
noncomputable section
namespace Kernel
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def horizonIncrement (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (T : ℝ) (n : ℕ) :
    (ℕ → ℝ × S) → ℝ := {w | arrivalTime n w ≤ T}.indicator (K.eventIncrement Λ f n)

def horizonSum (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (T : ℝ) (n : ℕ)
    (w : ℕ → ℝ × S) : ℝ := ∑ i ∈ Finset.range n, K.horizonIncrement Λ f T i w

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurableSet_before_horizon (n : ℕ) (T : ℝ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => ℝ × S) n] {w | arrivalTime n w ≤ T} :=
  measurableSet_le (measurable_arrivalTime n) measurable_const

theorem memLp_horizonIncrement (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (T : ℝ) (n : ℕ) :
    MemLp (K.horizonIncrement Λ f T n) 2 (K.eventLaw Λ hΛ x) :=
  (K.memLp_eventIncrement hΛ f x n).indicator
    (Filtration.piLE.le n _ (measurableSet_before_horizon n T))

theorem memLp_horizonSum (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (T : ℝ) (n : ℕ) :
    MemLp (K.horizonSum Λ f T n) 2 (K.eventLaw Λ hΛ x) :=
  memLp_finsetSum _ (fun i _ => K.memLp_horizonIncrement hΛ f x T i)

theorem condExp_horizonIncrement (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (T : ℝ) (n : ℕ) :
    (K.eventLaw Λ hΛ x)[K.horizonIncrement Λ f T n | Filtration.piLE n]
      =ᵐ[K.eventLaw Λ hΛ x] 0 := by
  refine (condExp_indicator (K.integrable_eventIncrement hΛ f x n)
    (measurableSet_before_horizon n T)).trans ?_
  filter_upwards [K.condExp_eventIncrement hΛ f x n] with w hw
  simp only [Set.indicator, Pi.zero_apply] at hw ⊢
  split_ifs <;> simp [hw]

theorem stronglyAdapted_horizonSum (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (T : ℝ) :
    StronglyAdapted Filtration.piLE (K.horizonSum Λ f T) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hd : Measurable[Filtration.piLE n] (K.eventIncrement Λ f i) :=
    (K.measurable_compensatedStep Λ f).comp
      ((measurable_event_eval (Nat.le_of_lt hi')).snd.prodMk
        (measurable_event_eval (Nat.succ_le_of_lt hi')))
  exact hd.indicator (Filtration.piLE.mono (Nat.le_of_lt hi') _ (measurableSet_before_horizon i T))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem horizonSum_succ_sub (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (T : ℝ) (n : ℕ) :
    K.horizonSum Λ f T (n+1)-K.horizonSum Λ f T n = K.horizonIncrement Λ f T n := by
  funext w
  simp [horizonSum, Finset.sum_range_succ]

theorem martingale_horizonSum (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (T : ℝ) :
    Martingale (K.horizonSum Λ f T) Filtration.piLE (K.eventLaw Λ hΛ x) := by
  apply martingale_of_condExp_sub_eq_zero_nat (K.stronglyAdapted_horizonSum Λ f T)
    (fun n => (K.memLp_horizonSum hΛ f x T n).integrable one_le_two)
  intro n
  rw [horizonSum_succ_sub]
  exact K.condExp_horizonIncrement hΛ f x T n

theorem integral_horizonIncrement_square_le (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (T : ℝ) (n : ℕ) {v : ℝ}
    (hv : ∀ s, K.expect (fun y => (f y-f s)^2) s ≤ v) :
    ∫ w, (K.horizonIncrement Λ f T n w)^2 ∂K.eventLaw Λ hΛ x ≤
      v*(K.eventLaw Λ hΛ x).real {w | arrivalTime n w ≤ T} := by
  let A := {w : ℕ → ℝ × S | arrivalTime n w ≤ T}
  have hA := measurableSet_before_horizon (S := S) n T
  have hA0 := Filtration.piLE.le n _ hA
  have he : (fun w => (K.horizonIncrement Λ f T n w)^2) =
      A.indicator (fun w => (K.eventIncrement Λ f n w)^2) := by
    funext w
    simp only [horizonIncrement, Set.indicator, A]
    split_ifs <;> simp
  rw [he, integral_indicator hA0, ← setIntegral_condExp (Filtration.piLE.le n)
    (K.integrable_eventIncrement_square hΛ f x n) hA]
  calc
    _ ≤ ∫ _ in A, v ∂K.eventLaw Λ hΛ x := integral_mono_ae integrable_condExp.restrict
      (integrable_const _) (by
        have hc := (K.condExp_eventIncrement_square hΛ f x n).filter_mono
          (ae_restrict_le (s := A))
        filter_upwards [hc] with w hw
        rw [hw]
        exact hv (w n).2)
    _ = _ := by rw [setIntegral_const]; simp [A, smul_eq_mul, mul_comm]

theorem integral_horizonSum_square_le (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (T : ℝ) (n : ℕ) {v : ℝ}
    (hv : ∀ s, K.expect (fun y => (f y-f s)^2) s ≤ v) :
    ∫ w, (K.horizonSum Λ f T n w)^2 ∂K.eventLaw Λ hΛ x ≤
      v*∑ i ∈ Finset.range n, (K.eventLaw Λ hΛ x).real {w | arrivalTime i w ≤ T} := by
  induction n with
  | zero => simp [horizonSum]
  | succ n ih =>
    have he : K.horizonSum Λ f T (n+1) =
        fun w => K.horizonSum Λ f T n w+K.horizonIncrement Λ f T n w := by
      funext w
      simp [horizonSum, Finset.sum_range_succ]
    rw [he, integral_square_add_of_condExp_zero (Filtration.piLE.le n)
      (K.stronglyAdapted_horizonSum Λ f T n) (K.memLp_horizonSum hΛ f x T n)
      (K.memLp_horizonIncrement hΛ f x T n) (K.condExp_horizonIncrement hΛ f x T n),
      Finset.sum_range_succ, mul_add]
    exact add_le_add ih (K.integral_horizonIncrement_square_le hΛ f x T n hv)
end Kernel
end
end HybridCTMC
