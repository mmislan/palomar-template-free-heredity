module

public import proofs.HybridCTMCInfrastructure.EventMartingale
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Arrival-clock Laplace estimates. Clipping holding times at zero only
specifies paths on an exponential-measure null set and makes clock
monotonicity hold everywhere. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators
noncomputable section

namespace HoldingTime
theorem ae_nonneg (Λ : ℝ) : ∀ᵐ t ∂expMeasure Λ, 0 ≤ t := by
  rw [ae_iff]
  simp only [not_le]
  change expMeasure Λ (Iio 0) = 0
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem integrable_laplace {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < Λ+θ) :
    Integrable (fun t => Real.exp (-θ*t)) (expMeasure Λ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_laplace hΛ hθ]
  positivity

theorem integral_clipped_laplace {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < Λ+θ) :
    ∫ t, Real.exp (-θ*max 0 t) ∂expMeasure Λ = Λ/(Λ+θ) := by
  calc
    _ = ∫ t, Real.exp (-θ*t) ∂expMeasure Λ := integral_congr_ae (by
      filter_upwards [ae_nonneg Λ] with t ht
      rw [max_eq_right ht])
    _ = _ := integral_laplace hΛ hθ

theorem integrable_clipped_laplace {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < Λ+θ) :
    Integrable (fun t => Real.exp (-θ*max 0 t)) (expMeasure Λ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_clipped_laplace hΛ hθ]
  positivity
end HoldingTime

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
namespace Kernel
def arrivalTime (n : ℕ) (w : ℕ → ℝ × S) : ℝ :=
  ∑ i ∈ Finset.range n, max 0 (w (i+1)).1

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem arrivalTime_nonneg (n : ℕ) (w : ℕ → ℝ × S) : 0 ≤ arrivalTime n w :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_arrivalTime (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => ℝ × S) n] (arrivalTime n) := by
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.max (measurable_event_eval (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).fst

omit [MeasurableSingletonClass S] in
theorem clockStep_laplace (K : HybridCTMC.Kernel S) {Λ θ : ℝ} (hΛ : 0 < Λ)
    (hθ : 0 < Λ+θ) (x : S) :
    ∫ z, Real.exp (-θ*max 0 z.1) ∂K.clockStep Λ x = Λ/(Λ+θ) := by
  let := isProbabilityMeasure_expMeasure hΛ
  rw [clockStep, integral_fun_fst (fun t : ℝ => Real.exp (-θ*max 0 t))]
  simp only [probReal_univ, one_smul, HoldingTime.integral_clipped_laplace hΛ hθ]

theorem condExp_holding_laplace (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < Λ+θ) (x : S) (n : ℕ) :
    (K.eventLaw Λ hΛ x)[fun w => Real.exp (-θ*max 0 (w (n+1)).1) | Filtration.piLE n]
      =ᵐ[K.eventLaw Λ hΛ x] fun _ => Λ/(Λ+θ) := by
  refine (K.eventLaw_condExp hΛ x n (fun _ z => Real.exp (-θ*max 0 z.1))
    (by fun_prop) (fun s => (HoldingTime.integrable_clipped_laplace hΛ hθ).comp_fst _)).trans ?_
  exact Filter.Eventually.of_forall (fun w => K.clockStep_laplace hΛ hθ (w n).2)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem arrival_laplace_bound {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) (w : ℕ → ℝ × S) :
    ‖Real.exp (-θ*arrivalTime n w)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (arrivalTime_nonneg n w)

theorem integral_arrival_laplace (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 ≤ θ) (x : S) (n : ℕ) :
    ∫ w, Real.exp (-θ*arrivalTime n w) ∂K.eventLaw Λ hΛ x = (Λ/(Λ+θ))^n := by
  induction n with
  | zero => simp [arrivalTime]
  | succ n ih =>
    let a : (ℕ → ℝ × S) → ℝ := fun w => Real.exp (-θ*arrivalTime n w)
    let b : (ℕ → ℝ × S) → ℝ := fun w => Real.exp (-θ*max 0 (w (n+1)).1)
    have ha : StronglyMeasurable[Filtration.piLE n] a :=
      ((measurable_arrivalTime n).const_mul (-θ)).exp.stronglyMeasurable
    have hb : Integrable b (K.eventLaw Λ hΛ x) :=
      K.eventLaw_integrable hΛ x n (fun _ z => Real.exp (-θ*max 0 z.1)) (by fun_prop)
        (fun s => (HoldingTime.integrable_clipped_laplace hΛ (by linarith)).comp_fst _)
    have hp := condExp_stronglyMeasurable_mul_of_bound (Filtration.piLE.le n) ha hb 1
      (Filter.Eventually.of_forall (arrival_laplace_bound hθ n))
    have he : (fun w : ℕ → ℝ × S => Real.exp (-θ*arrivalTime (n+1) w)) = a*b := by
      funext w
      simp only [arrivalTime, Finset.sum_range_succ, mul_add, Real.exp_add, Pi.mul_apply, a, b]
    rw [he, ← integral_condExp (Filtration.piLE.le n)]
    calc
      _ = ∫ w, a w*(Λ/(Λ+θ)) ∂K.eventLaw Λ hΛ x := integral_congr_ae (by
        filter_upwards [hp, K.condExp_holding_laplace (θ := θ) hΛ (by linarith) x n] with w hw hc
        simpa only [Pi.mul_apply, b, hc] using hw)
      _ = (∫ w, a w ∂K.eventLaw Λ hΛ x)*(Λ/(Λ+θ)) := integral_mul_const _ _
      _ = _ := by rw [ih, pow_succ]

theorem integrable_arrival_laplace (K : HybridCTMC.Kernel S) {Λ θ : ℝ}
    (hΛ : 0 < Λ) (hθ : 0 ≤ θ) (x : S) (n : ℕ) :
    Integrable (fun w => Real.exp (-θ*arrivalTime n w)) (K.eventLaw Λ hΛ x) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (((measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl).const_mul (-θ)).exp
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (arrival_laplace_bound hθ n)

theorem arrival_lower_tail (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 ≤ θ) (x : S) (n : ℕ) (T : ℝ) :
    K.eventLaw Λ hΛ x {w | arrivalTime n w ≤ T} ≤
      ENNReal.ofReal (Real.exp (θ*T)*(Λ/(Λ+θ))^n) := by
  have hi := (K.integrable_arrival_laplace hΛ hθ x n).const_mul (Real.exp (θ*T))
  have hb := hi.measure_le_integral
    (Filter.Eventually.of_forall (fun w => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    (s := {w | arrivalTime n w ≤ T}) (fun w hw => by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hw)])
  rwa [integral_const_mul, integral_arrival_laplace K hΛ hθ] at hb

theorem ae_arrival_crosses (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∃ n, T < arrivalTime n w := by
  rw [ae_iff]
  apply le_antisymm _ bot_le
  have hr0 : 0 ≤ Λ/(Λ+1) := by positivity
  have hr1 : Λ/(Λ+1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (Real.exp T)
  have ht' : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp T*(Λ/(Λ+1))^n))
      Filter.atTop (nhds 0) := by
    have hc : ContinuousAt ENNReal.ofReal (0 : ℝ) := ENNReal.continuous_ofReal.continuousAt
    have ht0 : Filter.Tendsto (fun n : ℕ => Real.exp T*(Λ/(Λ+1))^n)
        Filter.atTop (nhds (0 : ℝ)) := by simpa only [mul_zero] using ht
    convert hc.tendsto.comp ht0 using 1 <;> simp only [Function.comp_def, ENNReal.ofReal_zero]
  apply ge_of_tendsto' ht'
  intro n
  calc
    _ ≤ K.eventLaw Λ hΛ x {w | arrivalTime n w ≤ T} := measure_mono (by
      intro w hw
      exact le_of_not_gt (fun h => hw ⟨n, h⟩))
    _ ≤ _ := by simpa using K.arrival_lower_tail hΛ (by norm_num : 0 ≤ (1:ℝ)) x n T

theorem sum_arrival_lower_tail (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 < θ) (x : S) (n : ℕ) (T : ℝ) :
    ∑ i ∈ Finset.range n, (K.eventLaw Λ hΛ x).real {w | arrivalTime i w ≤ T} ≤
      Real.exp (θ*T)*(Λ+θ)/θ := by
  have hr0 : 0 ≤ Λ/(Λ+θ) := by positivity
  have hr1 : Λ/(Λ+θ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hb (i : ℕ) : (K.eventLaw Λ hΛ x).real {w | arrivalTime i w ≤ T} ≤
      Real.exp (θ*T)*(Λ/(Λ+θ))^i := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (K.arrival_lower_tail hΛ hθ.le x i T)
    simpa only [MeasureTheory.Measure.real, ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (pow_nonneg hr0 i))] using h
  calc
    _ ≤ ∑ i ∈ Finset.range n, Real.exp (θ*T)*(Λ/(Λ+θ))^i := Finset.sum_le_sum (fun i _ => hb i)
    _ = Real.exp (θ*T)*(∑ i ∈ Finset.range n, (Λ/(Λ+θ))^i) := (Finset.mul_sum ..).symm
    _ ≤ Real.exp (θ*T)*(∑' i : ℕ, (Λ/(Λ+θ))^i) := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (Finset.range n)
        (fun i _ => pow_nonneg hr0 i)) (Real.exp_pos _).le
    _ = _ := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      have hsum : Λ+θ ≠ 0 := by positivity
      field_simp [hθ.ne']
      ring
end Kernel
end
end HybridCTMC
