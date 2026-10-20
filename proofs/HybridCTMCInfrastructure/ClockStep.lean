module

public import proofs.HybridCTMCInfrastructure.FiniteKernel
public import proofs.HybridCTMCInfrastructure.HoldingTime
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Independent exponential holding time and finite transition. The compensated
increment's first and second moments are derived as actual product integrals. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

namespace Kernel
theorem integral_pmf (K : HybridCTMC.Kernel S) (f : S → ℝ) (x : S) :
    ∫ y, f y ∂(K.pmf x).toMeasure = K.expect f x := by
  rw [PMF.integral_eq_sum]
  simp only [pmf, PMF.ofFintype_apply, ENNReal.toReal_ofReal (K.nonneg x _), smul_eq_mul, expect]

def clockStep (K : HybridCTMC.Kernel S) (Λ : ℝ) (x : S) : Measure (ℝ × S) :=
  (expMeasure Λ).prod (K.pmf x).toMeasure

def compensatedStep (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (x : S)
    (z : ℝ × S) : ℝ := f z.2-f x-Λ*(K.expect f x-f x)*z.1

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem expect_difference (K : HybridCTMC.Kernel S) (f : S → ℝ) (x : S) :
    K.expect (fun y => f y-f x) x = K.expect f x-f x := by
  simp [expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, K.total]

theorem integrable_compensatedStep (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) : Integrable (K.compensatedStep Λ f x) (K.clockStep Λ x) := by
  let := isProbabilityMeasure_expMeasure hΛ
  have hf : Integrable (fun y => f y-f x) (K.pmf x).toMeasure := Integrable.of_finite
  have ht : Integrable (fun t : ℝ => t) (expMeasure Λ) := by
    simpa using HoldingTime.integrable_pow hΛ 1
  exact (hf.comp_snd _).sub ((ht.comp_fst _).const_mul (Λ*(K.expect f x-f x)))

theorem integral_compensatedStep (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) : ∫ z, K.compensatedStep Λ f x z ∂K.clockStep Λ x = 0 := by
  let := isProbabilityMeasure_expMeasure hΛ
  have hf : Integrable (fun y => f y-f x) (K.pmf x).toMeasure := Integrable.of_finite
  have ht : Integrable (fun t : ℝ => t) (expMeasure Λ) := by
    simpa using HoldingTime.integrable_pow hΛ 1
  unfold compensatedStep clockStep
  rw [integral_sub (hf.comp_snd _) ((ht.comp_fst _).const_mul (Λ*(K.expect f x-f x))),
    integral_fun_snd (fun y => f y-f x), integral_const_mul,
    integral_fun_fst (fun t : ℝ => t), integral_pmf, HoldingTime.integral_id hΛ]
  simp only [probReal_univ, one_smul]
  rw [expect_difference]
  field_simp
  ring

theorem integrable_compensatedStep_square (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) :
    Integrable (fun z => (K.compensatedStep Λ f x z)^2) (K.clockStep Λ x) := by
  let := isProbabilityMeasure_expMeasure hΛ
  let d := Λ*(K.expect f x-f x)
  have hf : Integrable (fun y => f y-f x) (K.pmf x).toMeasure := Integrable.of_finite
  have hf2 : Integrable (fun y => (f y-f x)^2) (K.pmf x).toMeasure := Integrable.of_finite
  have ht : Integrable (fun t : ℝ => t) (expMeasure Λ) := by
    simpa using HoldingTime.integrable_pow hΛ 1
  have ht2 := HoldingTime.integrable_pow hΛ 2
  have he : (fun z => (K.compensatedStep Λ f x z)^2) =
      fun z : ℝ × S => (f z.2-f x)^2 - (2*d)*(z.1*(f z.2-f x)) + d^2*z.1^2 := by
    funext z
    dsimp [compensatedStep, d]
    ring
  rw [he]
  exact ((hf2.comp_snd _).sub ((ht.mul_prod hf).const_mul (2*d))).add
    ((ht2.comp_fst _).const_mul (d^2))

theorem integral_compensatedStep_square (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) :
    ∫ z, (K.compensatedStep Λ f x z)^2 ∂K.clockStep Λ x =
      K.expect (fun y => (f y-f x)^2) x := by
  let := isProbabilityMeasure_expMeasure hΛ
  let d := Λ*(K.expect f x-f x)
  have hf : Integrable (fun y => f y-f x) (K.pmf x).toMeasure := Integrable.of_finite
  have hf2 : Integrable (fun y => (f y-f x)^2) (K.pmf x).toMeasure := Integrable.of_finite
  have ht : Integrable (fun t : ℝ => t) (expMeasure Λ) := by
    simpa using HoldingTime.integrable_pow hΛ 1
  have ht2 := HoldingTime.integrable_pow hΛ 2
  have he : (fun z => (K.compensatedStep Λ f x z)^2) =
      fun z : ℝ × S => (f z.2-f x)^2 - (2*d)*(z.1*(f z.2-f x)) + d^2*z.1^2 := by
    funext z
    dsimp [compensatedStep, d]
    ring
  rw [he]
  change (∫ z, (f z.2-f x)^2-(2*d)*(z.1*(f z.2-f x))+d^2*z.1^2
    ∂(expMeasure Λ).prod (K.pmf x).toMeasure) = _
  rw [integral_add (f := fun z : ℝ × S => (f z.2-f x)^2-(2*d)*(z.1*(f z.2-f x)))
      ((hf2.comp_snd _).sub ((ht.mul_prod hf).const_mul (2*d)))
      ((ht2.comp_fst _).const_mul (d^2)),
    integral_sub (hf2.comp_snd _) ((ht.mul_prod hf).const_mul (2*d)),
    integral_fun_snd (fun y => (f y-f x)^2), integral_const_mul,
    integral_prod_mul (fun t : ℝ => t) (fun y => f y-f x),
    integral_const_mul, integral_fun_fst (fun t : ℝ => t^2)]
  simp only [probReal_univ, one_smul, integral_pmf,
    HoldingTime.integral_id hΛ, HoldingTime.integral_square hΛ, expect_difference]
  dsimp [d]
  field_simp
  ring
end Kernel

namespace Rates
variable [DecidableEq S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem compensated_uniformize (q : Rates S) {Λ : ℝ} (hΛ : 0 < Λ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) (f : S → ℝ) (x : S) (z : ℝ × S) :
    (q.uniformize Λ hΛ bound).compensatedStep Λ f x z =
      f z.2-f x-q.generator f x*z.1 := by
  rw [Kernel.compensatedStep, uniformize_expect]
  field_simp
  ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem square_increment_uniformize (q : Rates S) {Λ : ℝ} (hΛ : 0 < Λ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) (f : S → ℝ) (x : S) :
    (q.uniformize Λ hΛ bound).expect (fun y => (f y-f x)^2) x =
      (q.generator (fun y => (f y)^2) x-2*f x*q.generator f x)/Λ := by
  rw [uniformize_expect]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  congr 1
  simp only [generator, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem integral_compensated_uniformize_square (q : Rates S) {Λ : ℝ} (hΛ : 0 < Λ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) (f : S → ℝ) (x : S) :
    ∫ z, (f z.2-f x-q.generator f x*z.1)^2
      ∂(q.uniformize Λ hΛ bound).clockStep Λ x =
      (q.generator (fun y => (f y)^2) x-2*f x*q.generator f x)/Λ := by
  simp_rw [← q.compensated_uniformize hΛ bound f x]
  rw [Kernel.integral_compensatedStep_square _ hΛ, square_increment_uniformize]
end Rates
end
end HybridCTMC
