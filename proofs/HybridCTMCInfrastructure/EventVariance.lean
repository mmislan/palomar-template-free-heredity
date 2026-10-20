module

public import proofs.HybridCTMCInfrastructure.EventMartingale
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

/-! Square integrability and second-moment identities for the actual timed
event martingale. These are event-index statements, before horizon stopping. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

section General
variable {W : Type*} [m0 : MeasurableSpace W] {μ : Measure W} [IsFiniteMeasure μ]

theorem integral_mul_zero_of_condExp_zero {m : MeasurableSpace W} (hm : m ≤ m0) {a d : W → ℝ}
    (ha : StronglyMeasurable[m] a) (ha2 : MemLp a 2 μ) (hd2 : MemLp d 2 μ)
    (hd : μ[d | m] =ᵐ[μ] 0) : ∫ w, a w*d w ∂μ = 0 := by
  have had : Integrable (a*d) μ := memLp_one_iff_integrable.mp (ha2.mul hd2)
  have hp := condExp_mul_of_stronglyMeasurable_left ha had (hd2.integrable one_le_two)
  change (∫ w, (a*d) w ∂μ) = 0
  rw [← integral_condExp hm (f := a*d)]
  calc
    _ = ∫ w, (0 : ℝ) ∂μ := integral_congr_ae (hp.trans (by
      filter_upwards [hd] with w hw
      simp only [Pi.mul_apply, hw, Pi.zero_apply, mul_zero]))
    _ = 0 := integral_zero W ℝ

theorem integral_square_add_of_condExp_zero {m : MeasurableSpace W} (hm : m ≤ m0) {a d : W → ℝ}
    (ha : StronglyMeasurable[m] a) (ha2 : MemLp a 2 μ) (hd2 : MemLp d 2 μ)
    (hd : μ[d | m] =ᵐ[μ] 0) :
    ∫ w, (a w+d w)^2 ∂μ = (∫ w, (a w)^2 ∂μ)+(∫ w, (d w)^2 ∂μ) := by
  have had : Integrable (fun w => a w*d w) μ := by
    have hmul : Integrable (a*d) μ := memLp_one_iff_integrable.mp (ha2.mul hd2)
    exact hmul.congr (Filter.Eventually.of_forall (fun _ => rfl))
  have he : (fun w => (a w+d w)^2) = fun w => (a w)^2+2*(a w*d w)+(d w)^2 := by
    funext w
    ring
  rw [he, integral_add (f := fun w => (a w)^2+2*(a w*d w))
      (ha2.integrable_sq.add (had.const_mul 2)) hd2.integrable_sq,
    integral_add ha2.integrable_sq (had.const_mul 2), integral_const_mul,
    integral_mul_zero_of_condExp_zero (m0 := m0) hm ha ha2 hd2 hd]
  ring

theorem square_submartingale {F : ℕ → W → ℝ} {ℱ : Filtration ℕ m0}
    (hF : Martingale F ℱ μ) (h2 : ∀ n, MemLp (F n) 2 μ) :
    Submartingale (fun n w => (F n w)^2) ℱ μ := by
  apply submartingale_nat (fun n => (hF.stronglyMeasurable n).pow 2)
    (fun n => (h2 n).integrable_sq)
  intro n
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le n) (h2 (n+1))
  have hn : 0 ≤ᵐ[μ] Var[F (n+1); μ | ℱ n] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun w => sq_nonneg _))
  filter_upwards [hv, hn, hF.condExp_ae_eq (Nat.le_succ n)] with w hvw hnw hew
  dsimp at hvw hnw ⊢
  rw [hew] at hvw
  linarith

theorem martingale_maximal_square_bound {F : ℕ → W → ℝ}
    {ℱ : Filtration ℕ m0} (hF : Martingale F ℱ μ)
    (h2 : ∀ n, MemLp (F n) 2 μ) (n : ℕ) {b B : ℝ} (hb : 0 < b)
    (hB : ∫ w, (F n w)^2 ∂μ ≤ B) :
    μ {w | ∃ k ≤ n, b ≤ |F k w|} ≤ ENNReal.ofReal (B/b^2) := by
  let A := {w | b^2 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
    (fun k => (F k w)^2)}
  have hs := square_submartingale hF h2
  have hd := maximal_ineq hs (fun k w => sq_nonneg (F k w))
    (ε := ⟨b^2, sq_nonneg b⟩) n
  have hnonneg : 0 ≤ ∫ w in A, (F n w)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hi : ∫ w in A, (F n w)^2 ∂μ ≤ B :=
    (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (h2 n).integrable_sq).trans hB
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  simp only [ENNReal.toReal_mul] at hdreal
  change b^2*(μ A).toReal ≤ ENNReal.toReal (ENNReal.ofReal (∫ w in A, (F n w)^2 ∂μ)) at hdreal
  rw [ENNReal.toReal_ofReal hnonneg] at hdreal
  have hm : μ A ≤ ENNReal.ofReal (B/b^2) := by
    rw [ENNReal.le_ofReal_iff_toReal_le]
    · apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
      nlinarith [hdreal]
    · exact measure_ne_top _ _
    · exact div_nonneg (hnonneg.trans hi) (sq_nonneg b)
  refine (measure_mono ?_).trans hm
  rintro w ⟨k, hk, hkb⟩
  change b^2 ≤ _
  rw [Finset.le_sup'_iff]
  refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
  have hh := (sq_le_sq₀ hb.le (abs_nonneg (F k w))).mpr hkb
  simpa only [sq_abs] using hh
end General

namespace Kernel
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem memLp_eventIncrement (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (n : ℕ) :
    MemLp (K.eventIncrement Λ f n) 2 (K.eventLaw Λ hΛ x) :=
  (memLp_two_iff_integrable_sq (K.integrable_eventIncrement hΛ f x n).aestronglyMeasurable).mpr
    (K.integrable_eventIncrement_square hΛ f x n)

theorem memLp_eventCompensator (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (n : ℕ) :
    MemLp (K.eventCompensator Λ f n) 2 (K.eventLaw Λ hΛ x) :=
  memLp_finsetSum _ (fun i _ => K.memLp_eventIncrement hΛ f x i)

theorem integral_eventCompensator_square_succ (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (n : ℕ) :
    ∫ w, (K.eventCompensator Λ f (n+1) w)^2 ∂K.eventLaw Λ hΛ x =
      (∫ w, (K.eventCompensator Λ f n w)^2 ∂K.eventLaw Λ hΛ x)+
      (∫ w, (K.eventIncrement Λ f n w)^2 ∂K.eventLaw Λ hΛ x) := by
  have he : K.eventCompensator Λ f (n+1) =
      fun w => K.eventCompensator Λ f n w+K.eventIncrement Λ f n w := by
    funext w
    simp [eventCompensator, Finset.sum_range_succ]
  rw [he]
  exact integral_square_add_of_condExp_zero (Filtration.piLE.le n)
    (K.stronglyAdapted_eventCompensator Λ f n) (K.memLp_eventCompensator hΛ f x n)
    (K.memLp_eventIncrement hΛ f x n) (K.condExp_eventIncrement hΛ f x n)

theorem submartingale_eventCompensator_square (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) :
    Submartingale (fun n w => (K.eventCompensator Λ f n w)^2) Filtration.piLE
      (K.eventLaw Λ hΛ x) :=
  square_submartingale (K.martingale_eventCompensator hΛ f x) (K.memLp_eventCompensator hΛ f x)
end Kernel
end
end HybridCTMC
