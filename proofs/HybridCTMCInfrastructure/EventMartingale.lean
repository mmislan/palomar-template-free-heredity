module

public import proofs.HybridCTMCInfrastructure.EventPaths
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The actual holding-time compensated sum is a martingale in the filtration
of the constructed timed event path. No martingale assumption is supplied. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

namespace Kernel
theorem measurable_compensatedStep (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) :
    Measurable (fun p : S × (ℝ × S) => K.compensatedStep Λ f p.1 p.2) := by
  have hf := measurable_of_countable f
  have he := measurable_of_countable (K.expect f)
  unfold compensatedStep
  fun_prop

def eventIncrement (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (n : ℕ)
    (w : ℕ → ℝ × S) : ℝ := K.compensatedStep Λ f (w n).2 (w (n+1))

def eventCompensator (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (n : ℕ)
    (w : ℕ → ℝ × S) : ℝ := ∑ i ∈ Finset.range n, K.eventIncrement Λ f i w

theorem integrable_eventIncrement (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (n : ℕ) :
    Integrable (K.eventIncrement Λ f n) (K.eventLaw Λ hΛ x) :=
  K.eventLaw_integrable hΛ x n (K.compensatedStep Λ f)
    (K.measurable_compensatedStep Λ f) (K.integrable_compensatedStep hΛ f)

theorem integrable_eventIncrement_square (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (n : ℕ) :
    Integrable (fun w => (K.eventIncrement Λ f n w)^2) (K.eventLaw Λ hΛ x) :=
  K.eventLaw_integrable hΛ x n (fun s z => (K.compensatedStep Λ f s z)^2)
    ((K.measurable_compensatedStep Λ f).pow_const 2) (K.integrable_compensatedStep_square hΛ f)

theorem condExp_eventIncrement (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (n : ℕ) :
    (K.eventLaw Λ hΛ x)[K.eventIncrement Λ f n | Filtration.piLE n] =ᵐ[K.eventLaw Λ hΛ x] 0 := by
  refine (K.eventLaw_condExp hΛ x n (K.compensatedStep Λ f)
    (K.measurable_compensatedStep Λ f) (K.integrable_compensatedStep hΛ f)).trans ?_
  exact Filter.Eventually.of_forall (fun w => K.integral_compensatedStep hΛ f (w n).2)

theorem condExp_eventIncrement_square (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) (n : ℕ) :
    (K.eventLaw Λ hΛ x)[fun w => (K.eventIncrement Λ f n w)^2 | Filtration.piLE n]
      =ᵐ[K.eventLaw Λ hΛ x] fun w => K.expect (fun y => (f y-f (w n).2)^2) (w n).2 := by
  refine (K.eventLaw_condExp hΛ x n (fun s z => (K.compensatedStep Λ f s z)^2)
    ((K.measurable_compensatedStep Λ f).pow_const 2)
    (K.integrable_compensatedStep_square hΛ f)).trans ?_
  exact Filter.Eventually.of_forall (fun w => K.integral_compensatedStep_square hΛ f (w n).2)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_event_eval {i n : ℕ} (hi : i ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => ℝ × S) n] (fun w => w i) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S) ⟨i, Finset.mem_Iic.mpr hi⟩).comp
    (comap_measurable (frestrictLe (π := fun _ : ℕ => ℝ × S) n))

theorem stronglyAdapted_eventCompensator (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) :
    StronglyAdapted Filtration.piLE (K.eventCompensator Λ f) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact (K.measurable_compensatedStep Λ f).comp
    ((measurable_event_eval (Nat.le_of_lt hi')).snd.prodMk
      (measurable_event_eval (Nat.succ_le_of_lt hi')))

theorem integrable_eventCompensator (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (n : ℕ) :
    Integrable (K.eventCompensator Λ f n) (K.eventLaw Λ hΛ x) := by
  exact integrable_finsetSum _ (fun i _ => K.integrable_eventIncrement hΛ f x i)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem eventCompensator_succ_sub (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (n : ℕ) :
    K.eventCompensator Λ f (n+1)-K.eventCompensator Λ f n = K.eventIncrement Λ f n := by
  funext w
  simp [eventCompensator, Finset.sum_range_succ]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem eventCompensator_telescopes (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (n : ℕ) (w : ℕ → ℝ × S) :
    K.eventCompensator Λ f n w = f (w n).2-f (w 0).2-
      ∑ i ∈ Finset.range n, Λ*(K.expect f (w i).2-f (w i).2)*(w (i+1)).1 := by
  induction n with
  | zero => simp [eventCompensator]
  | succ n ih =>
    have hs : K.eventCompensator Λ f (n+1) w =
        K.eventCompensator Λ f n w+K.eventIncrement Λ f n w := by
      simp [eventCompensator, Finset.sum_range_succ]
    rw [hs, ih, Finset.sum_range_succ]
    unfold eventIncrement compensatedStep
    ring

theorem martingale_eventCompensator (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (f : S → ℝ) (x : S) :
    Martingale (K.eventCompensator Λ f) Filtration.piLE (K.eventLaw Λ hΛ x) := by
  apply martingale_of_condExp_sub_eq_zero_nat (K.stronglyAdapted_eventCompensator Λ f)
    (K.integrable_eventCompensator hΛ f x)
  intro n
  rw [eventCompensator_succ_sub]
  exact K.condExp_eventIncrement hΛ f x n
end Kernel
end
end HybridCTMC
