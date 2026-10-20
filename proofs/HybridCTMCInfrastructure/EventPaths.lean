module

public import proofs.HybridCTMCInfrastructure.ClockStep
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

@[expose] public section

/-! A probability law on infinite sequences of holding times and states.
Index zero records the deterministic initial state with time zero. Each later
coordinate is sampled from the independent exponential/transition product. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

namespace Kernel
def clockKernel (K : HybridCTMC.Kernel S) (Λ : ℝ) : ProbabilityTheory.Kernel S (ℝ × S) where
  toFun := K.clockStep Λ
  measurable' := measurable_of_countable _

theorem clockKernel_markov (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) :
    IsMarkovKernel (K.clockKernel Λ) where
  isProbabilityMeasure x := by
    let := isProbabilityMeasure_expMeasure hΛ
    change IsProbabilityMeasure ((expMeasure Λ).prod (K.pmf x).toMeasure)
    infer_instance

def eventKernel (K : HybridCTMC.Kernel S) (Λ : ℝ) (n : ℕ) :
    ProbabilityTheory.Kernel (Π _ : Finset.Iic n, ℝ × S) (ℝ × S) :=
  (K.clockKernel Λ).comap (fun w => (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) (by fun_prop)

theorem eventKernel_markov (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    IsMarkovKernel (K.eventKernel Λ n) := by
  let := K.clockKernel_markov hΛ
  unfold eventKernel
  infer_instance

def eventLaw (K : HybridCTMC.Kernel S) (Λ : ℝ) (hΛ : 0 < Λ) (x : S) :
    Measure (ℕ → ℝ × S) := by
  let := K.eventKernel_markov hΛ
  exact ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (0, x)) (K.eventKernel Λ)

instance eventLaw_probability (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    IsProbabilityMeasure (K.eventLaw Λ hΛ x) := by
  unfold eventLaw
  infer_instance

theorem eventLaw_joint (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) (n : ℕ) :
    (K.eventLaw Λ hΛ x).map (frestrictLe n) ⊗ₘ K.eventKernel Λ n =
      (K.eventLaw Λ hΛ x).map (fun w => (frestrictLe n w, w (n+1))) := by
  let := K.eventKernel_markov hΛ
  exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem eventLaw_condDistrib (K : HybridCTMC.Kernel S) [StandardBorelSpace S] [Nonempty S]
    {Λ : ℝ} (hΛ : 0 < Λ) (x : S) (n : ℕ) :
    condDistrib (fun w : ℕ → ℝ × S => w (n+1)) (frestrictLe n) (K.eventLaw Λ hΛ x)
      =ᵐ[(K.eventLaw Λ hΛ x).map (frestrictLe n)] K.eventKernel Λ n := by
  let : Nonempty S := ⟨x⟩
  let := K.eventKernel_markov hΛ
  exact ProbabilityTheory.Kernel.condDistrib_trajMeasure

theorem eventLaw_integrable (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (x : S) (n : ℕ) (g : S → ℝ × S → ℝ)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ s, Integrable (g s) (K.clockStep Λ s)) :
    Integrable (fun w => g (w n).2 (w (n+1))) (K.eventLaw Λ hΛ x) := by
  let := K.eventKernel_markov hΛ
  let last : (Π _ : Finset.Iic n, ℝ × S) → S :=
    fun w => (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  have hl : Measurable last := by fun_prop
  let G : (Π _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ := fun p => g (last p.1) p.2
  have hG : Measurable G := hg.comp (hl.comp measurable_fst |>.prodMk measurable_snd)
  have hnorm : Integrable (fun s => ∫ z, ‖g s z‖ ∂K.clockStep Λ s)
      (((K.eventLaw Λ hΛ x).map (frestrictLe n)).map last) := Integrable.of_finite
  have hcomp : Integrable G ((K.eventLaw Λ hΛ x).map (frestrictLe n) ⊗ₘ K.eventKernel Λ n) := by
    apply (Measure.integrable_compProd_iff hG.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun w => hi (last w)), hnorm.comp_measurable hl⟩
  rw [K.eventLaw_joint hΛ x n] at hcomp
  exact hcomp.comp_measurable (by fun_prop)

theorem eventLaw_condExp (K : HybridCTMC.Kernel S) [StandardBorelSpace S]
    {Λ : ℝ} (hΛ : 0 < Λ) (x : S) (n : ℕ) (g : S → ℝ × S → ℝ)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ s, Integrable (g s) (K.clockStep Λ s)) :
    (K.eventLaw Λ hΛ x)[fun w => g (w n).2 (w (n+1)) | Filtration.piLE n] =ᵐ[K.eventLaw Λ hΛ x]
      fun w => ∫ z, g (w n).2 z ∂K.clockStep Λ (w n).2 := by
  let : Nonempty S := ⟨x⟩
  let last : (Π _ : Finset.Iic n, ℝ × S) → S :=
    fun w => (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  have hl : Measurable last := by fun_prop
  let G : (Π _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ := fun p => g (last p.1) p.2
  have hG : Measurable G := hg.comp (hl.comp measurable_fst |>.prodMk measurable_snd)
  have he := condExp_prod_ae_eq_integral_condDistrib (X := frestrictLe n)
    (Y := fun w : ℕ → ℝ × S => w (n+1)) (μ := K.eventLaw Λ hΛ x)
    (f := G) (by fun_prop) (measurable_pi_apply _ |>.aemeasurable) hG.stronglyMeasurable
    (K.eventLaw_integrable hΛ x n g hg hi)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  refine he.trans ?_
  have hc := ae_of_ae_map (show AEMeasurable (frestrictLe n) (K.eventLaw Λ hΛ x) by fun_prop)
    (K.eventLaw_condDistrib hΛ x n)
  filter_upwards [hc] with w hw
  rw [hw]
  rfl
end Kernel
end
end HybridCTMC
