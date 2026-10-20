module

public import proofs.HybridCTMCInfrastructure.ClockSupport
public import proofs.HybridCTMCInfrastructure.ClockInitial

@[expose] public section

/-! Invariants derived from positive-weight support of the actual timed path law. -/
namespace HybridCTMC

open MeasureTheory ProbabilityTheory Set

noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

namespace Kernel

theorem ae_pmf_relation (K : HybridCTMC.Kernel S) (R : S → S → Prop)
    (hR : ∀ s y, 0 < K.weight s y → R s y) (s : S) :
    ∀ᵐ y ∂(K.pmf s).toMeasure, R s y := by
  rw [ae_iff, (K.pmf s).toMeasure_apply_eq_zero_iff
    (Set.to_countable _).measurableSet]
  apply Set.disjoint_left.mpr
  intro y hy hbad
  have hwy : 0 < K.weight s y := by
    simpa only [PMF.mem_support_iff, pmf, PMF.ofFintype_apply,
      ne_eq, ENNReal.ofReal_eq_zero, not_le] using hy
  exact hbad (hR s y hwy)

theorem ae_event_relation (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (R : S → S → Prop)
    (hR : ∀ s y, 0 < K.weight s y → R s y) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x,
      ∀ n : ℕ, R (w n).2 (w (n+1)).2 := by
  rw [ae_all_iff]
  intro n
  have hm : MeasurableSet {z : S × S | R z.1 z.2} :=
    (Set.to_countable _).measurableSet
  have hp : MeasurableSet {z : S × (ℝ × S) | R z.1 z.2.2} :=
    hm.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply K.eventLaw_ae hΛ x n (fun s z => R s z.2) hp
  intro s
  let := isProbabilityMeasure_expMeasure hΛ
  have hms : MeasurableSet {z : ℝ × S | R s z.2} :=
    ((Set.to_countable _).measurableSet).preimage measurable_snd
  apply (Measure.ae_prod_iff_ae_ae hms).mpr
  exact Filter.Eventually.of_forall (fun _ => K.ae_pmf_relation R hR s)

theorem ae_event_invariant (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (safe : S → Prop)
    (hx : safe x)
    (hstep : ∀ s y, safe s → 0 < K.weight s y → safe y) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ n : ℕ, safe (w n).2 := by
  have hr := K.ae_event_relation hΛ x (fun s y => safe s → safe y)
    (fun s y hy hs => hstep s y hs hy)
  filter_upwards [K.ae_event_initial hΛ x, hr] with w h0 hw
  intro n
  induction n with
  | zero => simpa [h0] using hx
  | succ n ih => exact hw n ih

end Kernel
end
end HybridCTMC
