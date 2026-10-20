module

public import proofs.HybridCTMCInfrastructure.EventArrival
public import proofs.HybridCTMCInfrastructure.Channels

@[expose] public section

/-! Support properties of the constructed timed path, including deterministic
jump caps derived from positive finite-kernel weights. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators Classical
noncomputable section
namespace Kernel
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem eventLaw_ae (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (x : S) (n : ℕ) (p : S → ℝ × S → Prop)
    (hp : MeasurableSet {z : S × (ℝ × S) | p z.1 z.2})
    (hi : ∀ s, ∀ᵐ z ∂K.clockStep Λ s, p s z) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, p (w n).2 (w (n+1)) := by
  let := K.eventKernel_markov hΛ
  let last : (Π _ : Finset.Iic n, ℝ × S) → S :=
    fun w => (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  have hl : Measurable last := by fun_prop
  have hc : ∀ᵐ z ∂((K.eventLaw Λ hΛ x).map (frestrictLe n) ⊗ₘ K.eventKernel Λ n),
      p (last z.1) z.2 := Measure.ae_compProd_of_ae_ae
    ((hl.comp measurable_fst |>.prodMk measurable_snd) hp)
    (Filter.Eventually.of_forall (fun w => hi (last w)))
  rw [K.eventLaw_joint hΛ x n] at hc
  exact ae_of_ae_map (by fun_prop) hc

theorem ae_holding_nonneg (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ n : ℕ, 0 ≤ (w (n+1)).1 := by
  rw [ae_all_iff]
  intro n
  apply K.eventLaw_ae hΛ x n (fun _ z => 0 ≤ z.1)
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))
  intro s
  let := isProbabilityMeasure_expMeasure hΛ
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_fst)).mpr
  filter_upwards [HoldingTime.ae_nonneg Λ] with t ht
  exact Filter.Eventually.of_forall (fun _ => ht)

theorem ae_pmf_jump (K : HybridCTMC.Kernel S) (f : S → ℝ) {J : ℝ}
    (hj : ∀ s y, 0 < K.weight s y → |f y-f s| ≤ J) (s : S) :
    ∀ᵐ y ∂(K.pmf s).toMeasure, |f y-f s| ≤ J := by
  rw [ae_iff, (K.pmf s).toMeasure_apply_eq_zero_iff (Set.to_countable _).measurableSet]
  apply Set.disjoint_left.mpr
  intro y hy hbad
  have hy' : 0 < K.weight s y := by
    simpa only [PMF.mem_support_iff, pmf, PMF.ofFintype_apply, ne_eq,
      ENNReal.ofReal_eq_zero, not_le] using hy
  exact hbad (hj s y hy')

theorem ae_event_jump (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) {J : ℝ}
    (hj : ∀ s y, 0 < K.weight s y → |f y-f s| ≤ J) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ n : ℕ, |f (w (n+1)).2-f (w n).2| ≤ J := by
  rw [ae_all_iff]
  intro n
  have hf := measurable_of_countable f
  apply K.eventLaw_ae hΛ x n (fun s z => |f z.2-f s| ≤ J)
    (measurableSet_le ((hf.comp (measurable_snd.comp measurable_snd)).sub
      (hf.comp measurable_fst)).norm measurable_const)
  intro s
  let := isProbabilityMeasure_expMeasure hΛ
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le ((hf.comp measurable_snd).sub measurable_const).norm measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun _ => K.ae_pmf_jump f hj s)
end Kernel

namespace Channels
variable {S R : Type*} [Fintype S] [Fintype R] [DecidableEq S]

theorem uniformize_jump_bound (ch : Channels S R) {Λ J : ℝ} (hΛ : 0 < Λ) (hJ : 0 ≤ J)
    (bound : ∀ s, ∑ y, ch.rates.rate s y ≤ Λ) (f : S → ℝ)
    (hj : ∀ s r, |f (ch.next s r)-f s| ≤ J) (s y : S)
    (hpos : 0 < (ch.rates.uniformize Λ hΛ bound).weight s y) : |f y-f s| ≤ J := by
  by_cases he : y = s
  · subst y
    simpa using hJ
  · have hrate : 0 < ch.rates.rate s y := by
      simpa only [Rates.uniformize, ite_eq_right he, zero_add, div_pos_iff_of_pos_right hΛ] using hpos
    change 0 < ∑ r, if ch.next s r = y then ch.propensity s r else 0 at hrate
    have hex : ∃ r, 0 < (if ch.next s r = y then ch.propensity s r else 0) := by
      by_contra hn
      push Not at hn
      exact (not_le_of_gt hrate) (Finset.sum_nonpos (fun r _ => hn r))
    obtain ⟨r, hr⟩ := hex
    by_cases hr' : ch.next s r = y
    · simpa only [hr'] using hj s r
    · simp only [ite_eq_right hr', lt_self_iff_false] at hr
end Channels
end
end HybridCTMC
