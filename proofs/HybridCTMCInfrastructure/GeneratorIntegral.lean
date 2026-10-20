module

public import proofs.HybridCTMCInfrastructure.TimedProcess
public import proofs.HybridCTMCInfrastructure.ClockInitial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! The accumulated holding-time drift is the ordinary time integral along
the actual piecewise constant state path. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
noncomputable section
namespace Kernel
variable {S : Type*}

theorem clockIndex_eq_of_between (w : ℕ → ℝ × S) (i : ℕ) {t : ℝ}
    (hlo : arrivalTime i w ≤ t) (hhi : t < arrivalTime (i+1) w) : clockIndex t w = i := by
  have hex : ∃ n, t < arrivalTime n w := ⟨i+1, hhi⟩
  have hf : Nat.find hex = i+1 := (Nat.find_eq_iff hex).mpr ⟨hhi, fun n hn =>
    not_lt_of_ge (((arrivalTime_mono w) (Nat.lt_succ_iff.mp hn)).trans hlo)⟩
  rw [clockIndex, dite_eq_left hex, hf]
  omega

theorem ae_timedState_segment (g : S → ℝ) (w : ℕ → ℝ × S) (i : ℕ) {b : ℝ}
    (hab : arrivalTime i w ≤ b) (hb : b ≤ arrivalTime (i+1) w) :
    (fun t => g (timedState t w)) =ᵐ[volume.restrict (Set.uIoc (arrivalTime i w) b)]
      fun _ => g (w i).2 := by
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [volume.ae_ne (arrivalTime (i+1) w)] with t ht
  intro hmem
  rw [uIoc_of_le hab] at hmem
  have hind := clockIndex_eq_of_between w i hmem.1.le (lt_of_le_of_ne (hmem.2.trans hb) ht)
  simp only [timedState, hind]

theorem intervalIntegrable_timedState_segment (g : S → ℝ) (w : ℕ → ℝ × S) (i : ℕ) {b : ℝ}
    (hab : arrivalTime i w ≤ b) (hb : b ≤ arrivalTime (i+1) w) :
    IntervalIntegrable (fun t => g (timedState t w)) volume (arrivalTime i w) b :=
  (intervalIntegrable_congr_ae (ae_timedState_segment g w i hab hb)).mpr intervalIntegrable_const

theorem integral_timedState_segment (g : S → ℝ) (w : ℕ → ℝ × S) (i : ℕ) {b : ℝ}
    (hab : arrivalTime i w ≤ b) (hb : b ≤ arrivalTime (i+1) w) :
    ∫ t in (arrivalTime i w)..b, g (timedState t w) = (b-arrivalTime i w)*g (w i).2 := by
  rw [intervalIntegral.integral_congr_ae_restrict (ae_timedState_segment g w i hab hb),
    intervalIntegral.integral_const, smul_eq_mul]

theorem integral_timedState_arrival (g : S → ℝ) (w : ℕ → ℝ × S) (n : ℕ) :
    ∫ t in (0:ℝ)..(arrivalTime n w), g (timedState t w) =
      ∑ i ∈ Finset.range n, max 0 (w (i+1)).1*g (w i).2 := by
  have hi (i : ℕ) : IntervalIntegrable (fun t => g (timedState t w)) volume
      (arrivalTime i w) (arrivalTime (i+1) w) :=
    intervalIntegrable_timedState_segment g w i ((arrivalTime_mono w) (Nat.le_succ i)) le_rfl
  have he := intervalIntegral.sum_integral_adjacent_intervals (n := n) (fun i _ => hi i)
  have hz : arrivalTime 0 w = 0 := by simp [arrivalTime]
  rw [hz] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_timedState_segment g w i ((arrivalTime_mono w) (Nat.le_succ i)) le_rfl]
  simp [arrivalTime, Finset.sum_range_succ]

theorem intervalIntegrable_timedState (g : S → ℝ) (w : ℕ → ℝ × S) {t : ℝ} (ht : 0 ≤ t)
    (hex : ∃ n, t < arrivalTime n w) :
    IntervalIntegrable (fun u => g (timedState u w)) volume 0 t := by
  have hs := clockIndex_segment ht w hex
  have hi := IntervalIntegrable.trans_iterate (a := fun i => arrivalTime i w) (n := clockIndex t w)
    (fun i _ => intervalIntegrable_timedState_segment g w i
      ((arrivalTime_mono w) (Nat.le_succ i)) le_rfl)
  have hi0 : IntervalIntegrable (fun u => g (timedState u w)) volume 0
      (arrivalTime (clockIndex t w) w) := by simpa [arrivalTime] using hi
  exact hi0.trans (intervalIntegrable_timedState_segment g w (clockIndex t w) hs.1 hs.2.le)

theorem integral_timedState (g : S → ℝ) (w : ℕ → ℝ × S) {t : ℝ} (ht : 0 ≤ t)
    (hex : ∃ n, t < arrivalTime n w) :
    ∫ u in (0:ℝ)..t, g (timedState u w) =
      (∑ i ∈ Finset.range (clockIndex t w), max 0 (w (i+1)).1*g (w i).2)+
        (t-arrivalTime (clockIndex t w) w)*g (timedState t w) := by
  have hs := clockIndex_segment ht w hex
  have hi := IntervalIntegrable.trans_iterate (a := fun i => arrivalTime i w) (n := clockIndex t w)
    (fun i _ => intervalIntegrable_timedState_segment g w i
      ((arrivalTime_mono w) (Nat.le_succ i)) le_rfl)
  have hi0 : IntervalIntegrable (fun u => g (timedState u w)) volume 0
      (arrivalTime (clockIndex t w) w) := by simpa [arrivalTime] using hi
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0
    (intervalIntegrable_timedState_segment g w (clockIndex t w) hs.1 hs.2.le),
    integral_timedState_arrival, integral_timedState_segment g w (clockIndex t w) hs.1 hs.2.le]
  rfl

variable [Fintype S]

theorem timed_coordinate_identity (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (w : ℕ → ℝ × S) {t : ℝ} (ht : 0 ≤ t) (hex : ∃ n, t < arrivalTime n w)
    (hH : ∀ n : ℕ, 0 ≤ (w (n+1)).1) :
    f (timedState t w)-f (w 0).2 =
      (∫ u in (0:ℝ)..t, Λ*(K.expect f (timedState u w)-f (timedState u w)))+
        K.timedCompensated Λ f t w := by
  rw [integral_timedState (fun s => Λ*(K.expect f s-f s)) w ht hex,
    timedCompensated, eventCompensator_telescopes]
  simp_rw [max_eq_right (hH _)]
  have he : (∑ i ∈ Finset.range (clockIndex t w), (w (i+1)).1*
      (Λ*(K.expect f (w i).2-f (w i).2))) =
      ∑ i ∈ Finset.range (clockIndex t w), Λ*(K.expect f (w i).2-f (w i).2)*(w (i+1)).1 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  dsimp [timedState]
  ring

variable [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

omit [StandardBorelSpace S] in
theorem ae_timed_initial (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, timedState 0 w = x := by
  filter_upwards [K.ae_event_initial hΛ x, K.ae_holding_pos hΛ x] with w hw hH
  have h1 : 0 < arrivalTime 1 w := by
    simpa [arrivalTime, max_eq_right (hH 0).le] using hH 0
  have hi := clockIndex_eq_of_between w 0 (by simp [arrivalTime]) h1
  simp only [timedState, hi, hw]

theorem ae_timed_coordinate_identity (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : S → ℝ) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ t, 0 ≤ t → t ≤ T →
      f (timedState t w)-f x =
        (∫ u in (0:ℝ)..t, Λ*(K.expect f (timedState u w)-f (timedState u w)))+
          K.timedCompensated Λ f t w := by
  filter_upwards [K.ae_event_initial hΛ x, K.ae_holding_nonneg hΛ x,
    K.ae_arrival_crosses hΛ x T] with w hw hH hcross
  intro t ht htT
  obtain ⟨n, hn⟩ := hcross
  simpa only [hw] using K.timed_coordinate_identity Λ f w ht ⟨n, htT.trans_lt hn⟩ hH

theorem ae_timed_integrable (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : S → ℝ) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Λ hΛ x, ∀ t, 0 ≤ t → t ≤ T →
      IntervalIntegrable (fun u => g (timedState u w)) volume 0 t := by
  filter_upwards [K.ae_arrival_crosses hΛ x T] with w hcross
  intro t ht htT
  obtain ⟨n, hn⟩ := hcross
  exact intervalIntegrable_timedState g w ht ⟨n, htT.trans_lt hn⟩
end Kernel

namespace Rates
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S] [DecidableEq S]

theorem ae_timed_coordinate_identity (q : Rates S) {Λ : ℝ} (hΛ : 0 < Λ)
    (bound : ∀ s, ∑ y, q.rate s y ≤ Λ) (f : S → ℝ) (x : S) (T : ℝ) :
    ∀ᵐ w ∂(q.uniformize Λ hΛ bound).eventLaw Λ hΛ x, ∀ t, 0 ≤ t → t ≤ T →
      f (Kernel.timedState t w)-f x =
        (∫ u in (0:ℝ)..t, q.generator f (Kernel.timedState u w))+
          (q.uniformize Λ hΛ bound).timedCompensated Λ f t w := by
  have he (s : S) : Λ*((q.uniformize Λ hΛ bound).expect f s-f s) = q.generator f s := by
    rw [uniformize_expect]
    field_simp
    ring
  simpa only [he] using (q.uniformize Λ hΛ bound).ae_timed_coordinate_identity hΛ f x T
end Rates
end
end HybridCTMC
