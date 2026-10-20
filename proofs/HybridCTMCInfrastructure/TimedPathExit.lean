module

public import proofs.HybridCTMCInfrastructure.TimedHistoryLaw
public import proofs.HybridCTMCInfrastructure.PathExit

@[expose] public section

/-! Exact transfer of finite visited-history exits to the timed path. -/
namespace HybridCTMC
open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section
namespace Kernel
variable {S : Type*}

theorem clockIndex_mono_before (w : ℕ → ℝ × S) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) (hex : ∃ n, T < arrivalTime n w) :
    clockIndex t w ≤ clockIndex T w := by
  have hT := clockIndex_segment (ht.trans htT) w hex
  obtain ⟨m, hm⟩ := hex
  have hs := clockIndex_segment ht w ⟨m, htT.trans_lt hm⟩
  by_contra hn
  have hh := (arrivalTime_mono w) (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
  exact (not_lt_of_ge ((hh.trans hs.1).trans htT)) hT.2

theorem timedHistory_exited_iff (safe : S → Prop) (w : ℕ → ℝ × S) {T : ℝ}
    (hT : 0 ≤ T) (hex : ∃ n, T < arrivalTime n w)
    (hpos : ∀ n : ℕ, 0 < (w (n+1)).1) :
    exited safe (timedHistory T w) ↔
      ∃ t, 0 ≤ t ∧ t ≤ T ∧ ¬safe (timedState t w) := by
  constructor
  · rintro ⟨s, hs, hbad⟩
    obtain ⟨i, hi, his⟩ := (mem_statePrefix (clockIndex T w) w s).mp hs
    have hnext : arrivalTime i w < arrivalTime (i+1) w := by
      simp only [arrivalTime, Finset.sum_range_succ]
      exact lt_add_of_pos_right _ (lt_max_of_lt_right (hpos i))
    have hind := clockIndex_eq_of_between w i le_rfl hnext
    refine ⟨arrivalTime i w, arrivalTime_nonneg i w,
      ((arrivalTime_mono w) hi).trans (clockIndex_segment hT w hex).1, ?_⟩
    simpa only [timedState, hind, his] using hbad
  · rintro ⟨t, ht, htT, hbad⟩
    refine ⟨timedState t w, ?_, hbad⟩
    exact (mem_statePrefix (clockIndex T w) w _).mpr
      ⟨clockIndex t w, clockIndex_mono_before w ht htT hex, rfl⟩

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem timedPath_exit_mass (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (safe : S → Prop) :
    K.eventLaw Λ hΛ x {w | ∃ t, 0 ≤ t ∧ t ≤ T ∧ ¬safe (timedState t w)} =
      mass (K.poissonTrajectory ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x) (exited safe) := by
  have hh := K.timedHistory_event hΛ hT x (exited safe)
  have hd : (fun a => Classical.propDecidable (exited safe a)) =
      (inferInstance : DecidablePred (exited safe)) := Subsingleton.elim _ _
  rw [hd] at hh
  apply Eq.trans _ hh
  apply measure_congr
  filter_upwards [K.ae_arrival_crosses hΛ x T, K.ae_holding_pos hΛ x] with w hw hp
  exact propext (timedHistory_exited_iff safe w hT hw hp).symm

end Kernel

namespace Rates
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem timedPath_exit_bound (q : Rates S) (safe : S → Prop)
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) {Λ c b T : ℝ}
    (hΛ : 0 < Λ) (hc : 0 ≤ c) (hb : 0 < b) (hT : 0 ≤ T)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ c)
    (barrier : ∀ x, ¬safe x → b ≤ f x) (x : S) :
    (q.uniformize Λ hΛ bound).eventLaw Λ hΛ x
      {w | ∃ t, 0 ≤ t ∧ t ≤ T ∧ ¬safe (Kernel.timedState t w)} ≤
      ENNReal.ofReal ((f x+c*T)/b) := by
  rw [Kernel.timedPath_exit_mass _ hΛ hT x safe]
  exact q.poissonTrajectory_exit_bound safe f hf hΛ hc hb hT bound drift barrier x

end Rates
end
end HybridCTMC
