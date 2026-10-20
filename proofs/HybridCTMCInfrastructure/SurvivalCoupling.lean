module

public import proofs.HybridCTMCInfrastructure.TimedPathExit
public import proofs.HybridCTMCInfrastructure.TimedEndpointTransfer

@[expose] public section

/-! Original and stopped histories agree on every no-exit reward.
This finite-history induction supplies the coupling identity rather than
assuming a coupling of the constructed continuous-time laws. -/
namespace HybridCTMC.Kernel
open MeasureTheory Set
open scoped NNReal ENNReal Classical
noncomputable section
variable {S : Type*} [Fintype S]

def survivingReward (safe : S → Prop) (ψ : List S → ℝ≥0∞) (xs : List S) : ℝ≥0∞ :=
  if exited safe xs then 0 else ψ xs

theorem trajectory_survivingReward (K : HybridCTMC.Kernel S) (safe : S → Prop)
    (n : ℕ) (x : S) (ψ : List S → ℝ≥0∞) :
    nnReward (K.trajectory n x) (survivingReward safe ψ) =
      nnReward ((K.stop safe).trajectory n x) (survivingReward safe ψ) := by
  induction n generalizing x ψ with
  | zero => rfl
  | succ n ih =>
    by_cases hx : safe x
    · simp only [trajectory, nnReward_bind, nnReward_map, stop_pmf, ite_eq_left hx]
      have he : (fun xs => survivingReward safe ψ (x::xs)) =
          survivingReward safe (fun xs => ψ (x::xs)) := by
        funext xs
        have hcons : exited safe (x::xs) ↔ exited safe xs := by
          constructor
          · rintro ⟨y, hy, hny⟩
            rcases List.mem_cons.mp hy with hxy | hyt
            · subst y
              exact (hny hx).elim
            · exact ⟨y, hyt, hny⟩
          · rintro ⟨y, hy, hny⟩
            exact ⟨y, List.mem_cons.mpr (Or.inr hy), hny⟩
        change (if exited safe (x::xs) then 0 else ψ (x::xs)) =
          if exited safe xs then 0 else ψ (x::xs)
        by_cases hex : exited safe xs
        · calc
            _ = (0 : ℝ≥0∞) := ite_eq_left (hcons.mpr hex)
            _ = _ := (ite_eq_left hex).symm
        · have hcx : ¬ exited safe (x::xs) := fun h => hex (hcons.mp h)
          calc
            _ = ψ (x::xs) := ite_eq_right hcx
            _ = _ := (ite_eq_right hex).symm
      simp only [he]
      apply congrArg (nnReward (K.pmf x))
      funext y
      exact ih y (fun xs => ψ (x::xs))
    · have he : (fun xs => survivingReward safe ψ (x::xs)) = fun _ => 0 := by
        funext xs
        simp [survivingReward, exited, hx]
      simp only [trajectory, nnReward_bind, nnReward_map, he]
      simp only [nnReward, mul_zero, tsum_zero]

theorem poissonTrajectory_survivingReward (K : HybridCTMC.Kernel S) (safe : S → Prop)
    (r : ℝ≥0) (x : S) (ψ : List S → ℝ≥0∞) :
    nnReward (K.poissonTrajectory r x) (survivingReward safe ψ) =
      nnReward ((K.stop safe).poissonTrajectory r x) (survivingReward safe ψ) := by
  simp only [poissonTrajectory, nnReward_bind]
  apply congrArg (nnReward ((ProbabilityTheory.poissonMeasure r).toPMF))
  funext n
  exact K.trajectory_survivingReward safe n x ψ

variable [MeasurableSpace S] [MeasurableSingletonClass S]

def noExit (safe : S → Prop) (T : ℝ) (w : ℕ → ℝ × S) : Prop :=
  ∀ t, 0 ≤ t → t ≤ T → safe (timedState t w)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem noExit_iff_not_exited (safe : S → Prop) (w : ℕ → ℝ × S) {T : ℝ}
    (hT : 0 ≤ T) (hex : ∃ n, T < arrivalTime n w)
    (hpos : ∀ n : ℕ, 0 < (w (n+1)).1) :
    noExit safe T w ↔ ¬exited safe (timedHistory T w) := by
  rw [timedHistory_exited_iff safe w hT hex hpos]
  simp only [noExit, not_exists, not_and, not_not]

theorem noExit_history_reward (K : HybridCTMC.Kernel S) (safe : S → Prop)
    {Λ T : ℝ} (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, if noExit safe T w then ψ (timedHistory T w) else 0 ∂K.eventLaw Λ hΛ x) =
      nnReward (K.poissonTrajectory ⟨Λ*T, mul_nonneg hΛ.le hT⟩ x)
        (survivingReward safe ψ) := by
  rw [← K.timedHistory_reward hΛ hT x (survivingReward safe ψ)]
  apply lintegral_congr_ae
  filter_upwards [K.ae_arrival_crosses hΛ x T, K.ae_holding_pos hΛ x] with w hw hp
  rw [noExit_iff_not_exited safe w hT hw hp]
  by_cases he : exited safe (timedHistory T w) <;> simp [survivingReward, he]

theorem noExit_history_coupling (K : HybridCTMC.Kernel S) (safe : S → Prop)
    {Λ T : ℝ} (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, if noExit safe T w then ψ (timedHistory T w) else 0 ∂K.eventLaw Λ hΛ x) =
      ∫⁻ w, if noExit safe T w then ψ (timedHistory T w) else 0
        ∂(K.stop safe).eventLaw Λ hΛ x := by
  rw [K.noExit_history_reward safe hΛ hT x ψ,
    (K.stop safe).noExit_history_reward safe hΛ hT x ψ]
  exact K.poissonTrajectory_survivingReward safe _ x ψ

theorem noExit_endpoint_reward_le (K : HybridCTMC.Kernel S) (safe : S → Prop)
    {Λ T : ℝ} (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (g : S → ℝ≥0∞) :
    (∫⁻ w, if noExit safe T w then g (timedState T w) else 0 ∂K.eventLaw Λ hΛ x) ≤
      nnReward ((K.stop safe).timedEndpoint Λ hΛ T x) (fun y => if safe y then g y else 0) := by
  have he (w : ℕ → ℝ × S) : (timedHistory T w).getLastD x = timedState T w :=
    statePrefix_getLastD (clockIndex T w) w x
  have hc := K.noExit_history_coupling safe hΛ hT x (fun xs => g (xs.getLastD x))
  simp only [he] at hc
  rw [hc, ← lintegral_pmf_nnReward, (K.stop safe).timedEndpoint_toMeasure hΛ T x,
    endpointLaw, lintegral_map (measurable_of_countable _) (measurable_timedState T)]
  apply lintegral_mono
  intro w
  by_cases hw : noExit safe T w
  · simp only [ite_eq_left hw, ite_eq_left (hw T hT le_rfl), le_refl]
  · simp only [ite_eq_right hw, zero_le]

end
end HybridCTMC.Kernel
