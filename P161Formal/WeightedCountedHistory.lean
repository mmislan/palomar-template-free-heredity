module

public import P161Formal.CountedLiveHistory
public import proofs.CTMCHeredity20261019.V2.MarkedCountTail

/-! Multiplicative marked-history bounds with a terminal occupation witness.
The terminal factor is retained, so fuel accounting can telescope through
physical intervals without a fresh stock allocation at each boundary. -/

@[expose] public section
namespace P161Formal
open HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped ENNReal Classical
noncomputable section
variable {S : Type*} [Fintype S]

def weightedWholeHistory (f : S → ℝ≥0∞) (U : S → ℝ) (xs : List S) : ℝ≥0∞ :=
  wholeWeight f xs*historyTerminal U xs

def weightedTailHistory (f : S → ℝ≥0∞) (U : S → ℝ) (xs : List S) : ℝ≥0∞ :=
  tailWeight f xs*historyTerminal U xs

theorem trajectory_weighted_whole_eq (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (U : S → ℝ) (n : ℕ) (x : S) :
    nnReward (K.trajectory n x) (weightedWholeHistory f U) =
      f x*nnReward (K.trajectory n x) (weightedTailHistory f U) := by
  have he := nnReward_congr_support (K.trajectory n x) (weightedWholeHistory f U)
    (fun xs => f x*weightedTailHistory f U xs) (by
      intro xs hs
      obtain ⟨ys,rfl⟩ := trajectory_support_cons K n x xs hs
      simp only [weightedWholeHistory,weightedTailHistory,wholeWeight,tailWeight,List.tail_cons]
      exact mul_assoc _ _ _)
  rw [he,CTMCHeredity20261019.V2.MarkedCountTail.nnReward_const_mul]

theorem trajectory_weighted_cons_reward (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (U : S → ℝ) (n : ℕ) (x y : S) :
    nnReward (K.trajectory n y) (fun xs => weightedTailHistory f U (x::xs)) =
      nnReward (K.trajectory n y) (weightedWholeHistory f U) := by
  apply nnReward_congr_support
  intro xs hs
  obtain ⟨ys,rfl⟩ := trajectory_support_cons K n y xs hs
  rfl

theorem trajectory_weighted_tail_succ (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (U : S → ℝ) (n : ℕ) (x : S) :
    nnReward (K.trajectory (n+1) x) (weightedTailHistory f U) =
      nnReward (K.pmf x) (fun y => f y*
        nnReward (K.trajectory n y) (weightedTailHistory f U)) := by
  rw [Kernel.trajectory,nnReward_bind]
  simp_rw [nnReward_map,trajectory_weighted_cons_reward,trajectory_weighted_whole_eq]

theorem trajectory_weighted_tail_bound (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (U : S → ℝ) (a : ℝ≥0∞)
    (hloc : ∀ x, nnReward (K.pmf x) (fun y => f y*ENNReal.ofReal (U y)) ≤ a*ENNReal.ofReal (U x))
    (n : ℕ) (x : S) :
    nnReward (K.trajectory n x) (weightedTailHistory f U) ≤ a^n*ENNReal.ofReal (U x) := by
  induction n generalizing x with
  | zero => simp [Kernel.trajectory,nnReward_pure,weightedTailHistory,tailWeight,wholeWeight,historyTerminal]
  | succ n ih =>
    rw [trajectory_weighted_tail_succ]
    calc
      _ ≤ nnReward (K.pmf x) (fun y => f y*(a^n*ENNReal.ofReal (U y))) :=
        nnReward_pointwise_le _ _ _ (fun y => mul_le_mul_right (ih y) (f y))
      _ = a^n*nnReward (K.pmf x) (fun y => f y*ENNReal.ofReal (U y)) := by
        have he : (fun y => f y*(a^n*ENNReal.ofReal (U y))) =
            (fun y => a^n*(f y*ENNReal.ofReal (U y))) := by
          funext y
          ac_rfl
        rw [he,CTMCHeredity20261019.V2.MarkedCountTail.nnReward_const_mul]
      _ ≤ a^n*(a*ENNReal.ofReal (U x)) := mul_le_mul_right (hloc x) (a^n)
      _ = a^(n+1)*ENNReal.ofReal (U x) := by rw [pow_succ]; ac_rfl

omit [Fintype S] in
theorem history_terminal_append_singleton (U : S → ℝ) (xs : List S) (y : S) :
    historyTerminal U (xs++[y]) = ENNReal.ofReal (U y) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons z zs => exact ih

omit [Fintype S] in
theorem history_terminal_statePrefix (U : S → ℝ) (w : ℕ → ℝ × S) (n : ℕ) :
    historyTerminal U (statePrefix n w) = ENNReal.ofReal (U (w n).2) := by
  cases n with
  | zero => rw [statePrefix_zero]; rfl
  | succ n => rw [statePrefix_succ,history_terminal_append_singleton]

omit [Fintype S] in
theorem history_terminal_timed_history (U : S → ℝ) (T : ℝ) (w : ℕ → ℝ × S) :
    historyTerminal U (timedHistory T w) = ENNReal.ofReal (U (timedState T w)) :=
  history_terminal_statePrefix U w (clockIndex T w)

end
end P161Formal
