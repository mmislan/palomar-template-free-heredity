module

public import proofs.HybridCTMCInfrastructure.StateHistory

@[expose] public section

/-! Finite-prefix observables represented on the actual path space. -/
namespace HybridCTMC.Kernel
open MeasureTheory Preorder
noncomputable section
variable {S : Type*}

def prefixPath (n : ℕ) (u : Π _ : Finset.Iic n, ℝ × S) (i : ℕ) : ℝ × S :=
  if h : i ≤ n then u ⟨i, Finset.mem_Iic.mpr h⟩
  else u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

theorem prefixPath_frestrict (n : ℕ) (w : ℕ → ℝ × S) (i : ℕ) (hi : i ≤ n) :
    prefixPath n (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) i = w i := by
  simp [prefixPath, hi, frestrictLe]

theorem arrivalTime_prefixPath (n : ℕ) (w : ℕ → ℝ × S) :
    arrivalTime n (prefixPath n (frestrictLe (π := fun _ : ℕ => ℝ × S) n w)) =
      arrivalTime n w := by
  unfold arrivalTime
  apply Finset.sum_congr rfl
  intro i hi
  rw [prefixPath_frestrict n w (i+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))]

theorem statePrefix_prefixPath (n : ℕ) (w : ℕ → ℝ × S) :
    statePrefix n (prefixPath n (frestrictLe (π := fun _ : ℕ => ℝ × S) n w)) =
      statePrefix n w := by
  unfold statePrefix
  apply congrArg List.ofFn
  funext i
  rw [prefixPath_frestrict n w i (Nat.le_of_lt_succ i.isLt)]

theorem statePrefix_getLastD (n : ℕ) (w : ℕ → ℝ × S) (x : S) :
    (statePrefix n w).getLastD x = (w n).2 := by
  cases n with
  | zero => simp [statePrefix_zero]
  | succ n => rw [statePrefix_succ, List.getLastD_concat]

variable [MeasurableSpace S]

theorem measurable_prefixPath (n : ℕ) : Measurable (prefixPath (S := S) n) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ≤ n
  · simpa only [prefixPath, dite_eq_left hi] using
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
        ⟨i, Finset.mem_Iic.mpr hi⟩)
  · simpa only [prefixPath, dite_eq_right hi] using
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
        ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩)

variable [Fintype S] [MeasurableSingletonClass S]

theorem measurable_statePrefix_observable {E : Type*} [MeasurableSpace E]
    (n : ℕ) (ψ : List S → E) : Measurable (fun w : ℕ → ℝ × S => ψ (statePrefix n w)) := by
  have hm : Measurable (fun w : ℕ → ℝ × S => fun i : Fin (n+1) => (w i).2) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (i : ℕ)).snd
  exact (measurable_of_countable (fun u : Fin (n+1) → S => ψ (List.ofFn u))).comp hm

theorem measurable_statePrefix_append_observable {E : Type*} [MeasurableSpace E]
    (n : ℕ) (ψ : List S → E) :
    Measurable (fun p : (ℕ → ℝ × S) × (ℝ × S) => ψ (statePrefix n p.1 ++ [p.2.2])) := by
  have hm : Measurable (fun p : (ℕ → ℝ × S) × (ℝ × S) =>
      ((fun i : Fin (n+1) => (p.1 i).2), p.2.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (i : ℕ)).comp measurable_fst).snd
    · exact measurable_snd.comp measurable_snd
  exact (measurable_of_countable (fun u : (Fin (n+1) → S) × S =>
    ψ (List.ofFn u.1 ++ [u.2]))).comp hm

end
end HybridCTMC.Kernel
