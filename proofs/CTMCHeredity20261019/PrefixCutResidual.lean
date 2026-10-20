module

public import proofs.CTMCHeredity20261019.ClockStepResidual
public import proofs.HybridCTMCInfrastructure.PrefixFactorization
public import proofs.HybridCTMCInfrastructure.EventArrival

@[expose] public section

/-!
# Residual holding law inside the actual finite-prefix disintegration

The elapsed time may depend on the entire finite history. The main source-level
theorem uses the literal `arrivalTime` and the exact slice
`arrivalTime n ≤ T < arrivalTime (n+1)`. The next residual hold and next state
are integrated against the original `clockStep`, weighted by survival from the
last arrival to the cut. No conditional infinite-suffix law is assumed.

The prefix-arrival helper is just a finite-coordinate presentation of the
source arrival sum. It avoids importing HistoryObservables and its much wider
TimedProcess closure merely to extend a finite tuple to an infinite sequence.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators ENNReal
noncomputable section

abbrev CutPrefix (S : Type*) (n : ℕ) := ∀ _ : Finset.Iic n, ℝ × S

/-- The source arrival sum, evaluated directly on the finite prefix carrier. -/
def cutPrefixArrival {S : Type*} (n : ℕ) (u : CutPrefix S n) : ℝ :=
  ∑ i ∈ Finset.range n,
    if hi : i + 1 ≤ n then max 0 (u ⟨i + 1, Finset.mem_Iic.mpr hi⟩).1 else 0

theorem measurable_cutPrefixArrival {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (cutPrefixArrival (S := S) n) := by
  unfold cutPrefixArrival
  apply Finset.measurable_sum
  intro i hi
  have hin : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  simp only [dite_eq_left hin]
  exact measurable_const.max
    (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
      ⟨i + 1, Finset.mem_Iic.mpr hin⟩).fst

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem cutPrefixArrival_frestrict (n : ℕ) (w : ℕ → ℝ × S) :
    cutPrefixArrival n (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) =
      HybridCTMC.Kernel.arrivalTime n w := by
  unfold cutPrefixArrival HybridCTMC.Kernel.arrivalTime
  apply Finset.sum_congr rfl
  intro i hi
  rw [dite_eq_left (Nat.succ_le_of_lt (Finset.mem_range.mp hi))]
  rfl

/-- One-step residual factorization under the actual event law, for any
measurable last-arrival time depending on the complete finite prefix. -/
theorem eventLaw_prefix_cut_residual (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ)
    (a : CutPrefix S n → ℝ) (ha : Measurable a) (T : ℝ)
    (F : CutPrefix S n × (ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if a (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) ≤ T ∧
          T < a (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) + (w (n + 1)).1 then
        F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w,
          (a (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) + (w (n + 1)).1 - T,
            (w (n + 1)).2))
      else 0 ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if a u ≤ T then ENNReal.ofReal (Real.exp (-(Lam * (T - a u)))) *
          ∫⁻ z, F (u, z) ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let G : CutPrefix S n × (ℝ × S) → ℝ≥0∞ := fun p =>
    if a p.1 ≤ T ∧ T < a p.1 + p.2.1 then
      F (p.1, (a p.1 + p.2.1 - T, p.2.2)) else 0
  have ht : Measurable (fun p : CutPrefix S n × (ℝ × S) => a p.1 + p.2.1) :=
    (ha.comp measurable_fst).add (measurable_fst.comp measurable_snd)
  have hr : Measurable (fun p : CutPrefix S n × (ℝ × S) => a p.1 + p.2.1 - T) :=
    ht.sub measurable_const
  have hobs : Measurable (fun p : CutPrefix S n × (ℝ × S) =>
      F (p.1, (a p.1 + p.2.1 - T, p.2.2))) :=
    hF.comp (measurable_fst.prodMk (hr.prodMk (measurable_snd.comp measurable_snd)))
  have hG : Measurable G :=
    Measurable.ite
      ((measurableSet_le (ha.comp measurable_fst) measurable_const).inter
        (measurableSet_lt measurable_const ht)) hobs measurable_const
  calc
    _ = ∫⁻ u, ∫⁻ z, G (u, z)
        ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) :=
      K.eventLaw_lintegral_prefix_step hLam x n G hG
    _ = _ := by
      apply lintegral_congr
      intro u
      by_cases hu : a u ≤ T
      · simp only [G, hu, true_and, ite_true]
        exact clockStep_residual_at_cut K hLam hu
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
          (fun z => F (u, z)) (hF.comp measurable_prodMk_left)
      · simp [G, hu]

/-- Residual holding/state factorization on the literal source arrival slice.
The next arrival uses the source's clipped holding-time convention everywhere;
on this slice the hold is positive, so its actual residual is unambiguous. -/
theorem eventLaw_arrival_slice_residual (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (F : CutPrefix S n × (ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if HybridCTMC.Kernel.arrivalTime n w ≤ T ∧
          T < HybridCTMC.Kernel.arrivalTime (n + 1) w then
        F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w,
          (HybridCTMC.Kernel.arrivalTime (n + 1) w - T, (w (n + 1)).2))
      else 0 ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T then
          ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          ∫⁻ z, F (u, z) ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  have he : (fun w : ℕ → ℝ × S =>
      if HybridCTMC.Kernel.arrivalTime n w ≤ T ∧
          T < HybridCTMC.Kernel.arrivalTime (n + 1) w then
        F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w,
          (HybridCTMC.Kernel.arrivalTime (n + 1) w - T, (w (n + 1)).2)) else 0) =
      (fun w : ℕ → ℝ × S =>
        if HybridCTMC.Kernel.arrivalTime n w ≤ T ∧
            T < HybridCTMC.Kernel.arrivalTime n w + (w (n + 1)).1 then
          F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w,
            (HybridCTMC.Kernel.arrivalTime n w + (w (n + 1)).1 - T,
              (w (n + 1)).2)) else 0) := by
    funext w
    have hnext : HybridCTMC.Kernel.arrivalTime (n + 1) w =
        HybridCTMC.Kernel.arrivalTime n w + max 0 (w (n + 1)).1 := by
      simp only [HybridCTMC.Kernel.arrivalTime, Finset.sum_range_succ]
    by_cases hu : HybridCTMC.Kernel.arrivalTime n w ≤ T
    · by_cases hh : 0 ≤ (w (n + 1)).1
      · rw [hnext, max_eq_right hh]
      · have hh' : (w (n + 1)).1 ≤ 0 := le_of_not_ge hh
        have hn : ¬ T < HybridCTMC.Kernel.arrivalTime n w := not_lt.mpr hu
        have hr : ¬ T < HybridCTMC.Kernel.arrivalTime n w + (w (n + 1)).1 := by
          linarith
        simp [hnext, max_eq_left hh', hu, hn, hr]
    · simp [hu]
  rw [he]
  simpa only [cutPrefixArrival_frestrict] using
    eventLaw_prefix_cut_residual K hLam x n (cutPrefixArrival n)
      (measurable_cutPrefixArrival n) T F hF

end
end CTMCHeredity20261019
