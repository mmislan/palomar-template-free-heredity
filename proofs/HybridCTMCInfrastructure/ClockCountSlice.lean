module

public import proofs.HybridCTMCInfrastructure.ClockHistoryFactorization
public import proofs.HybridCTMCInfrastructure.ClockSurvival
public import proofs.HybridCTMCInfrastructure.ClockSurvivalConvolution

@[expose] public section

/-! Extract a fixed clock count using the next hold's actual survival law. -/
namespace HybridCTMC.Kernel
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem clock_count_survival (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (n : ℕ) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, if clockIndex T w = n then ψ (statePrefix n w) else 0 ∂K.eventLaw Λ hΛ x) =
    ∫⁻ w, HoldingTime.survivalWeight Λ T 0 (arrivalTime n w)*ψ (statePrefix n w)
      ∂K.eventLaw Λ hΛ x := by
  let A := fun u : Π _ : Finset.Iic n, ℝ × S => arrivalTime n (prefixPath n u)
  let L := fun u : Π _ : Finset.Iic n, ℝ × S => statePrefix n (prefixPath n u)
  let F : (Π _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ≥0∞ := fun p =>
    if A p.1 ≤ T then (if T-A p.1 < max 0 p.2.1 then ψ (L p.1) else 0) else 0
  have hA : Measurable A :=
    ((measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl).comp (measurable_prefixPath n)
  have hL : Measurable (fun u => ψ (L u)) :=
    (measurable_statePrefix_observable n ψ).comp (measurable_prefixPath n)
  have hF : Measurable F := by
    apply Measurable.ite (measurableSet_le (hA.comp measurable_fst) measurable_const)
    · apply Measurable.ite (measurableSet_lt (measurable_const.sub (hA.comp measurable_fst))
        (measurable_const.max (measurable_fst.comp measurable_snd)))
      · exact hL.comp measurable_fst
      · exact measurable_const
    · exact measurable_const
  have hG : Measurable (fun u => HoldingTime.survivalWeight Λ T 0 (A u)*ψ (L u)) :=
    ((HoldingTime.measurable_survivalWeight Λ T 0).comp hA).mul hL
  calc
    _ = ∫⁻ w, F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n+1))
        ∂K.eventLaw Λ hΛ x := by
      apply lintegral_congr_ae
      filter_upwards [K.ae_arrival_crosses hΛ x T] with w hw
      have hs : arrivalTime (n+1) w = arrivalTime n w+max 0 (w (n+1)).1 := by
        simp [arrivalTime, Finset.sum_range_succ]
      have he : clockIndex T w = n ↔
          arrivalTime n w ≤ T ∧ T-arrivalTime n w < max 0 (w (n+1)).1 := by
        rw [clockIndex_eq_iff_between w hT hw n, hs]
        constructor <;> rintro ⟨ha, hb⟩ <;> constructor
        · exact ha
        · linarith
        · exact ha
        · linarith
      dsimp only [F, A, L]
      simp only [arrivalTime_prefixPath, statePrefix_prefixPath, he]
      by_cases ha : arrivalTime n w ≤ T <;> simp [ha]
    _ = ∫⁻ u, ∫⁻ z, F (u, z)
        ∂K.clockStep Λ (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) :=
      K.eventLaw_lintegral_prefix_step hΛ x n F hF
    _ = ∫⁻ u, HoldingTime.survivalWeight Λ T 0 (A u)*ψ (L u)
        ∂((K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
      apply lintegral_congr
      intro u
      by_cases ha : A u ≤ T
      · have he : (fun z : ℝ × S => F (u,z)) = fun z =>
            (if T-A u < max 0 z.1 then (1:ℝ≥0∞) else 0)*ψ (L u) := by
          funext z
          dsimp [F]
          rw [ite_eq_left ha]
          split_ifs <;> simp
        rw [he, K.clockStep_lintegral_mul Λ _
          (fun h => if T-A u < max 0 h then (1:ℝ≥0∞) else 0) (fun _ => ψ (L u))
          (Measurable.ite (measurableSet_lt measurable_const (measurable_const.max measurable_id))
            measurable_const measurable_const) measurable_const,
          HoldingTime.lintegral_survival_indicator hΛ (sub_nonneg.mpr ha)]
        simp [HoldingTime.survivalWeight_zero, ha]
      · simp [F, ha, HoldingTime.survivalWeight_zero]
    _ = _ := by
      rw [lintegral_map hG (measurable_frestrictLe n)]
      apply lintegral_congr
      intro w
      simp only [A, L, arrivalTime_prefixPath, statePrefix_prefixPath]

theorem clock_count_prefix_factorization (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (n : ℕ) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, if clockIndex T w = n then ψ (statePrefix n w) else 0 ∂K.eventLaw Λ hΛ x) =
      HoldingTime.clockIntegral Λ n (HoldingTime.survivalWeight Λ T 0)*
        nnReward (K.trajectory n x) ψ := by
  rw [K.clock_count_survival hΛ hT x n ψ,
    K.clock_history_factorization hΛ x n (HoldingTime.survivalWeight Λ T 0)
      (HoldingTime.measurable_survivalWeight Λ T 0) ψ]

theorem clock_count_prefix_poisson (K : HybridCTMC.Kernel S) {Λ T : ℝ}
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (x : S) (n : ℕ) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, if clockIndex T w = n then ψ (statePrefix n w) else 0 ∂K.eventLaw Λ hΛ x) =
      ENNReal.ofReal (poissonWeight ⟨Λ*T, mul_nonneg hΛ.le hT⟩ n)*
        nnReward (K.trajectory n x) ψ := by
  rw [K.clock_count_prefix_factorization hΛ hT x n ψ,
    HoldingTime.clockIntegral_survivalWeight hΛ]
  simp only [Nat.add_zero, HoldingTime.survivalWeight, ite_eq_left hT, sub_zero,
    poissonWeight]
  rfl

end
end HybridCTMC.Kernel
