module

public import proofs.HybridCTMCInfrastructure.PrefixFactorization
public import proofs.HybridCTMCInfrastructure.PrefixReward
public import proofs.HybridCTMCInfrastructure.HistoryObservables
public import proofs.HybridCTMCInfrastructure.ClockFunctional
public import proofs.HybridCTMCInfrastructure.ClockInitial

@[expose] public section

/-! Uniform clock/history factorization for the actual constructed event law.
No Poisson count distribution is an input. -/
namespace HybridCTMC.Kernel
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem clock_history_step (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (x : S) (n : ℕ) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, φ (arrivalTime (n+1) w)*ψ (statePrefix (n+1) w) ∂K.eventLaw Λ hΛ x) =
    ∫⁻ w, (∫⁻ h, φ (arrivalTime n w+max 0 h) ∂expMeasure Λ)*
      nnReward (K.pmf ((statePrefix n w).getLastD x))
        (fun y => ψ (statePrefix n w ++ [y])) ∂K.eventLaw Λ hΛ x := by
  let A := fun u : Π _ : Finset.Iic n, ℝ × S => arrivalTime n (prefixPath n u)
  let L := fun u : Π _ : Finset.Iic n, ℝ × S => statePrefix n (prefixPath n u)
  let g := fun a : ℝ => ∫⁻ h, φ (a+max 0 h) ∂expMeasure Λ
  let ψ' := fun xs : List S => nnReward (K.pmf (xs.getLastD x)) (fun y => ψ (xs ++ [y]))
  let F : (Π _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ≥0∞ := fun p =>
    φ (A p.1+max 0 p.2.1)*ψ (L p.1 ++ [p.2.2])
  have hA : Measurable A :=
    ((measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl).comp (measurable_prefixPath n)
  have hg : Measurable g := HoldingTime.measurable_holding_average hΛ φ hφ
  have hF : Measurable F := by
    apply Measurable.mul
    · exact hφ.comp ((hA.comp measurable_fst).add
        (measurable_const.max (measurable_fst.comp measurable_snd)))
    · exact (measurable_statePrefix_append_observable n ψ).comp
        (((measurable_prefixPath n).comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable (fun u => g (A u)*ψ' (L u)) :=
    (hg.comp hA).mul ((measurable_statePrefix_observable n ψ').comp (measurable_prefixPath n))
  calc
    _ = ∫⁻ w, F (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n+1))
        ∂K.eventLaw Λ hΛ x := by
      apply lintegral_congr
      intro w
      dsimp only [F, A, L]
      rw [arrivalTime_prefixPath, statePrefix_prefixPath, statePrefix_succ]
      simp only [arrivalTime, Finset.sum_range_succ]
    _ = ∫⁻ u, ∫⁻ z, F (u, z)
        ∂K.clockStep Λ (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) :=
      K.eventLaw_lintegral_prefix_step hΛ x n F hF
    _ = ∫⁻ u, g (A u)*ψ' (L u)
        ∂((K.eventLaw Λ hΛ x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
      apply lintegral_congr
      intro u
      change (∫⁻ z, φ (A u+max 0 z.1)*ψ (L u ++ [z.2])
        ∂K.clockStep Λ (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) = _
      rw [K.clockStep_lintegral_mul Λ _ (fun h => φ (A u+max 0 h))
        (fun y => ψ (L u ++ [y])) (by fun_prop) (measurable_of_countable _),
        lintegral_pmf_nnReward]
      have hl : (L u).getLastD x = (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 := by
        change (statePrefix n (prefixPath n u)).getLastD x = _
        rw [statePrefix_getLastD]
        simp [prefixPath]
      dsimp [g, ψ']
      rw [hl]
    _ = _ := by
      rw [lintegral_map hG (measurable_frestrictLe n)]
      apply lintegral_congr
      intro w
      simp only [A, L, arrivalTime_prefixPath, statePrefix_prefixPath, g, ψ']

theorem clock_history_factorization (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ)
    (x : S) (n : ℕ) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (ψ : List S → ℝ≥0∞) :
    (∫⁻ w, φ (arrivalTime n w)*ψ (statePrefix n w) ∂K.eventLaw Λ hΛ x) =
      HoldingTime.clockIntegral Λ n φ * nnReward (K.trajectory n x) ψ := by
  induction n generalizing φ ψ with
  | zero =>
    have he : (fun w => φ (arrivalTime 0 w)*ψ (statePrefix 0 w)) =ᵐ[K.eventLaw Λ hΛ x]
        fun _ => φ 0*ψ [x] := by
      filter_upwards [K.ae_event_initial hΛ x] with w hw
      simp [arrivalTime, statePrefix_zero, hw]
    rw [lintegral_congr_ae he]
    simp [HoldingTime.clockIntegral, trajectory, nnReward_pure]
  | succ n ih =>
    rw [K.clock_history_step hΛ x n φ hφ ψ]
    rw [ih (fun a => ∫⁻ h, φ (a+max 0 h) ∂expMeasure Λ)
      (HoldingTime.measurable_holding_average hΛ φ hφ)
      (fun xs => nnReward (K.pmf (xs.getLastD x)) (fun y => ψ (xs ++ [y])))]
    rw [HoldingTime.clockIntegral_succ, K.trajectoryReward_snoc]

end
end HybridCTMC.Kernel
