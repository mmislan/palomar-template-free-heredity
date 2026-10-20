module

public import P161Formal.SourceRecoveryOperators

/-! Witness inequalities for the actual stopped raw-source proposal
suboperators. The physical marked path probability interpretation is separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev RecoveryDivisionLabel :=
  SiteId × (Option SpeciesId × (FunctionalCapacity.Split 3 2048 × SiteId))

theorem source_division_gain_sum (x : RecoverySource) :
    (∑ d : RecoveryDivisionLabel,
      CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x (Sum.inr d)*
        killedRecoveryPotential
          (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar 0) x (Sum.inr d))) =
      sourceResetGain x := by
  simpa only [Fintype.sum_prod_type] using (source_reset_gain_mark_sum x).symm

theorem source_division_label_intensity (x : RecoverySource) :
    (∑ d : RecoveryDivisionLabel,
      CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x (Sum.inr d)) =
        sourceActualDivisionIntensity x := by
  calc
    _ = ∑ i : SiteId, ∑ k : Option SpeciesId,
        ∑ z : FunctionalCapacity.Split 3 2048 × SiteId,
          CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x (Sum.inr (i,(k,z))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
    _ = ∑ i : SiteId, ∑ k : Option SpeciesId,
        (FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) k := by
      simp only [CTMCHeredity20261019.CF3Marked.divisionIntensity_sum
        (literal_source_valid 0 (by norm_num))]
    _ = sourceActualDivisionIntensity x := by
      simp only [Fintype.sum_option,sourceActualDivisionIntensity,siteDivisionIntensity,
        contract_division_rate_is_source]

theorem source_generator_killed_decomposition (x : RecoverySource) :
    FunctionalCapacity.cf3Gen (literalSourcePar 0) killedRecoveryPotential x =
      sourceChemicalGenerator killedRecoveryPotential x+sourceResetGain x-
        sourceActualDivisionIntensity x*killedRecoveryPotential x := by
  rw [←CTMCHeredity20261019.CF3Marked.source_generator
    (p := literalSourcePar 0) killedRecoveryPotential x,Fintype.sum_sum_type]
  have hchem : (∑ r : SiteId × FunctionalCapacity.Chem 3,
      CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x (Sum.inl r)*
        (killedRecoveryPotential
          (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar 0) x (Sum.inl r))-
            killedRecoveryPotential x)) = sourceChemicalGenerator killedRecoveryPotential x := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hchem]
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  rw [source_division_gain_sum,source_division_label_intensity]
  ring

theorem recovery_reset_apply_live (x : RecoverySource) (hx : recoverySourceLive x) :
    recoveryResetOperator.P (sourcePotential strongRecoveryWitness) x =
      sourceResetGain x/recoveryLambda := by
  classical
  change restrictedProposalApply recoveryChannels recoveryLambda recoverySourceLive
    (fun m => isDivisionProposal m = true) (sourcePotential strongRecoveryWitness) x = _
  rw [restrictedProposalApply,ite_eq_left hx]
  simp only [Fintype.sum_option,Fintype.sum_sum_type,isDivisionProposal,
    CTMCHeredity20261019.MarkedUniformization.weight,
    CTMCHeredity20261019.MarkedUniformization.next,Bool.false_eq_true,
    ite_false,ite_true,mul_zero,Finset.sum_const_zero,zero_add]
  change (∑ d : RecoveryDivisionLabel,
    CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x (Sum.inr d)/recoveryLambda*
      killedRecoveryPotential
        (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar 0) x (Sum.inr d))) = _
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,source_division_gain_sum]

theorem recovery_reset_apply_dead (f : RecoverySource → ℝ) (x : RecoverySource)
    (hx : ¬recoverySourceLive x) : recoveryResetOperator.P f x = 0 := by
  classical
  simp only [recoveryResetOperator,markedSuboperator,restrictedProposalApply,ite_eq_right hx]

theorem recovery_nonreset_apply_dead (f : RecoverySource → ℝ) (x : RecoverySource)
    (hx : ¬recoverySourceLive x) : recoveryNonresetOperator.P f x = 0 := by
  classical
  simp only [recoveryNonresetOperator,markedSuboperator,restrictedProposalApply,ite_eq_right hx]

theorem recovery_reset_witness (x : RecoverySource) :
    recoveryResetOperator.P (sourcePotential strongRecoveryWitness) x ≤
      (478/recoveryLambda)*sourcePotential strongRecoveryWitness x := by
  by_cases hx : recoverySourceLive x
  · rw [recovery_reset_apply_live x hx,div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right recovery_lambda_positive).mpr
      (source_direct_reset_gain_bound x hx).2.le
  · rw [recovery_reset_apply_dead _ x hx]
    exact mul_nonneg (by norm_num) (source_selected_potential_nonnegative x)

theorem recovery_nonreset_witness (x : RecoverySource) :
    recoveryNonresetOperator.P (sourcePotential strongRecoveryWitness) x ≤
      (1-(263197/1175 : ℝ)/recoveryLambda)*sourcePotential strongRecoveryWitness x := by
  by_cases hx : recoverySourceLive x
  · have h := recovery_partition_generator (sourcePotential strongRecoveryWitness) x hx
    have hk : recoveryKillReward (sourcePotential strongRecoveryWitness) = killedRecoveryPotential :=
      funext recovery_kill_potential
    have hcurrent : killedRecoveryPotential x = sourcePotential strongRecoveryWitness x := by
      simp only [killedRecoveryPotential,ite_eq_left hx]
    rw [hk,source_generator_killed_decomposition x,hcurrent,recovery_reset_apply_live x hx] at h
    have hd := source_killed_nonreset_recovery_bound x hx
    unfold sourceKilledNonresetDrift at hd
    norm_num only [recoveryLambda] at h ⊢
    nlinarith
  · rw [recovery_nonreset_apply_dead _ x hx]
    exact mul_nonneg (by norm_num) (source_selected_potential_nonnegative x)

end
end P161Formal
