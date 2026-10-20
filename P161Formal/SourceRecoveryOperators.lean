module

public import P161Formal.MarkedSuboperators
public import P161Formal.SourceResetCertificate

/-! Literal source proposal suboperators for stopped recovery. Actual division
labels, including state-null physical divisions, are retained in the reset
operator. Only `none` is an idle proposal. The raw natural ledgers are retained. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev RecoveryMark := CTMCHeredity20261019.CF3Marked.Mark (literalSourcePar 0)
abbrev recoveryLambda : ℝ := 93515792

local instance : DecidablePred recoverySourceLive := fun _ => Classical.propDecidable _

abbrev recoveryChannels : HybridCTMC.Channels RecoverySource RecoveryMark :=
  CTMCHeredity20261019.CF3Marked.sourceChannels (literal_source_valid 0 (by norm_num))

theorem recovery_lambda_positive : 0 < recoveryLambda := by norm_num

theorem recovery_proposal_rate_bound (x : RecoverySource) :
    (∑ r : RecoveryMark, recoveryChannels.propensity x r) ≤ recoveryLambda := by
  have h := CTMCHeredity20261019.CF3Marked.sourceIntensity_bound
    (literal_source_valid 0 (by norm_num)) x
  exact h.trans_eq source_common_clock.2

def isDivisionProposal : Option RecoveryMark → Bool
  | some (Sum.inr _) => true
  | some (Sum.inl _) | none => false

def recoveryResetOperator : FunctionalCapacity.SubMarkov RecoverySource := by
  classical
  exact markedSuboperator recoveryChannels recovery_lambda_positive recovery_proposal_rate_bound
    recoverySourceLive (fun m => isDivisionProposal m = true)

def recoveryNonresetOperator : FunctionalCapacity.SubMarkov RecoverySource := by
  classical
  exact markedSuboperator recoveryChannels recovery_lambda_positive recovery_proposal_rate_bound
    recoverySourceLive (fun m => ¬isDivisionProposal m = true)

def recoveryKillReward (f : RecoverySource → ℝ) (x : RecoverySource) : ℝ := by
  classical
  exact if recoverySourceLive x then f x else 0

theorem recovery_kill_potential (x : RecoverySource) :
    recoveryKillReward (sourcePotential strongRecoveryWitness) x = killedRecoveryPotential x := by
  rfl

theorem recovery_reset_nonreset_partition (f : RecoverySource → ℝ) (x : RecoverySource) :
    recoveryResetOperator.P f x+recoveryNonresetOperator.P f x =
      restrictedProposalApply recoveryChannels recoveryLambda recoverySourceLive
        (fun _ => True) f x := by
  classical
  exact restricted_proposal_partition recoveryChannels recoveryLambda recoverySourceLive
    (fun m => isDivisionProposal m = true) f x

theorem recovery_partition_generator (f : RecoverySource → ℝ) (x : RecoverySource)
    (hx : recoverySourceLive x) :
    recoveryResetOperator.P f x+recoveryNonresetOperator.P f x =
      f x+FunctionalCapacity.cf3Gen (literalSourcePar 0) (recoveryKillReward f) x/recoveryLambda := by
  classical
  rw [recovery_reset_nonreset_partition]
  simp only [restrictedProposalApply,ite_eq_left hx,ite_true]
  change CTMCHeredity20261019.MarkedUniformization.expect recoveryChannels recoveryLambda x
    (fun m => recoveryKillReward f
      (CTMCHeredity20261019.MarkedUniformization.next recoveryChannels x m)) = _
  have h := CTMCHeredity20261019.CF3Marked.source_expect_next (p := literalSourcePar 0)
    (literal_source_valid 0 (by norm_num)) recoveryLambda (recoveryKillReward f) x
  simpa only [recoveryKillReward,ite_eq_left hx,recoveryChannels] using h

theorem source_reset_gain_mark_sum (x : RecoverySource) :
    sourceResetGain x = ∑ i : SiteId, ∑ k : Option SpeciesId,
      ∑ o : FunctionalCapacity.Split 3 2048, ∑ v : SiteId,
        CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar 0) x
          (Sum.inr (i,(k,(o,v)))) *
        killedRecoveryPotential
          (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar 0) x
            (Sum.inr (i,(k,(o,v))))) := by
  unfold sourceResetGain sourceDivisionChannelGain
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro v _
  simp only [CTMCHeredity20261019.CF3Marked.sourceIntensity,
    CTMCHeredity20261019.CF3Marked.outcomeWeight,CTMCHeredity20261019.CF3Marked.sourceNext]
  ring

end
end P161Formal
