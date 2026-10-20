module

public import P161Formal.SourceRecoveryPoisson
public import proofs.CTMCHeredity20261019.CF3MarkedKernel

/-! The checked raw-source recovery inequalities dock to the actual finite
counts/fuel/last-mark kernel. Natural q/nd are forgotten only in observables
which depend exclusively on current counts and fuel. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019 CTMCHeredity20261019.CF3Marked
open scoped BigOperators Classical
noncomputable section

abbrev RecoveryCore := CoreState (literalSourcePar 0)
abbrev RecoveryMarkedState := CF3MarkedKernel.State (literalSourcePar 0)
abbrev recoveryValid := literal_source_valid 0 (by norm_num)

abbrev recoveryCorePotential (x : RecoveryCore) : ℝ :=
  sourcePotential strongRecoveryWitness (coreRepresent x)

abbrev recoveryCoreLive (x : RecoveryCore) : Prop := recoverySourceLive (coreRepresent x)

abbrev recoveryStatePotential (z : RecoveryMarkedState) : ℝ := recoveryCorePotential z.1
abbrev recoveryStateLive (z : RecoveryMarkedState) : Prop := recoveryCoreLive z.1
abbrev recoveryStateDivision (z : RecoveryMarkedState) : Prop := isDivisionProposal z.2 = true

theorem recovery_core_potential_project (x : RecoverySource) :
    recoveryCorePotential (coreProject x) = sourcePotential strongRecoveryWitness x := rfl

theorem recovery_core_live_project (x : RecoverySource) :
    recoveryCoreLive (coreProject x) ↔ recoverySourceLive x := Iff.rfl

theorem recovery_kernel_filtered_expect (keep : Option RecoveryMark → Prop) [DecidablePred keep]
    (x : RecoverySource) (old : Option RecoveryMark) (hx : recoverySourceLive x) :
    (CF3MarkedKernel.kernel recoveryValid).expect
      (fun y => if recoveryStateLive y ∧ keep y.2 then recoveryStatePotential y else 0)
      (coreProject x,old) =
        restrictedProposalApply recoveryChannels recoveryLambda recoverySourceLive keep
          (sourcePotential strongRecoveryWitness) x := by
  rw [CF3MarkedKernel.kernel,MarkedKernel.kernel_expect,source_common_clock.2]
  unfold MarkedUniformization.expect
  rw [restrictedProposalApply,ite_eq_left hx]
  apply Finset.sum_congr rfl
  intro m _
  rw [← CF3MarkedKernel.proposalWeight_lump recoveryValid recoveryLambda x m]
  have hn := CF3MarkedKernel.proposalNext_project recoveryValid x m
  change _ * (if recoveryCoreLive
    (MarkedUniformization.next (coreChannels recoveryValid) (coreProject x) m) ∧ keep m
      then recoveryCorePotential
        (MarkedUniformization.next (coreChannels recoveryValid) (coreProject x) m) else 0) = _
  rw [← hn,recovery_core_potential_project]
  have hl := recovery_core_live_project
    (MarkedUniformization.next recoveryChannels x m)
  simp only [hl]
  split_ifs <;> first | rfl | simp_all

theorem recovery_kernel_nonreset_bound (z : RecoveryMarkedState)
    (hz : recoveryStateLive z) :
    (CF3MarkedKernel.kernel recoveryValid).expect
      (fun y => if recoveryStateLive y ∧ ¬recoveryStateDivision y
        then recoveryStatePotential y else 0) z ≤ recoveryWordA*recoveryStatePotential z := by
  rcases z with ⟨z,old⟩
  have hx : recoverySourceLive (coreRepresent z) := hz
  have h := recovery_kernel_filtered_expect (fun m => ¬isDivisionProposal m = true)
    (coreRepresent z) old hx
  simp only [coreProject_represent] at h
  change _ ≤ recoveryWordA*sourcePotential strongRecoveryWitness (coreRepresent z)
  refine le_trans ?_ (h.le.trans (recovery_nonreset_witness (coreRepresent z)))
  apply (CF3MarkedKernel.kernel recoveryValid).expect_mono
  intro y
  split_ifs <;> simp_all

theorem recovery_kernel_reset_bound (z : RecoveryMarkedState)
    (hz : recoveryStateLive z) :
    (CF3MarkedKernel.kernel recoveryValid).expect
      (fun y => if recoveryStateLive y ∧ recoveryStateDivision y
        then recoveryStatePotential y else 0) z ≤ recoveryWordB*recoveryStatePotential z := by
  rcases z with ⟨z,old⟩
  have hx : recoverySourceLive (coreRepresent z) := hz
  have h := recovery_kernel_filtered_expect (fun m => isDivisionProposal m = true)
    (coreRepresent z) old hx
  simp only [coreProject_represent] at h
  change _ ≤ recoveryWordB*sourcePotential strongRecoveryWitness (coreRepresent z)
  refine le_trans ?_ (h.le.trans (recovery_reset_witness (coreRepresent z)))
  apply (CF3MarkedKernel.kernel recoveryValid).expect_mono
  intro y
  split_ifs <;> simp_all

theorem recovery_state_potential_nonnegative (z : RecoveryMarkedState) :
    0 ≤ recoveryStatePotential z := source_selected_potential_nonnegative _

theorem recovery_state_potential_barrier (z : RecoveryMarkedState)
    (hz : recoveryStateLive z) : 1 ≤ recoveryStatePotential z := by
  change 1 ≤ sourcePotential strongRecoveryWitness (coreRepresent z.1)
  rw [source_selected_potential_eq]
  exact_mod_cast strong_nonready_barrier (sourcePopulation (coreRepresent z.1)) hz.1 hz.2

theorem recovery_state_potential_max (z : RecoveryMarkedState) :
    recoveryStatePotential z ≤ (338971453059/125000 : ℝ) := source_recovery_potential_max _

end
end P161Formal
