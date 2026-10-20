module

public import P161Formal.SourceRenewalSwitch

/-! Literal reconstructed global counts agree with the finite-core renewal
observables after withdrawal. The equality is proved on the actual joint law,
with arbitrary initial natural ledgers and no successful-history hypothesis. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019 CF3Marked CF3RawPathLift
open V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped ENNReal Classical
noncomputable section

local instance renewalObsRawMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (SourceState p) := ⊤
local instance renewalObsRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance renewalObsMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance renewalObsMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance renewalObsRecoveryMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalObsRecoveryMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩
local instance renewalObsCoreMeasurableSpace : MeasurableSpace RecoveryCore := ⊤
local instance renewalObsCoreMeasurableSingleton : MeasurableSingletonClass RecoveryCore :=
  ⟨fun _ => trivial⟩
local instance renewalObsLiteralRawMeasurableSpace : MeasurableSpace RecoverySource := ⊤
local instance renewalObsLiteralRawMeasurableSingleton : MeasurableSingletonClass RecoverySource :=
  ⟨fun _ => trivial⟩

def offRenewalInitial (a : PhaseHistory) : RecoverySource :=
  sourceResetAll (p := literalSourcePar 0) a.2

def offRenewalFoldCoherent (z : PhaseHistory × RecoveryPath) : Prop :=
  ∀ n : ℕ, coreProject (rawAt (literalSourcePar 0) (offRenewalInitial z.1) z.2 n) = (z.2 n).2.1

theorem measurable_offRenewalInitial : Measurable offRenewalInitial :=
  (measurable_of_countable (sourceResetAll (p := literalSourcePar 0))).comp measurable_snd

theorem measurableSet_offRenewalFoldCoherent :
    MeasurableSet {z | offRenewalFoldCoherent z} := by
  have hm (n : ℕ) : Measurable (fun z : RecoverySource × RecoveryPath =>
      coreProject (rawAt (literalSourcePar 0) z.1 z.2 n)) :=
    measurable_from_prod_countable_right (fun x =>
      (measurable_of_countable (coreProject (p := literalSourcePar 0))).comp
        (measurable_rawAt (literalSourcePar 0) x n))
  have hR (n : ℕ) : Measurable (fun w : RecoveryPath => (w n).2.1) :=
    (measurable_of_countable (fun z : RecoveryMarkedState => z.1)).comp
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × RecoveryMarkedState) n).snd
  have he (n : ℕ) : MeasurableSet {z : PhaseHistory × RecoveryPath |
      coreProject (rawAt (literalSourcePar 0) (offRenewalInitial z.1) z.2 n) = (z.2 n).2.1} :=
    measurableSet_eq_fun
      ((hm n).comp ((measurable_offRenewalInitial.comp measurable_fst).prodMk measurable_snd))
      ((hR n).comp (measurable_snd : Measurable (fun z : PhaseHistory × RecoveryPath => z.2)))
  convert MeasurableSet.iInter he using 1
  ext z
  simp only [offRenewalFoldCoherent,Set.mem_ofPred_eq,Set.mem_iInter]

set_option backward.isDefEq.respectTransparency false in
theorem ae_completed_switch_off_fold_coherent (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x,
      offRenewalFoldCoherent (z.1.1,offPath z) := by
  let B : Set (PhaseHistory × RecoveryPath) := {z | ¬offRenewalFoldCoherent z}
  have hB : MeasurableSet B := measurableSet_offRenewalFoldCoherent.compl
  let F : PhaseHistory × RecoveryPath → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hB
  have hzero (a : PhaseHistory) :
      (∫⁻ w, F (a,w) ∂CF3MarkedKernel.eventLaw canonicalSeedFree_valid
        (coreProject (sourceResetAll a.2)) none) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    have ha : ∀ᵐ w ∂CF3MarkedKernel.eventLaw canonicalSeedFree_valid
        (coreProject (sourceResetAll a.2)) none, offRenewalFoldCoherent (a,w) :=
      ae_rawAt_project recoveryValid (offRenewalInitial a) none
    filter_upwards [ha] with w hw
    exact Set.indicator_of_notMem (show (a,w) ∉ B from fun hb => hb hw) (fun _ => 1)
  rw [ae_iff]
  calc
    _ = ∫⁻ z, F (z.1.1,offPath z) ∂V4.TwoPhaseLaw.completedSwitchLaw x := by
      exact (lintegral_indicator_one
        (μ := V4.TwoPhaseLaw.completedSwitchLaw x)
        (hB.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_offPath))).symm
    _ = ∫⁻ a, ∫⁻ w, F (a,w)
        ∂CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject (sourceResetAll a.2)) none
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      completed_switch_off_joint_reward x F hF
    _ = 0 := (lintegral_congr hzero).trans lintegral_zero

theorem raw_at_core_congr {p : FunctionalCapacity.Par} (hp : p.Valid)
    (x y : SourceState p) (hxy : coreProject x = coreProject y) (w : MarkedPath p) (n : ℕ) :
    coreProject (rawAt p x w n) = coreProject (rawAt p y w n) := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
    simp only [rawAt_succ,CF3RawPathLift.sourceProposalNext_project hp,ih]

theorem source_reset_all_core {p : FunctionalCapacity.Par} (x : SourceState p) :
    coreProject (sourceResetAll (p := p) x) = coreProject x := rfl

set_option backward.isDefEq.respectTransparency false in
theorem ae_global_after_switch_core (x : Raw) :
    ∀ᵐ z ∂V4.TwoPhaseLaw.completedSwitchLaw x, ∀ t : ℝ, 0 ≤ t →
      coreProject (p := literalSourcePar 0) (globalState x z (30+t)) =
        (timedState t (offPath z)).1 := by
  filter_upwards [V4.TwoPhaseLaw.completedSwitchLaw_ae_support x,
    ae_completed_switch_off_fold_coherent x] with z hs hc
  have hinit : coreProject (p := literalSourcePar 0) (switchState z.1) =
      coreProject (offRenewalInitial z.1.1) :=
    (LedgerOffsets.addLedgers_core (literalSourcePar 0) z.1.1.2
      (onOffset z.1 300) (fun _ => 0)).trans
      (source_reset_all_core (p := literalSourcePar 0) z.1.1.2).symm
  have hproj (n : ℕ) : coreProject (rawAt (literalSourcePar 0) (switchState z.1) (offPath z) n) =
      (offPath z n).2.1 :=
    (raw_at_core_congr recoveryValid (switchState z.1) (offRenewalInitial z.1.1)
      hinit (offPath z) n).trans (hc n)
  intro t ht
  have hraw := globalRaw_after_switch x z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 t ht
  exact (congrArg (fun y : Raw => coreProject (p := literalSourcePar 0) y) hraw).trans
    (rawSequence_timed_project (switchState z.1) (offPath z) hproj t)

end
end P161Formal
