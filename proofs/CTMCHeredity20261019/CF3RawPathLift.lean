module

public import proofs.CTMCHeredity20261019.CF3MarkedKernel
public import proofs.CTMCHeredity20261019.PhysicalTimedCut

@[expose] public section

/-!
# Natural-valued CF3 source ledgers reconstructed from the actual sampled marks

The existing actual finite marked event law samples each complete physical
proposal label. Starting at an arbitrary original source state, this module
folds precisely those labels through the source's original complete update.
No ledger cap, reset, discarded state-null operation, or successful-path
premise is inserted. The same sampled holds are retained verbatim.

The lift is measurable because each finite raw state factors through a finite
prefix of sampled labels. Its pushforward is a constructed reconstruction
measure, and its core agrees with the sampled finite physical core almost
surely at every event and physical time. This does not assert a conditional
raw Markov/generator law, arbitrary stopped-counter theorem, or mission law.
-/

namespace CTMCHeredity20261019.CF3RawPathLift

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel CF3Marked
open scoped Classical

abbrev MarkedPath (p : Par) := ℕ → ℝ × CF3MarkedKernel.State p

/-- Only the explicit idle proposal leaves the source untouched by convention;
every actual label applies the complete original source update. -/
def sourceProposalNext (p : Par) (x : SourceState p) : Option (Mark p) → SourceState p
  | none => x
  | some r => sourceNext p x r

theorem sourceProposalNext_eq {p : Par} (hp : p.Valid) (x : SourceState p)
    (m : Option (Mark p)) :
    sourceProposalNext p x m = MarkedUniformization.next (sourceChannels hp) x m := by
  cases m <;> rfl

theorem sourceProposalNext_project {p : Par} (hp : p.Valid) (x : SourceState p)
    (m : Option (Mark p)) :
    coreProject (sourceProposalNext p x m) =
      MarkedUniformization.next (coreChannels hp) (coreProject x) m := by
  rw [sourceProposalNext_eq hp]
  exact CF3MarkedKernel.proposalNext_project hp x m

/-- Reconstruct the full original source state after n sampled proposals.
The coordinate-zero sentinel mark is never interpreted as an operation. -/
def rawAt (p : Par) (x : SourceState p) (w : MarkedPath p) : ℕ → SourceState p
  | 0 => x
  | n + 1 => sourceProposalNext p (rawAt p x w n) (w (n + 1)).2.2

@[simp] theorem rawAt_zero (p : Par) (x : SourceState p) (w : MarkedPath p) :
    rawAt p x w 0 = x := rfl

/-- This is the complete source update, including original q/nd changes and
victim-ledger retention, rather than a counter inferred from projected states. -/
@[simp] theorem rawAt_succ (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    rawAt p x w (n + 1) = sourceProposalNext p (rawAt p x w n) (w (n + 1)).2.2 := rfl

theorem rawAt_actual_mark (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (r : Mark p) (hr : (w (n + 1)).2.2 = some r) :
    rawAt p x w (n + 1) = sourceNext p (rawAt p x w n) r := by
  rw [rawAt_succ, hr]
  rfl

theorem rawAt_idle (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (hr : (w (n + 1)).2.2 = none) :
    rawAt p x w (n + 1) = rawAt p x w n := by
  rw [rawAt_succ, hr]
  rfl

/-- Exact deterministic core coherence under the existing sampled-update
relation. The actual source law will discharge both premises below. -/
theorem rawAt_project {p : Par} (hp : p.Valid) (x : SourceState p) (w : MarkedPath p)
    (hzero : (w 0).2.1 = coreProject x)
    (hstep : ∀ n : ℕ, (w (n + 1)).2.1 =
      MarkedUniformization.next (coreChannels hp) (w n).2.1 (w (n + 1)).2.2) :
    ∀ n : ℕ, coreProject (rawAt p x w n) = (w n).2.1 := by
  intro n
  induction n with
  | zero => exact hzero.symm
  | succ n ih =>
      rw [rawAt_succ, sourceProposalNext_project hp, ih]
      exact (hstep n).symm

/-- Reconstructed original source states with exactly the original sampled holds. -/
def rawSequence (p : Par) (x : SourceState p) (w : MarkedPath p) : ℕ → ℝ × SourceState p :=
  fun n => ((w n).1, rawAt p x w n)

@[simp] theorem rawSequence_hold (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    (rawSequence p x w n).1 = (w n).1 := rfl

@[simp] theorem rawSequence_arrivalTime (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    arrivalTime n (rawSequence p x w) = arrivalTime n w := rfl

@[simp] theorem rawSequence_clockIndex (p : Par) (x : SourceState p) (w : MarkedPath p) (T : ℝ) :
    clockIndex T (rawSequence p x w) = clockIndex T w := rfl

theorem rawSequence_timed_project {p : Par} (x : SourceState p) (w : MarkedPath p)
    (hproject : ∀ n : ℕ, coreProject (rawAt p x w n) = (w n).2.1) (T : ℝ) :
    coreProject (timedState T (rawSequence p x w)) = (timedState T w).1 := by
  change coreProject (rawAt p x w (clockIndex T (rawSequence p x w))) =
    (w (clockIndex T w)).2.1
  rw [rawSequence_clockIndex]
  exact hproject _

/-! The chosen sigma algebras are discrete on the source states and labels.
They are local and agree with the finite marked law's existing convention. -/
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

/-- The finite vector of all sampled proposal marks relevant to rawAt n. -/
def proposalPrefix (p : Par) (n : ℕ) (w : MarkedPath p) : Fin n → Option (Mark p) :=
  fun i => (w (i.val + 1)).2.2

/-- The same fold as rawAt, represented on a finite proposal-prefix carrier. -/
def rawPrefixAt (p : Par) (x : SourceState p) :
    (n : ℕ) → (Fin n → Option (Mark p)) → SourceState p
  | 0, _ => x
  | n + 1, m => sourceProposalNext p
      (rawPrefixAt p x n (fun i => m i.castSucc)) (m ⟨n, by omega⟩)

theorem rawAt_eq_prefix (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    rawAt p x w n = rawPrefixAt p x n (proposalPrefix p n w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change sourceProposalNext p (rawAt p x w n) (w (n + 1)).2.2 = _
      rw [ih]
      rfl

theorem measurable_proposalPrefix (p : Par) (n : ℕ) : Measurable (proposalPrefix p n) := by
  apply measurable_pi_iff.mpr
  intro i
  have hm : Measurable (fun z : ℝ × CF3MarkedKernel.State p => z.2.2) :=
    (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.2)).comp measurable_snd
  exact hm.comp (measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) (i.val + 1))

/-- No countable-state Markov construction is assumed: each raw state is a
measurable function of a finite carrier of sampled marks. -/
theorem measurable_rawAt (p : Par) (x : SourceState p) (n : ℕ) :
    Measurable (fun w : MarkedPath p => rawAt p x w n) := by
  have hf : Measurable (rawPrefixAt p x n) := measurable_of_countable _
  have he : (fun w : MarkedPath p => rawAt p x w n) =
      fun w => rawPrefixAt p x n (proposalPrefix p n w) := by
    funext w
    exact rawAt_eq_prefix p x w n
  rw [he]
  exact hf.comp (measurable_proposalPrefix p n)

theorem measurable_rawSequence (p : Par) (x : SourceState p) :
    Measurable (rawSequence p x) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n).fst.prodMk
    (measurable_rawAt p x n)

/-- The raw reconstruction measure is a measurable pushforward of the actual
finite timed marked law. No raw conditional-law property is part of this definition. -/
def rawLiftLaw {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p)) :
    Measure (ℕ → ℝ × SourceState p) :=
  (CF3MarkedKernel.eventLaw hp (coreProject x) old).map (rawSequence p x)

instance rawLiftLaw_probability {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) : IsProbabilityMeasure (rawLiftLaw hp x old) := by
  constructor
  rw [rawLiftLaw, Measure.map_apply (measurable_rawSequence p x) MeasurableSet.univ]
  simp

/-- The actual finite marked path supplies both hypotheses of rawAt_project. -/
theorem ae_rawAt_project {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ n : ℕ, coreProject (rawAt p x w n) = (w n).2.1 := by
  have hinit : ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      w 0 = (0, (coreProject x, old)) :=
    (CF3MarkedKernel.kernel hp).ae_event_initial (CF3MarkedKernel.rate_positive hp) (coreProject x, old)
  filter_upwards [hinit, CF3MarkedKernel.ae_event_actual_update hp (coreProject x) old] with w h0 hs
  apply rawAt_project hp x w _ hs
  rw [h0]

theorem ae_rawSequence_initial {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      rawSequence p x w 0 = (0, x) := by
  have hinit : ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      w 0 = (0, (coreProject x, old)) :=
    (CF3MarkedKernel.kernel hp).ae_event_initial (CF3MarkedKernel.rate_positive hp) (coreProject x, old)
  filter_upwards [hinit] with w h0
  change ((w 0).1, x) = (0, x)
  rw [h0]

/-- Core agreement holds simultaneously at every real physical time, using
the original source clockIndex/timedState definitions on the reconstructed path. -/
theorem ae_rawSequence_timed_project {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ T : ℝ, coreProject (timedState T (rawSequence p x w)) = (timedState T w).1 := by
  filter_upwards [ae_rawAt_project hp x old] with w hw
  intro T
  exact rawSequence_timed_project x w hw T

/-- No holding time is changed by the raw lift. The actual finite marked law's
positive holds and unbounded arrival clock therefore transfer without a new
raw nonexplosion hypothesis. Every raw state at a finite event index is an
ordinary original source state with natural-valued ledgers. -/
theorem ae_rawSequence_clock_regular {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (∀ n : ℕ, 0 < (rawSequence p x w (n + 1)).1) ∧
      (∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n (rawSequence p x w)) := by
  have hpos : ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ n : ℕ, 0 < (w (n + 1)).1 :=
    (CF3MarkedKernel.kernel hp).ae_holding_pos (CF3MarkedKernel.rate_positive hp) (coreProject x, old)
  have hclock : ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n w :=
    ae_arrivals_unbounded (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp) (coreProject x, old)
  filter_upwards [hpos, hclock] with w hpw hw
  constructor
  · exact hpw
  · simpa only [rawSequence_arrivalTime] using hw

/-- Concrete canonical post-withdrawal raw-ledger reconstruction from the
actual canonical finite marked law, with arbitrary initial natural ledgers. -/
theorem canonical_ae_rawAt_project
    (x : SourceState canonicalSeedFreeCF3) (old : Option (Mark canonicalSeedFreeCF3)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw CF3MarkedKernel.canonical_valid (coreProject x) old,
      ∀ n : ℕ, coreProject (rawAt canonicalSeedFreeCF3 x w n) = (w n).2.1 :=
  ae_rawAt_project CF3MarkedKernel.canonical_valid x old

end

end CTMCHeredity20261019.CF3RawPathLift
