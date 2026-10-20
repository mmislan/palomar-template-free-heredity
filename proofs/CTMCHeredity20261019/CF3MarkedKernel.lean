module

public import proofs.CTMCHeredity20261019.MarkedKernel
public import proofs.CTMCHeredity20261019.CF3Marked
public import proofs.CTMCHeredity20261019.CF3Copying
public import proofs.CTMCHeredity20261019.CF3RatePositive

@[expose] public section

/-!
# The actual CF3 finite-core timed labelled law

The physical generator, label intensities, and every labelled update are tied
to the original source for arbitrary q/nd ledgers. The actual exponential-clock
path law is then constructed on the finite core together with the last sampled
label. Both complementary daughters use one split; actual null-state operations
are retained. This does not yet reconstruct unbounded raw ledgers along paths,
identify a projected whole path law, or prove arbitrary operation stopping laws.
-/

namespace CTMCHeredity20261019.CF3MarkedKernel

open FunctionalCapacity MeasureTheory CF3Marked
open scoped BigOperators Classical
noncomputable section

/-- The physical core together with the most recently sampled proposal label. -/
abbrev State (p : Par) := CoreState p × Option (Mark p)

/-- The small source rate-positivity proof requires no historical mission module. -/
theorem rate_positive {p : Par} (hp : p.Valid) : 0 < cf3Rate p :=
  CF3RatePositive.rate_pos (by have := hp.hM; omega) hp.hα hp.hβ hp.hε

/-- Every raw-state label has the same intensity after forgetting q/nd. -/
theorem sourceIntensity_lump (p : Par) (x : SourceState p) (r : Mark p) :
    sourceIntensity p x r = sourceIntensity p (coreRepresent (coreProject x)) r := by
  cases r with
  | inl a => rfl
  | inr a =>
      rcases a with ⟨i, k, o, v⟩
      cases k <;> rfl

/-- Labelled intensity lumping, expressed directly between the two actual
minimal channel records. No stochastic law is hypothesized. -/
theorem core_source_propensity {p : Par} (hp : p.Valid)
    (x : SourceState p) (r : Mark p) :
    (coreChannels hp).propensity (coreProject x) r =
      (sourceChannels hp).propensity x r :=
  (sourceIntensity_lump p x r).symm

/-- Projecting each complete raw-state operation commutes with its core update,
including both simultaneous daughter installations and victim-ledger retention. -/
theorem sourceNext_project {p : Par} (hp : p.Valid)
    (x : SourceState p) (r : Mark p) :
    coreProject (sourceNext p x r) = (coreChannels hp).next (coreProject x) r := by
  cases r with
  | inl a =>
      rcases a with ⟨i, k⟩
      change coreProject (Function.update x i ((cf3 p).tc (x i) k)) =
        coreProject (Function.update (coreRepresent (coreProject x)) i
          ((cf3 p).tc ((coreRepresent (coreProject x)) i) k))
      simp only [coreProject_update, coreProject_represent, cf3_tc_core]
      rfl
  | inr a =>
      rcases a with ⟨i, k, o, v⟩
      change coreProject (divisionNext p x i k o v) =
        coreProject (divisionNext p (coreRepresent (coreProject x)) i k o v)
      simp only [divisionNext, coreProject_update, coreProject_represent,
        cf3_d1_core, cf3_d2_core, cf3_merge_core, cf3_td_core]
      rfl

/-- The explicit idle proposal also commutes with projection. -/
theorem proposalNext_project {p : Par} (hp : p.Valid)
    (x : SourceState p) (m : Option (Mark p)) :
    coreProject (MarkedUniformization.next (sourceChannels hp) x m) =
      MarkedUniformization.next (coreChannels hp) (coreProject x) m := by
  cases m with
  | none => rfl
  | some r => exact sourceNext_project hp x r

/-- The complete label weights, including idle, are source-derived and ledger
independent, rather than recovered from an unlabelled state matrix. -/
theorem proposalWeight_lump {p : Par} (hp : p.Valid) (Lam : ℝ)
    (x : SourceState p) (m : Option (Mark p)) :
    MarkedUniformization.weight (sourceChannels hp) Lam x m =
      MarkedUniformization.weight (coreChannels hp) Lam (coreProject x) m := by
  cases m with
  | none =>
      change 1 - (∑ r, sourceIntensity p x r) / Lam =
        1 - (∑ r, sourceIntensity p (coreRepresent (coreProject x)) r) / Lam
      have he : (∑ r, sourceIntensity p x r) =
          ∑ r, sourceIntensity p (coreRepresent (coreProject x)) r :=
        Finset.sum_congr rfl (fun r _ => sourceIntensity_lump p x r)
      rw [he]
  | some r =>
      change sourceIntensity p x r / Lam =
        sourceIntensity p (coreRepresent (coreProject x)) r / Lam
      rw [sourceIntensity_lump]

theorem core_channel_bound {p : Par} (hp : p.Valid) (x : CoreState p) :
    ∑ r, (coreChannels hp).propensity x r ≤ cf3Rate p :=
  sourceIntensity_bound hp (coreRepresent x)

/-- The concrete finite marked kernel uses the original actual marked envelope. -/
def kernel {p : Par} (hp : p.Valid) : HybridCTMC.Kernel (State p) :=
  MarkedKernel.kernel (coreChannels hp) (rate_positive hp) (core_channel_bound hp)

/-- Erasing the last mark in one-step observables gives exactly the independently
constructed uniformization of the original physical core generator. -/
theorem kernel_state_expect {p : Par} (hp : p.Valid)
    (f : CoreState p → ℝ) (z : State p) :
    (kernel hp).expect (fun y => f y.1) z =
      (uniformizedKernel (coreGen_isGen hp) (rate_positive hp) le_rfl).expect f z.1 := by
  rw [kernel, MarkedKernel.kernel_expect_state]
  exact core_expect_eq_uniformizedKernel hp (rate_positive hp) le_rfl f z.1

/-- The same erased expectation evaluated from any raw source state, with its
arbitrary q/nd ledger values carried by the exact source generator quotient. -/
theorem kernel_source_expect {p : Par} (hp : p.Valid)
    (f : CoreState p → ℝ) (x : SourceState p) (old : Option (Mark p)) :
    (kernel hp).expect (fun y => f y.1) (coreProject x, old) =
      f (coreProject x) + cf3Gen p (fun y => f (coreProject y)) x / cf3Rate p := by
  rw [kernel_state_expect, uniformizedKernel_expect, cf3Gen_lump]

/-- The next mark law on the finite quotient agrees with the actual source's
one-proposal law at every raw representative, not merely at zero ledgers. -/
theorem core_proposal_law_eq_source {p : Par} (hp : p.Valid) (x : SourceState p) :
    MarkedUniformization.law (coreChannels hp) (rate_positive hp)
        (core_channel_bound hp) (coreProject x) =
      sourceLaw hp (rate_positive hp) le_rfl x := by
  apply PMF.ext
  intro m
  simp only [sourceLaw, MarkedUniformization.law_apply]
  exact congrArg ENNReal.ofReal (proposalWeight_lump hp (cf3Rate p) x m).symm

/-! The finite state carries its ordinary discrete sigma algebra. These
instances are local to this file and do not alter other source measurability. -/
local instance (p : Par) : MeasurableSpace (State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (State p) := ⟨fun _ => trivial⟩

/-- The actual constructed exponential-clock measure on finite physical states
and retained marks, with the source's unchanged rate envelope. -/
def eventLaw {p : Par} (hp : p.Valid) (x : CoreState p) (old : Option (Mark p)) :
    Measure (ℕ → ℝ × State p) :=
  (kernel hp).eventLaw (cf3Rate p) (rate_positive hp) (x, old)

instance eventLaw_probability {p : Par} (hp : p.Valid)
    (x : CoreState p) (old : Option (Mark p)) :
    IsProbabilityMeasure (eventLaw hp x old) := by
  unfold eventLaw
  infer_instance

/-- Every actual adjacent proposal on this timed law applies the same labelled
CF3 update that was derived from the original full source. -/
theorem ae_event_actual_update {p : Par} (hp : p.Valid)
    (x : CoreState p) (old : Option (Mark p)) :
    ∀ᵐ w ∂eventLaw hp x old, ∀ n : ℕ,
      (w (n + 1)).2.1 =
        MarkedUniformization.next (coreChannels hp) (w n).2.1 (w (n + 1)).2.2 := by
  exact MarkedKernel.ae_event_adjacent_update (coreChannels hp)
    (rate_positive hp) (core_channel_bound hp) (x, old)

theorem canonical_valid : canonicalSeedFreeCF3.Valid := by
  constructor <;> norm_num [canonicalSeedFreeCF3]

theorem canonical_rate : cf3Rate canonicalSeedFreeCF3 = 93515792 := by
  norm_num [cf3Rate, canonicalSeedFreeCF3]

set_option maxHeartbeats 2000000 in
/-- Canonical beta4m, seed-free timed marked-law root. Initial catalyst counts,
fuel, and last-mark sentinel are arbitrary; no successful-path premise appears. -/
theorem canonical_ae_event_actual_update
    (x : CoreState canonicalSeedFreeCF3) (old : Option (Mark canonicalSeedFreeCF3)) :
    ∀ᵐ w ∂eventLaw canonical_valid x old, ∀ n : ℕ,
      (w (n + 1)).2.1 = MarkedUniformization.next
        (coreChannels canonical_valid) (w n).2.1 (w (n + 1)).2.2 :=
  ae_event_actual_update canonical_valid x old

end
end CTMCHeredity20261019.CF3MarkedKernel
