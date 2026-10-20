module

public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-!
# Actual finite-prefix next-proposal law carrying the original CF3 ledgers

The reconstructed raw state is measurable from a finite vector of sampled
marks. The actual finite marked event law supplies one-step prefix
disintegration. The source-derived equality of complete proposal weights then
identifies the next source-state/mark expectation at that reconstructed raw
state. No raw Markov or desired generator-law premise is assumed.

Signed prefix rewards are measurable and integrable, and next-source/mark
observables are bounded. Integrability is the analytic condition needed for
the real-valued expectation identity, not a stochastic bridge assumption.
No reset, switched mission, or random stopping-time statement is made.
-/

namespace CTMCHeredity20261019.CF3RawStepLaw

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory Preorder HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators Classical

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

abbrev Prefix (p : Par) (n : ℕ) := ∀ _ : Finset.Iic n, ℝ × CF3MarkedKernel.State p

def prefixMarks (p : Par) (n : ℕ) (u : Prefix p n) : Fin n → Option (Mark p) :=
  fun i => (u ⟨i.val + 1, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩).2.2

def prefixRaw (p : Par) (x : SourceState p) (n : ℕ) (u : Prefix p n) : SourceState p :=
  rawPrefixAt p x n (prefixMarks p n u)

theorem prefixRaw_frestrict (p : Par) (x : SourceState p) (n : ℕ) (w : MarkedPath p) :
    prefixRaw p x n (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
      rawAt p x w n := by
  rw [rawAt_eq_prefix]
  rfl

theorem measurable_prefixMarks (p : Par) (n : ℕ) : Measurable (prefixMarks p n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.2)).comp
    (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p)
      ⟨i.val + 1, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩).snd

/-- A next-source/mark observable is measurable here without imposing a raw
Markov law: its source input factors through the finite proposal prefix. -/
theorem measurable_prefix_nextReward (p : Par) (x : SourceState p) (n : ℕ)
    (g : SourceState p → Option (Mark p) → ℝ) :
    Measurable (fun z : Prefix p n × (ℝ × CF3MarkedKernel.State p) =>
      g (sourceProposalNext p (prefixRaw p x n z.1) z.2.2.2) z.2.2.2) := by
  let v : (Fin n → Option (Mark p)) × Option (Mark p) → ℝ := fun a =>
    g (sourceProposalNext p (rawPrefixAt p x n a.1) a.2) a.2
  have hv : Measurable v := measurable_of_countable _
  have hm : Measurable (fun z : Prefix p n × (ℝ × CF3MarkedKernel.State p) => z.2.2.2) :=
    (measurable_of_countable (fun a : CF3MarkedKernel.State p => a.2)).comp
      (measurable_snd.comp measurable_snd)
  exact hv.comp (((measurable_prefixMarks p n).comp measurable_fst).prodMk hm)

/-- Real-valued version of the actual source prefix-step disintegration. Its
integrability premise concerns the supplied reward, not a path law. -/
private theorem integral_prefix_step {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (z : S) (n : ℕ)
    (H : (∀ _ : Finset.Iic n, ℝ × S) × (ℝ × S) → ℝ) (hH : Measurable H)
    (hI : Integrable
      (fun w => H (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n + 1)))
      (K.eventLaw Lam hLam z)) :
    (∫ w, H (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n + 1))
      ∂K.eventLaw Lam hLam z) =
    ∫ u, ∫ a, H (u, a) ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
      ∂((K.eventLaw Lam hLam z).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let := K.eventKernel_markov hLam
  have hm : Measurable (fun w : ℕ → ℝ × S =>
      (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hi : Integrable H ((K.eventLaw Lam hLam z).map
      (fun w => (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, w (n + 1)))) :=
    (integrable_map_measure hH.aestronglyMeasurable hm.aemeasurable).mpr hI
  have hc : Integrable H
      ((K.eventLaw Lam hLam z).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n) ⊗ₘ
        K.eventKernel Lam n) := by
    rw [K.eventLaw_joint hLam z n]
    exact hi
  have h := Measure.integral_compProd hc
  rw [K.eventLaw_joint hLam z n, integral_map hm.aemeasurable hH.aestronglyMeasurable] at h
  exact h

/-- Integrating the actual source clock step leaves precisely the actual
normalized finite proposal-mark expectation, with no held-time premise. -/
theorem integral_clockStep_mark {p : Par} (hp : p.Valid)
    (z : CF3MarkedKernel.State p) (g : Option (Mark p) → ℝ) :
    (∫ a, g a.2.2 ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) z) =
      MarkedUniformization.expect (coreChannels hp) (cf3Rate p) z.1 g := by
  let := isProbabilityMeasure_expMeasure (CF3MarkedKernel.rate_positive hp)
  rw [HybridCTMC.Kernel.clockStep, integral_fun_snd (fun y : CF3MarkedKernel.State p => g y.2),
    probReal_univ, one_smul, HybridCTMC.Kernel.integral_pmf]
  exact MarkedKernel.kernel_expect_mark (coreChannels hp)
    (CF3MarkedKernel.rate_positive hp) (CF3MarkedKernel.core_channel_bound hp) g z

/-- Literal complete source proposal expectation, including natural-valued
output/division ledgers and the exact source update for each label. -/
def sourceStepValue {p : Par} (hp : p.Valid) (y : SourceState p)
    (g : SourceState p → Option (Mark p) → ℝ) : ℝ :=
  ∑ m, (sourceLaw hp (CF3MarkedKernel.rate_positive hp) le_rfl y m).toReal *
    g (sourceProposalNext p y m) m

/-- Keep the source PMF opaque: its already proved equality with the finite
core proposal law supplies every coefficient, including the idle label. -/
private theorem sourceLaw_probability_real {p : Par} (hp : p.Valid)
    (y : SourceState p) (m : Option (Mark p)) :
    (sourceLaw hp (CF3MarkedKernel.rate_positive hp) le_rfl y m).toReal =
      MarkedUniformization.weight (sourceChannels hp) (cf3Rate p) y m := by
  calc
    _ = (MarkedUniformization.law (coreChannels hp) (CF3MarkedKernel.rate_positive hp)
        (CF3MarkedKernel.core_channel_bound hp) (coreProject y) m).toReal :=
      congrArg (fun q : PMF (Option (Mark p)) => (q m).toReal)
        (CF3MarkedKernel.core_proposal_law_eq_source hp y).symm
    _ = MarkedUniformization.weight (coreChannels hp) (cf3Rate p) (coreProject y) m :=
      MarkedUniformization.law_apply_real (coreChannels hp)
        (CF3MarkedKernel.rate_positive hp) (CF3MarkedKernel.core_channel_bound hp) (coreProject y) m
    _ = _ := (CF3MarkedKernel.proposalWeight_lump hp (cf3Rate p) y m).symm

theorem core_expect_sourceStep {p : Par} (hp : p.Valid) (y : SourceState p)
    (g : SourceState p → Option (Mark p) → ℝ) :
    MarkedUniformization.expect (coreChannels hp) (cf3Rate p) (coreProject y)
      (fun m => g (sourceProposalNext p y m) m) = sourceStepValue hp y g := by
  simp only [sourceStepValue, MarkedUniformization.expect]
  apply Finset.sum_congr rfl
  intro m _
  rw [sourceLaw_probability_real hp y m,
    CF3MarkedKernel.proposalWeight_lump hp (cf3Rate p) y m]

/- Keep the finite input map separate from its value function. In particular,
measurability composition must not ask elaboration to discover the equality
between a recursive raw-prefix fold and that fold after a dependent projection. -/
private def prefixMarkState (p : Par) (n : ℕ) (u : Prefix p n) :
    (Fin n → Option (Mark p)) × CF3MarkedKernel.State p :=
  (prefixMarks p n u, (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)

private theorem measurable_prefixMarkState (p : Par) (n : ℕ) :
    Measurable (prefixMarkState p n) :=
  (measurable_prefixMarks p n).prodMk
    (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd

private def finitePrefixStepValue {p : Par} (hp : p.Valid) (x : SourceState p)
    (n : ℕ) (g : SourceState p → Option (Mark p) → ℝ)
    (a : (Fin n → Option (Mark p)) × CF3MarkedKernel.State p) : ℝ :=
  MarkedUniformization.expect (coreChannels hp) (cf3Rate p) a.2.1
    (fun m => g (sourceProposalNext p (rawPrefixAt p x n a.1) m) m)

private def corePrefixStep {p : Par} (hp : p.Valid) (x : SourceState p)
    (n : ℕ) (g : SourceState p → Option (Mark p) → ℝ) : Prefix p n → ℝ :=
  finitePrefixStepValue hp x n g ∘ prefixMarkState p n

private theorem measurable_corePrefixStep {p : Par} (hp : p.Valid) (x : SourceState p)
    (n : ℕ) (g : SourceState p → Option (Mark p) → ℝ) :
    Measurable (corePrefixStep hp x n g) := by
  have hv : Measurable (finitePrefixStepValue hp x n g) := measurable_of_countable _
  change Measurable (finitePrefixStepValue hp x n g ∘ prefixMarkState p n)
  exact hv.comp (measurable_prefixMarkState p n)

private theorem corePrefixStep_eq {p : Par} (hp : p.Valid) (x : SourceState p)
    (n : ℕ) (g : SourceState p → Option (Mark p) → ℝ) (u : Prefix p n) :
    corePrefixStep hp x n g u =
      MarkedUniformization.expect (coreChannels hp) (cf3Rate p)
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1
        (fun m => g (sourceProposalNext p (prefixRaw p x n u) m) m) := rfl

private theorem corePrefixStep_frestrict {p : Par} (hp : p.Valid) (x : SourceState p)
    (n : ℕ) (g : SourceState p → Option (Mark p) → ℝ) (w : MarkedPath p) :
    corePrefixStep hp x n g
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
      MarkedUniformization.expect (coreChannels hp) (cf3Rate p) (w n).2.1
        (fun m => g (sourceProposalNext p (rawAt p x w n) m) m) := by
  simpa only [prefixRaw_frestrict, frestrictLe_apply] using
    corePrefixStep_eq hp x n g
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w)

/- Scoped diagnostic budget after check143; typed helper declarations expose
any remaining elaboration hotspot. -/
set_option maxHeartbeats 400000 in
/-- Exact next-state/mark expectation against every measurable integrable
complete-prefix reward. The source one-proposal law is evaluated at the
reconstructed raw q/nd state, not at a zero-ledger representative. -/
theorem raw_next_prefix_expect {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (B : Prefix p n → ℝ) (hB : Measurable B)
    (hBI : Integrable B ((CF3MarkedKernel.eventLaw hp (coreProject x) old).map
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)))
    (g : SourceState p → Option (Mark p) → ℝ) (C : ℝ)
    (hbound : ∀ y m, |g y m| ≤ C) :
    (∫ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        g (rawAt p x w (n + 1)) (w (n + 1)).2.2
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
    ∫ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        sourceStepValue hp (rawAt p x w n) g
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
  let H : Prefix p n × (ℝ × CF3MarkedKernel.State p) → ℝ := fun z =>
    B z.1 * g (sourceProposalNext p (prefixRaw p x n z.1) z.2.2.2) z.2.2.2
  have hH : Measurable H :=
    (hB.comp measurable_fst).mul (measurable_prefix_nextReward p x n g)
  have hm : Measurable (fun w : MarkedPath p =>
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, w (n + 1))) :=
    (measurable_frestrictLe n).prodMk
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) (n + 1))
  have hBp : Integrable
      (fun w : MarkedPath p => B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w))
      (CF3MarkedKernel.eventLaw hp (coreProject x) old) :=
    hBI.comp_measurable (measurable_frestrictLe n)
  have hI : Integrable
      (fun w : MarkedPath p => H
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, w (n + 1)))
      (CF3MarkedKernel.eventLaw hp (coreProject x) old) := by
    apply (hBp.abs.mul_const C).mono' (hH.comp hm).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    dsimp only [H, Function.comp_def]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound _ _) (abs_nonneg _)
  have hq : Measurable (corePrefixStep hp x n g) :=
    measurable_corePrefixStep hp x n g
  have hinner (u : Prefix p n) :
      (∫ a, H (u, a) ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) =
      B u * corePrefixStep hp x n g u := by
    change (∫ a, B u * g (sourceProposalNext p (prefixRaw p x n u) a.2.2) a.2.2
      ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) = _
    rw [integral_const_mul]
    exact congrArg (fun r : ℝ => B u * r)
      ((integral_clockStep_mark hp (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        (fun m => g (sourceProposalNext p (prefixRaw p x n u) m) m)).trans
          (corePrefixStep_eq hp x n g u).symm)
  calc
    _ = ∫ w, H (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        w (n + 1)) ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => by
        simp only [H, prefixRaw_frestrict, rawAt_succ])
    _ = ∫ u, ∫ a, H (u, a)
        ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((CF3MarkedKernel.eventLaw hp (coreProject x) old).map
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)) :=
      integral_prefix_step (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
        (coreProject x, old) n H hH hI
    _ = ∫ u, B u * corePrefixStep hp x n g u
        ∂((CF3MarkedKernel.eventLaw hp (coreProject x) old).map
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = ∫ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        corePrefixStep hp x n g
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w)
        ∂CF3MarkedKernel.eventLaw hp (coreProject x) old :=
      integral_map (measurable_frestrictLe n).aemeasurable (hB.mul hq).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_rawAt_project hp x old] with w hw
      have hstate : (w n).2.1 = coreProject (rawAt p x w n) := (hw n).symm
      have hproject :
          MarkedUniformization.expect (coreChannels hp) (cf3Rate p) (w n).2.1
              (fun m => g (sourceProposalNext p (rawAt p x w n) m) m) =
            MarkedUniformization.expect (coreChannels hp) (cf3Rate p)
              (coreProject (rawAt p x w n))
              (fun m => g (sourceProposalNext p (rawAt p x w n) m) m) :=
        congrArg (fun s => MarkedUniformization.expect (coreChannels hp) (cf3Rate p) s
          (fun m => g (sourceProposalNext p (rawAt p x w n) m) m)) hstate
      have hvalue :
          corePrefixStep hp x n g
              (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
            sourceStepValue hp (rawAt p x w n) g :=
        (corePrefixStep_frestrict hp x n g w).trans
          (hproject.trans (core_expect_sourceStep hp (rawAt p x w n) g))
      exact congrArg (fun r : ℝ =>
        B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) * r) hvalue

/-- The actual raw source generator formula, now derived inside the exact
finite-prefix physical-law identity for bounded source observables. -/
theorem sourceStepValue_state {p : Par} (hp : p.Valid)
    (y : SourceState p) (f : SourceState p → ℝ) :
    sourceStepValue hp y (fun z _ => f z) = f y + cf3Gen p f y / cf3Rate p := by
  simp only [sourceStepValue, sourceLaw_probability_real]
  change MarkedUniformization.expect (sourceChannels hp) (cf3Rate p) y
    (fun m => f (sourceProposalNext p y m)) = _
  simp_rw [sourceProposalNext_eq hp]
  exact source_expect_next hp (cf3Rate p) f y

/-- Integrated next-event generator identity for the reconstructed original
q/nd source. This is derived from the actual marked event law and the source's
complete proposal update, not supplied as a raw Markov/generator hypothesis. -/
theorem raw_next_prefix_generator {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (n : ℕ) (B : Prefix p n → ℝ) (hB : Measurable B)
    (hBI : Integrable B ((CF3MarkedKernel.eventLaw hp (coreProject x) old).map
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)))
    (f : SourceState p → ℝ) (C : ℝ) (hbound : ∀ y, |f y| ≤ C) :
    (∫ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        f (rawAt p x w (n + 1)) ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
    ∫ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        (f (rawAt p x w n) + cf3Gen p f (rawAt p x w n) / cf3Rate p)
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
  simpa only [sourceStepValue_state] using
    raw_next_prefix_expect hp x old n B hB hBI (fun y _ => f y) C (fun y _ => hbound y)

end

end CTMCHeredity20261019.CF3RawStepLaw
