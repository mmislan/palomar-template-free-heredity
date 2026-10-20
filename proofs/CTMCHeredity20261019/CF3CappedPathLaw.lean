module

public import proofs.CTMCHeredity20261019.CF3RawStepLaw
public import proofs.CTMCHeredity20261019.CF3Capped
public import proofs.CTMCHeredity20261019.EventIndexLaw

@[expose] public section

/-!
# The actual raw marked CF3 law has the capped source's whole timed path law

All raw q/nd updates are the original mark fold. We retain every sampled hold
and saturate only the state observation. The holding/next-cap transition law
is derived from the actual marked PMF and the source generator quotient.
Actual prefix disintegration then identifies every finite cylinder, and the
official square-cylinder uniqueness theorem identifies the entire path measure.
No projected conditional-law or raw Markov premise is assumed.
-/

namespace CTMCHeredity20261019.CF3CappedPathLaw

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) (Q D : ℕ) : MeasurableSpace (CappedState p Q D) := ⊤
local instance (p : Par) (Q D : ℕ) : MeasurableSingletonClass (CappedState p Q D) :=
  ⟨fun _ => trivial⟩

/-- Exactly the independently constructed finite capped source uniformization. -/
def cappedKernel {p : Par} (hp : p.Valid) (Q D : ℕ) : HybridCTMC.Kernel (CappedState p Q D) :=
  uniformizedKernel (cappedGen_isGen hp Q D) (CF3MarkedKernel.rate_positive hp) le_rfl

/-- The cap is applied to the actual original source update, including idle,
actual state-null labels, both complementary daughters, and external ledgers. -/
def markedCapNext (p : Par) (Q D : ℕ) (y : SourceState p)
    (z : CF3MarkedKernel.State p) : CappedState p Q D :=
  capProject Q D (sourceProposalNext p y z.2)

private theorem kernel_pmf_map_of_expect {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] (K : HybridCTMC.Kernel A) (H : HybridCTMC.Kernel B)
    (f : A → B) (a : A) (b : B)
    (h : ∀ g : B → ℝ, K.expect (fun z => g (f z)) a = H.expect g b) :
    (K.pmf a).map f = H.pmf b := by
  apply PMF.ext
  intro y
  have hm : (((K.pmf a).map f) y).toReal = K.expect (fun z => delta y (f z)) a := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp only [HybridCTMC.Kernel.expect, HybridCTMC.Kernel.pmf, PMF.ofFintype_apply,
        delta, mul_one, mul_zero, apply_ite, ENNReal.toReal_zero,
        ENNReal.toReal_ofReal (K.nonneg a _)]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : y = f z <;> simp [hz]
    · intro z _
      split_ifs
      · exact (K.pmf a).apply_ne_top z
      · exact ENNReal.zero_ne_top
  calc
    _ = ENNReal.ofReal ((((K.pmf a).map f) y).toReal) :=
      (ENNReal.ofReal_toReal (((K.pmf a).map f).apply_ne_top y)).symm
    _ = ENNReal.ofReal (K.expect (fun z => delta y (f z)) a) := congrArg ENNReal.ofReal hm
    _ = ENNReal.ofReal (H.expect (delta y) b) := congrArg ENNReal.ofReal (h (delta y))
    _ = H.pmf b y := by
      rw [kernel_expect_delta]
      rfl

/-- Complete next-cap distribution under the actual marked transition PMF.
The coefficients come from the source's complete proposal law at raw y. -/
theorem marked_pmf_capped {p : Par} (hp : p.Valid) (Q D : ℕ)
    (y : SourceState p) (old : Option (Mark p)) :
    ((CF3MarkedKernel.kernel hp).pmf (coreProject y, old)).map (markedCapNext p Q D y) =
      (cappedKernel hp Q D).pmf (capProject Q D y) := by
  apply kernel_pmf_map_of_expect
  intro f
  calc
    _ = MarkedUniformization.expect (coreChannels hp) (cf3Rate p) (coreProject y)
        (fun m => f (capProject Q D (sourceProposalNext p y m))) :=
      MarkedKernel.kernel_expect_mark (coreChannels hp) (CF3MarkedKernel.rate_positive hp)
        (CF3MarkedKernel.core_channel_bound hp) _ (coreProject y, old)
    _ = CF3RawStepLaw.sourceStepValue hp y (fun z _ => f (capProject Q D z)) :=
      CF3RawStepLaw.core_expect_sourceStep hp y (fun z _ => f (capProject Q D z))
    _ = f (capProject Q D y) + cf3Gen p (fun z => f (capProject Q D z)) y / cf3Rate p :=
      CF3RawStepLaw.sourceStepValue_state hp y (fun z => f (capProject Q D z))
    _ = _ := by
      rw [cappedKernel, uniformizedKernel_expect, cf3Gen_capped_lump]

/-- Joint holding-time/next-cap law. The exponential hold is retained verbatim;
the equality concerns actual probability measures, not only generators. -/
theorem clockStep_capped {p : Par} (hp : p.Valid) (Q D : ℕ)
    (y : SourceState p) (old : Option (Mark p)) :
    ((CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) (coreProject y, old)).map
        (Prod.map id (markedCapNext p Q D y)) =
      (cappedKernel hp Q D).clockStep (cf3Rate p) (capProject Q D y) := by
  let := isProbabilityMeasure_expMeasure (CF3MarkedKernel.rate_positive hp)
  have hf : Measurable (markedCapNext p Q D y) := measurable_of_countable _
  change (((expMeasure (cf3Rate p)).prod
      ((CF3MarkedKernel.kernel hp).pmf (coreProject y, old)).toMeasure).map
        (Prod.map id (markedCapNext p Q D y))) =
    (expMeasure (cf3Rate p)).prod ((cappedKernel hp Q D).pmf (capProject Q D y)).toMeasure
  rw [← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id,
    PMF.toMeasure_map (markedCapNext p Q D y) _ hf, marked_pmf_capped hp Q D y old]

/-- The entire reconstructed original source sequence, observed through caps. -/
def cappedSequence (p : Par) (x : SourceState p) (Q D : ℕ) (w : MarkedPath p) :
    ℕ → ℝ × CappedState p Q D :=
  fun n => ((w n).1, capProject Q D (rawAt p x w n))

theorem measurable_cappedAt (p : Par) (x : SourceState p) (Q D n : ℕ) :
    Measurable (fun w : MarkedPath p => capProject Q D (rawAt p x w n)) := by
  let v : (Fin n → Option (Mark p)) → CappedState p Q D :=
    fun a => capProject Q D (rawPrefixAt p x n a)
  have hv : Measurable v := measurable_of_countable _
  have he : (fun w : MarkedPath p => capProject Q D (rawAt p x w n)) =
      v ∘ proposalPrefix p n := by
    funext w
    exact congrArg (capProject Q D) (rawAt_eq_prefix p x w n)
  rw [he]
  exact hv.comp (measurable_proposalPrefix p n)

theorem measurable_cappedSequence (p : Par) (x : SourceState p) (Q D : ℕ) :
    Measurable (cappedSequence p x Q D) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n).fst.prodMk
    (measurable_cappedAt p x Q D n)

/-- A finite-prefix capped state factors through the finite sampled label vector. -/
private theorem measurable_capPrefixRaw (p : Par) (x : SourceState p) (Q D n : ℕ) :
    Measurable (fun u : CF3RawStepLaw.Prefix p n =>
      capProject Q D (CF3RawStepLaw.prefixRaw p x n u)) := by
  let v : (Fin n → Option (Mark p)) → CappedState p Q D :=
    fun a => capProject Q D (rawPrefixAt p x n a)
  have hv : Measurable v := measurable_of_countable _
  change Measurable (v ∘ CF3RawStepLaw.prefixMarks p n)
  exact hv.comp (CF3RawStepLaw.measurable_prefixMarks p n)

private theorem measurable_prefix_nextCap (p : Par) (x : SourceState p) (Q D n : ℕ) :
    Measurable (fun z : CF3RawStepLaw.Prefix p n × (ℝ × CF3MarkedKernel.State p) =>
      capProject Q D (sourceProposalNext p (CF3RawStepLaw.prefixRaw p x n z.1) z.2.2.2)) := by
  let v : (Fin n → Option (Mark p)) × Option (Mark p) → CappedState p Q D := fun a =>
    capProject Q D (sourceProposalNext p (rawPrefixAt p x n a.1) a.2)
  have hv : Measurable v := measurable_of_countable _
  have hm : Measurable (fun z : CF3RawStepLaw.Prefix p n × (ℝ × CF3MarkedKernel.State p) =>
      z.2.2.2) :=
    (measurable_of_countable (fun a : CF3MarkedKernel.State p => a.2)).comp
      (measurable_snd.comp measurable_snd)
  exact hv.comp (((CF3RawStepLaw.measurable_prefixMarks p n).comp measurable_fst).prodMk hm)

/-- The actual complete-prefix law of the next holding time and capped raw
state. The source current state is the mark fold, with arbitrary raw ledgers. -/
theorem capped_next_prefix_lintegral {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D n : ℕ)
    (B : CF3RawStepLaw.Prefix p n → ℝ≥0∞) (hB : Measurable B)
    (F : ℝ × CappedState p Q D → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        F (cappedSequence p x Q D w (n + 1))
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) *
        (∫⁻ z, F z ∂(cappedKernel hp Q D).clockStep (cf3Rate p)
          (capProject Q D (rawAt p x w n)))
        ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
  let H : CF3RawStepLaw.Prefix p n × (ℝ × CF3MarkedKernel.State p) → ℝ≥0∞ := fun z =>
    B z.1 * F (z.2.1,
      capProject Q D (sourceProposalNext p (CF3RawStepLaw.prefixRaw p x n z.1) z.2.2.2))
  have hH : Measurable H :=
    (hB.comp measurable_fst).mul (hF.comp
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_prefix_nextCap p x Q D n)))
  let := (CF3MarkedKernel.kernel hp).eventKernel_markov (CF3MarkedKernel.rate_positive hp) n
  have hq : Measurable (fun u : CF3RawStepLaw.Prefix p n =>
      ∫⁻ a, H (u, a) ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) := by
    change Measurable (fun u => ∫⁻ a, H (u, a)
      ∂(CF3MarkedKernel.kernel hp).eventKernel (cf3Rate p) n u)
    exact hH.lintegral_kernel_prod_right'
  calc
    _ = ∫⁻ w, H (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w,
        w (n + 1)) ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
      apply lintegral_congr
      intro w
      dsimp only [H, cappedSequence]
      rw [CF3RawStepLaw.prefixRaw_frestrict, rawAt_succ]
    _ = ∫⁻ u, ∫⁻ a, H (u, a) ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((CF3MarkedKernel.eventLaw hp (coreProject x) old).map
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n)) :=
      (CF3MarkedKernel.kernel hp).eventLaw_lintegral_prefix_step
        (CF3MarkedKernel.rate_positive hp) (coreProject x, old) n H hH
    _ = ∫⁻ w, ∫⁻ a, H
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, a)
        ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) (w n).2
        ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
      exact lintegral_map hq (measurable_frestrictLe n)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_rawAt_project hp x old] with w hw
      let y : SourceState p := rawAt p x w n
      let m : Option (Mark p) := (w n).2.2
      let b : ℝ≥0∞ := B
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w)
      let φ : (ℝ × CF3MarkedKernel.State p) → ℝ × CappedState p Q D :=
        Prod.map id (markedCapNext p Q D y)
      have hφ : Measurable φ := measurable_id.prodMap (measurable_of_countable _)
      have hpair : (w n).2 = (coreProject y, m) := Prod.ext (hw n).symm rfl
      have hmeasure : (CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) (w n).2 =
          (CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) (coreProject y, m) :=
        congrArg ((CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)) hpair
      have hfun : (fun a => H
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, a)) =
          fun a => b * F (φ a) := by
        funext a
        dsimp only [H, b, φ, Prod.map, id_eq, markedCapNext, y]
        rw [CF3RawStepLaw.prefixRaw_frestrict]
      have hclock :
          (∫⁻ a, F (φ a) ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p)
            (coreProject y, m)) =
            ∫⁻ z, F z ∂(cappedKernel hp Q D).clockStep (cf3Rate p) (capProject Q D y) := by
        rw [← lintegral_map hF hφ]
        exact congrArg (fun μ : Measure (ℝ × CappedState p Q D) => ∫⁻ z, F z ∂μ)
          (clockStep_capped hp Q D y m)
      change (∫⁻ a, H
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w, a)
        ∂(CF3MarkedKernel.kernel hp).clockStep (cf3Rate p) (w n).2) = _
      rw [hfun, hmeasure,
        lintegral_const_mul (f := fun a : ℝ × CF3MarkedKernel.State p => F (φ a)) b (hF.comp hφ),
        hclock]

/-- All capped prefix coordinates are computed from only the matching sampled
mark prefix, never from future marks. -/
private def cappedPrefix (p : Par) (x : SourceState p) (Q D n : ℕ)
    (u : CF3RawStepLaw.Prefix p n) : EventPrefix (CappedState p Q D) n := fun i =>
  ((u i).1, capProject Q D (CF3RawStepLaw.prefixRaw p x i.val
    (frestrictLe₂ (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p)
      (Finset.mem_Iic.mp i.property) u)))

private theorem measurable_cappedPrefix (p : Par) (x : SourceState p) (Q D n : ℕ) :
    Measurable (cappedPrefix p x Q D n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p) i).fst.prodMk
    ((measurable_capPrefixRaw p x Q D i.val).comp
      (measurable_frestrictLe₂ (Finset.mem_Iic.mp i.property)))

private theorem cappedPrefix_frestrict (p : Par) (x : SourceState p) (Q D n : ℕ)
    (w : MarkedPath p) :
    cappedPrefix p x Q D n
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
      frestrictLe (π := fun _ : ℕ => ℝ × CappedState p Q D) n (cappedSequence p x Q D w) := by
  funext i
  change ((w i.val).1, capProject Q D (CF3RawStepLaw.prefixRaw p x i.val
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) i.val w))) =
    ((w i.val).1, capProject Q D (rawAt p x w i.val))
  rw [CF3RawStepLaw.prefixRaw_frestrict]

private def cappedPastWeight (p : Par) (x : SourceState p) (Q D n : ℕ)
    (f : ℕ → ℝ × CappedState p Q D → ℝ≥0∞)
    (u : CF3RawStepLaw.Prefix p n) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, if hi : i + 1 ≤ n then
    f i (cappedPrefix p x Q D n u ⟨i + 1, Finset.mem_Iic.mpr hi⟩) else 1

private theorem measurable_cappedPastWeight (p : Par) (x : SourceState p) (Q D n : ℕ)
    (f : ℕ → ℝ × CappedState p Q D → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (cappedPastWeight p x Q D n f) := by
  unfold cappedPastWeight
  apply Finset.measurable_prod
  intro i hi
  have hin : i + 1 ≤ n := by have := Finset.mem_range.mp hi; omega
  simp only [dite_eq_left hin]
  exact (hf i).comp ((measurable_pi_apply
    (X := fun _ : Finset.Iic n => ℝ × CappedState p Q D)
    ⟨i + 1, Finset.mem_Iic.mpr hin⟩).comp (measurable_cappedPrefix p x Q D n))

private theorem cappedPastWeight_frestrict (p : Par) (x : SourceState p) (Q D n : ℕ)
    (f : ℕ → ℝ × CappedState p Q D → ℝ≥0∞) (w : MarkedPath p) :
    cappedPastWeight p x Q D n f
        (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w) =
      futureCylinderWeight 0 n f (cappedSequence p x Q D w) := by
  unfold cappedPastWeight futureCylinderWeight
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i + 1 ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [dite_eq_left hin, cappedPrefix_frestrict]
  simp only [frestrictLe_apply, Nat.zero_add]

/-- Every finite holding-time/capped-state cylinder has the independently
constructed capped kernel's actual recursion. This is proved by eliminating
the last sampled proposal using the actual marked prefix law. -/
theorem capped_futureCylinder_value {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D k : ℕ)
    (f : ℕ → ℝ × CappedState p Q D → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (g : CappedState p Q D → ℝ≥0∞) :
    (∫⁻ w, futureCylinderWeight 0 k f (cappedSequence p x Q D w) *
        g (capProject Q D (rawAt p x w k))
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      futureCylinderValue (cappedKernel hp Q D) (cf3Rate p) f k g (capProject Q D x) := by
  induction k generalizing g with
  | zero => simp [futureCylinderWeight, futureCylinderValue]
  | succ k ih =>
    let q : CappedState p Q D → ℝ≥0∞ := fun y =>
      ∫⁻ z, f k z * g z.2 ∂(cappedKernel hp Q D).clockStep (cf3Rate p) y
    have hF : Measurable (fun z : ℝ × CappedState p Q D => f k z * g z.2) :=
      (hf k).mul ((measurable_of_countable g).comp measurable_snd)
    have hs := capped_next_prefix_lintegral hp x old Q D k
      (cappedPastWeight p x Q D k f) (measurable_cappedPastWeight p x Q D k f hf)
      (fun z => f k z * g z.2) hF
    calc
      _ = ∫⁻ w, cappedPastWeight p x Q D k f
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) k w) *
          (f k (cappedSequence p x Q D w (k + 1)) *
            g (cappedSequence p x Q D w (k + 1)).2)
          ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
        apply lintegral_congr
        intro w
        rw [cappedPastWeight_frestrict, futureCylinderWeight_succ]
        simp only [Nat.zero_add, cappedSequence, mul_assoc]
      _ = ∫⁻ w, cappedPastWeight p x Q D k f
          (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) k w) *
          q (capProject Q D (rawAt p x w k))
          ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := hs
      _ = ∫⁻ w, futureCylinderWeight 0 k f (cappedSequence p x Q D w) *
          q (capProject Q D (rawAt p x w k))
          ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
        apply lintegral_congr
        intro w
        rw [cappedPastWeight_frestrict]
      _ = futureCylinderValue (cappedKernel hp Q D) (cf3Rate p) f k q (capProject Q D x) := ih q
      _ = _ := rfl

/-- Coordinate zero has the same zero hold and actual capped initial state in
the raw marked lift and the independent capped construction. -/
theorem ae_cappedSequence_initial {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D : ℕ) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      cappedSequence p x Q D w 0 = (0, capProject Q D x) := by
  have hi := (CF3MarkedKernel.kernel hp).ae_event_initial
    (CF3MarkedKernel.rate_positive hp) (coreProject x, old)
  filter_upwards [hi] with w hw
  change ((w 0).1, capProject Q D x) = (0, capProject Q D x)
  rw [hw]

/-- Full finite cylinders, including the actual coordinate-zero convention. -/
theorem capped_fullCylinder {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D k : ℕ)
    (b : ℕ → ℝ × CappedState p Q D → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) :
    (∫⁻ w, fullCylinderWeight (k + 1) b (cappedSequence p x Q D w)
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∫⁻ v, fullCylinderWeight (k + 1) b v
        ∂(cappedKernel hp Q D).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (capProject Q D x) := by
  let f : ℕ → ℝ × CappedState p Q D → ℝ≥0∞ := fun i => b (i + 1)
  have hf : ∀ i, Measurable (f i) := fun i => hb (i + 1)
  have hs := capped_futureCylinder_value hp x old Q D k f hf (fun _ => 1)
  have ht := eventLaw_futureCylinder_value (cappedKernel hp Q D)
    (CF3MarkedKernel.rate_positive hp) (capProject Q D x) k f hf (fun _ => 1)
  simp only [mul_one] at hs ht
  have he :
      (∫⁻ w, fullCylinderWeight (k + 1) b (cappedSequence p x Q D w)
        ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
        b 0 (0, capProject Q D x) *
          ∫⁻ w, futureCylinderWeight 0 k f (cappedSequence p x Q D w)
            ∂CF3MarkedKernel.eventLaw hp (coreProject x) old := by
    have hae :
        (fun w => fullCylinderWeight (k + 1) b (cappedSequence p x Q D w)) =ᵐ[
          CF3MarkedKernel.eventLaw hp (coreProject x) old]
        fun w => b 0 (0, capProject Q D x) *
          futureCylinderWeight 0 k f (cappedSequence p x Q D w) := by
      filter_upwards [ae_cappedSequence_initial hp x old Q D] with w hw
      rw [fullCylinderWeight_succ, hw]
    rw [lintegral_congr_ae hae, lintegral_const_mul
      (f := fun w : MarkedPath p => futureCylinderWeight 0 k f (cappedSequence p x Q D w)) _
      ((measurable_futureCylinderWeight 0 k f hf).comp (measurable_cappedSequence p x Q D))]
  have hte :
      (∫⁻ v, fullCylinderWeight (k + 1) b v
        ∂(cappedKernel hp Q D).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (capProject Q D x)) =
        b 0 (0, capProject Q D x) *
          ∫⁻ v, futureCylinderWeight 0 k f v
            ∂(cappedKernel hp Q D).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
              (capProject Q D x) := by
    have hae : (fun v => fullCylinderWeight (k + 1) b v) =ᵐ[
        (cappedKernel hp Q D).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
          (capProject Q D x)]
        fun v => b 0 (0, capProject Q D x) * futureCylinderWeight 0 k f v := by
      filter_upwards [(cappedKernel hp Q D).ae_event_initial
        (CF3MarkedKernel.rate_positive hp) (capProject Q D x)] with v hv
      rw [fullCylinderWeight_succ, hv]
    rw [lintegral_congr_ae hae, lintegral_const_mul _ (measurable_futureCylinderWeight 0 k f hf)]
  exact he.trans ((congrArg (fun r : ℝ≥0∞ => b 0 (0, capProject Q D x) * r)
    (hs.trans ht.symm)).trans hte.symm)

/-- The actual timed marked CF3 law, after the original raw mark fold and
finite q/nd saturation, is exactly the separately constructed capped source
eventLaw on the entire infinite holding-time/state sequence. -/
theorem eventLaw_cappedSequence {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D : ℕ) :
    (CF3MarkedKernel.eventLaw hp (coreProject x) old).map (cappedSequence p x Q D) =
      (uniformizedKernel (cappedGen_isGen hp Q D) (CF3MarkedKernel.rate_positive hp) le_rfl).eventLaw
        (cf3Rate p) (CF3MarkedKernel.rate_positive hp) (capProject Q D x) := by
  let μ := (CF3MarkedKernel.eventLaw hp (coreProject x) old).map (cappedSequence p x Q D)
  let ν := (cappedKernel hp Q D).eventLaw (cf3Rate p) (CF3MarkedKernel.rate_positive hp)
    (capProject Q D x)
  let : IsFiniteMeasure μ := by unfold μ; infer_instance
  have hbox (I : Finset ℕ) (t : ℕ → Set (ℝ × CappedState p Q D))
      (ht : ∀ i, MeasurableSet (t i)) : μ ((I : Set ℕ).pi t) = ν ((I : Set ℕ).pi t) := by
    let b : ℕ → ℝ × CappedState p Q D → ℝ≥0∞ := fun i z =>
      if i ∈ I then (if z ∈ t i then 1 else 0) else 1
    have hb (i : ℕ) : Measurable (b i) := by
      by_cases hi : i ∈ I
      · simp only [b, hi, ite_true]
        exact Measurable.ite (ht i) measurable_const measurable_const
      · simpa only [b, hi, ite_false] using
          (measurable_const : Measurable (fun _ : ℝ × CappedState p Q D => (1 : ℝ≥0∞)))
    have hm := measurable_fullCylinderWeight (I.sup id + 2) b hb
    have hset : MeasurableSet ((I : Set ℕ).pi t) :=
      MeasurableSet.pi I.countable_toSet (fun i _ => ht i)
    have he : fullCylinderWeight (I.sup id + 2) b =
        ((I : Set ℕ).pi t).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext v
      exact paddedBoxWeight_indicator I t v
    calc
      _ = ∫⁻ v, fullCylinderWeight (I.sup id + 2) b v ∂μ := by
        rw [he, lintegral_indicator hset]
        simp
      _ = ∫⁻ w, fullCylinderWeight (I.sup id + 2) b (cappedSequence p x Q D w)
          ∂CF3MarkedKernel.eventLaw hp (coreProject x) old :=
        lintegral_map hm (measurable_cappedSequence p x Q D)
      _ = ∫⁻ v, fullCylinderWeight (I.sup id + 2) b v ∂ν := by
        simpa only [Nat.add_assoc] using
          capped_fullCylinder hp x old Q D (I.sup id + 1) b hb
      _ = _ := by rw [he, lintegral_indicator hset]; simp
  change μ = ν
  apply ext_of_generate_finite
    (squareCylinders (fun _ : ℕ => {s : Set (ℝ × CappedState p Q D) | MeasurableSet s}))
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (by
        intro i
        change MeasurableSet (Set.univ : Set (ℝ × CappedState p Q D))
        exact MeasurableSet.univ))
  · rintro C ⟨I, t, ht, rfl⟩
    exact hbox I t (fun i => ht i (mem_univ i))
  · simp

/-- Reward form for every measurable event or observable of the whole capped
holding-time/state sequence, not only a chosen finite collection of endpoints. -/
theorem eventLaw_cappedSequence_lintegral {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D : ℕ)
    (F : (ℕ → ℝ × CappedState p Q D) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (cappedSequence p x Q D w)
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∫⁻ v, F v
        ∂(uniformizedKernel (cappedGen_isGen hp Q D) (CF3MarkedKernel.rate_positive hp) le_rfl).eventLaw
          (cf3Rate p) (CF3MarkedKernel.rate_positive hp) (capProject Q D x) := by
  rw [← lintegral_map hF (measurable_cappedSequence p x Q D),
    eventLaw_cappedSequence hp x old Q D]

@[simp] theorem cappedSequence_arrivalTime (p : Par) (x : SourceState p) (Q D : ℕ)
    (w : MarkedPath p) (n : ℕ) :
    arrivalTime n (cappedSequence p x Q D w) = arrivalTime n w := rfl

@[simp] theorem cappedSequence_clockIndex (p : Par) (x : SourceState p) (Q D : ℕ)
    (w : MarkedPath p) (T : ℝ) :
    clockIndex T (cappedSequence p x Q D w) = clockIndex T w := rfl

/-- Physical-time observation of the capped sequence is exactly the cap of
the same raw marked lift at the same physical clock index. -/
theorem cappedSequence_timedState (p : Par) (x : SourceState p) (Q D : ℕ)
    (w : MarkedPath p) (T : ℝ) :
    timedState T (cappedSequence p x Q D w) =
      capProject Q D (timedState T (rawSequence p x w)) := rfl

/-- The very same sampled path has positive holds and an unbounded clock
before and after observing the caps; no new nonexplosion premise is used. -/
theorem ae_cappedSequence_clock_regular {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (Q D : ℕ) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (∀ n : ℕ, 0 < (cappedSequence p x Q D w (n + 1)).1) ∧
      (∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n (cappedSequence p x Q D w)) := by
  filter_upwards [ae_rawSequence_clock_regular hp x old] with w hw
  exact hw

/-- Canonical beta4m seed-withdrawn source, retaining arbitrary initial raw
q/nd ledgers. Caps change only observations and do not alter the source path. -/
theorem canonical_eventLaw_cappedSequence (x : SourceState canonicalSeedFreeCF3)
    (old : Option (Mark canonicalSeedFreeCF3)) (Q D : ℕ) :
    (CF3MarkedKernel.eventLaw CF3MarkedKernel.canonical_valid (coreProject x) old).map
        (cappedSequence canonicalSeedFreeCF3 x Q D) =
      (uniformizedKernel (cappedGen_isGen CF3MarkedKernel.canonical_valid Q D)
        (CF3MarkedKernel.rate_positive CF3MarkedKernel.canonical_valid) le_rfl).eventLaw
          (cf3Rate canonicalSeedFreeCF3)
          (CF3MarkedKernel.rate_positive CF3MarkedKernel.canonical_valid) (capProject Q D x) :=
  eventLaw_cappedSequence CF3MarkedKernel.canonical_valid x old Q D

end

end CTMCHeredity20261019.CF3CappedPathLaw
