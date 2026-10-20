module

public import proofs.CTMCHeredity20261019.SourceBlockAmbient
public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import proofs.CTMCHeredity20261019.CF3CappedPathLaw
public import proofs.CTMCHeredity20261019.V2.RawOperated
public import proofs.CTMCHeredity20261019.V2.NoBoundaryArrival

@[expose] public section

/-!
# Canonical deterministic seed withdrawal: two actual source phases

This versioned successor composes the actual raw marked source law with
epsilon=6 before physical time 30 and epsilon=0 afterwards. The deterministic
boundary operation clears output/division bookkeeping only. Counts and the
physical fuel bit are unchanged, and no stock is replenished. Each phase
retains its complete sampled marks and holds, including state-null operations.

The common-clock seed-erasure proposal-history construction is a separately
owned P161Formal branch. No equality with that primitive proposal history, or
with an unchanged homogeneous whole path after intervention, is asserted here.
The numerical mission bound, recovery stops, and finite-stock tails remain
separate obligations.
-/

namespace CTMCHeredity20261019.V2.SeedSwitch

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical
noncomputable section

/-- The canonical source before withdrawal, with the literal seed coefficient 6. -/
def canonicalSeedOnCF3 : Par := ⟨4, 3, 2048, 800, 4000000, 6⟩

abbrev seedOff : Par := canonicalSeedFreeCF3
abbrev Raw := SourceState seedOff
abbrev Marks := Mark seedOff

theorem seedOn_valid : canonicalSeedOnCF3.Valid := by
  constructor <;> norm_num [canonicalSeedOnCF3]

theorem seedOn_rate : cf3Rate canonicalSeedOnCF3 = 93515864 := by
  norm_num [cf3Rate, canonicalSeedOnCF3]

theorem seedOn_clock_pos : (0 : ℝ) < 93515864 := by norm_num

theorem seedOff_rate : cf3Rate seedOff = 93515792 := canonicalSeedFree_rate

/-- The two parameter records have literally the same full raw state carrier. -/
theorem source_carrier_same : SourceState canonicalSeedOnCF3 = Raw := rfl

/-- Complete channel/split/victim marks have the same carrier in both phases. -/
theorem mark_carrier_same : Mark canonicalSeedOnCF3 = Marks := rfl

theorem marked_path_carrier_same : MarkedPath canonicalSeedOnCF3 = MarkedPath seedOff := rfl

theorem divisionNext_same (x : Raw) (i : Fin 4) (k : Option (Fin 3))
    (o : Split 3 2048) (v : Fin 4) :
    divisionNext canonicalSeedOnCF3 x i k o v = divisionNext seedOff x i k o v := by
  cases k <;> rfl

theorem chemical_update_same (s : Site 3 2048) (k : Chem 3) :
    (cf3 canonicalSeedOnCF3).tc s k = (cf3 seedOff).tc s k := by
  cases k with
  | inl a => rcases a with ⟨t, j⟩; rfl
  | inr b => cases b <;> rfl

/-- The withdrawal changes propensities, not the physical update of any label.
In particular both daughters share the same split and the same victim. -/
theorem sourceNext_same (x : Raw) (r : Marks) :
    sourceNext canonicalSeedOnCF3 x r = sourceNext seedOff x r := by
  cases r with
  | inl a =>
      rcases a with ⟨i, k⟩
      exact congrArg (Function.update x i) (chemical_update_same (x i) k)
  | inr a =>
      rcases a with ⟨i, k, o, v⟩
      exact divisionNext_same x i k o v

theorem sourceProposalNext_same (x : Raw) (r : Option Marks) :
    sourceProposalNext canonicalSeedOnCF3 x r = sourceProposalNext seedOff x r := by
  cases r with
  | none => rfl
  | some r => exact sourceNext_same x r

theorem division_rate_same (s : Site 3 2048) (k : Option (Fin 3)) :
    (cf3 canonicalSeedOnCF3).rd s k = (cf3 seedOff).rd s k := by
  cases k <;> rfl

theorem division_split_law_same (s : Site 3 2048) (o : Split 3 2048) :
    (cf3 canonicalSeedOnCF3).ps s o = (cf3 seedOff).ps s o := rfl

theorem source_seed_rate_on (x : Raw) (i : Fin 4) (j : Fin 3) :
    sourceIntensity canonicalSeedOnCF3 x (Sum.inl (i, Sum.inl (0, j))) =
      6 * (1 - (x i).u j) := by
  norm_num [sourceIntensity, cf3, canonicalSeedOnCF3, Site.u, seedOff,
    canonicalSeedFreeCF3]

/-- The actual source seed channel has zero rate after the deterministic switch. -/
theorem source_seed_rate_off (x : Raw) (i : Fin 4) (j : Fin 3) :
    sourceIntensity seedOff x (Sum.inl (i, Sum.inl (0, j))) = 0 := by
  simp [sourceIntensity, cf3, seedOff, canonicalSeedFreeCF3]

/-- Every other chemical propensity is unchanged by withdrawal. -/
theorem chemical_nonseed_rate_same (s : Site 3 2048) (k : Chem 3)
    (hk : ∀ j : Fin 3, k ≠ Sum.inl (0, j)) :
    (cf3 canonicalSeedOnCF3).rc s k = (cf3 seedOff).rc s k := by
  cases k with
  | inl a =>
      rcases a with ⟨t, j⟩
      have ht : t ≠ 0 := fun ht => hk j (by rw [ht])
      simp [cf3, ht, canonicalSeedOnCF3, seedOff, canonicalSeedFreeCF3]
  | inr b => cases b <;> rfl

theorem division_intensity_same (x : Raw) (i : Fin 4) (k : Option (Fin 3))
    (o : Split 3 2048) (v : Fin 4) :
    sourceIntensity canonicalSeedOnCF3 x (Sum.inr (i, (k, (o, v)))) =
      sourceIntensity seedOff x (Sum.inr (i, (k, (o, v)))) := by
  cases k <;> rfl

/-- The protected old species are exactly indices 0 and 1. -/
def oldSpecies : Finset (Fin 3) := {0, 1}

def allSpecies : Finset (Fin 3) := Finset.univ

theorem oldSpecies_iff (j : Fin 3) : j ∈ oldSpecies ↔ j.val < 2 := by
  fin_cases j <;> norm_num [oldSpecies]

theorem oldSpecies_nonempty : oldSpecies.Nonempty := by
  exact ⟨0, by simp [oldSpecies]⟩

theorem allSpecies_nonempty : allSpecies.Nonempty := by
  exact ⟨0, Finset.mem_univ _⟩

/-- Initial and switch resets affect only external bookkeeping. -/
theorem resetAll_physical (x : Raw) (i : Fin 4) :
    (sourceResetAll x i).a = (x i).a ∧ (sourceResetAll x i).R = (x i).R := ⟨rfl, rfl⟩

theorem resetAll_ledgers (x : Raw) (i : Fin 4) :
    (sourceResetAll x i).q = (fun _ => 0) ∧ (sourceResetAll x i).nd = 0 := ⟨rfl, rfl⟩

theorem resetQ_physical (x : Raw) (i : Fin 4) :
    (sourceResetQ x i).a = (x i).a ∧ (sourceResetQ x i).R = (x i).R := ⟨rfl, rfl⟩

theorem resetQ_divisions (x : Raw) (i : Fin 4) :
    (sourceResetQ x i).nd = (x i).nd := rfl

theorem phase_duration : (300 : ℝ) * (1 / 10) = 30 := by norm_num

theorem total_duration : (300 : ℝ) * (1 / 10) + 300 * (1 / 10) = 60 := by norm_num

local instance (p : Par) (Q D : ℕ) : MeasurableSpace (CappedState p Q D) := ⊤
local instance (p : Par) (Q D : ℕ) : MeasurableSingletonClass (CappedState p Q D) :=
  ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

abbrev Capped := CappedState seedOff 500 5

def blockDuration : ℝ := 1 / 10

def onKilled : SubMarkov Raw :=
  cf3SourceKilled (p := canonicalSeedOnCF3) seedOn_valid
    (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl
    (sourceDead 16 oldSpecies)

def offKilled : SubMarkov Raw :=
  cf3SourceKilled canonicalSeedFree_valid
    (CF3MarkedKernel.rate_positive canonicalSeedFree_valid) le_rfl
    (sourceDead 16 allSpecies)

/-- The second phase's literal source value, after the switch ledger reset. -/
def offSourceValue (y : Raw) : ℝ :=
  blocks offKilled (cf3Rate seedOff * blockDuration) (sourceOkS 500 allSpecies)
    sourceResetQ 300 (sourceFinalD 5) (sourceResetAll y)

/-- Explicit genuinely switched source composition. The first phase's
terminal reward invokes the other generator after `resetAll`. -/
def switchedSourceValue (x : Raw) : ℝ :=
  blocks onKilled (cf3Rate canonicalSeedOnCF3 * blockDuration)
    (sourceOkS 500 oldSpecies) sourceResetQ 300 offSourceValue (sourceResetAll x)

def offCappedValue (y : Capped) : ℝ :=
  blocks (cf3CappedKilled canonicalSeedFree_valid 500 5
      (CF3MarkedKernel.rate_positive canonicalSeedFree_valid) le_rfl
      (cappedDead 16 allSpecies))
    (cf3Rate seedOff * blockDuration) (cappedOkS 500 allSpecies) cappedResetQ 300
      (cappedFinalD 5) (cappedResetAll y)

def switchedCappedValue (x : Capped) : ℝ :=
  blocks (cf3CappedKilled seedOn_valid 500 5
      (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl (cappedDead 16 oldSpecies))
    (cf3Rate canonicalSeedOnCF3 * blockDuration) (cappedOkS 500 oldSpecies)
      cappedResetQ 300 offCappedValue (cappedResetAll x)

theorem offSourceValue_cap (y : Raw) :
    offSourceValue y = offCappedValue (capProject 500 5 y) := by
  unfold offSourceValue offCappedValue offKilled
  rw [cf3_capped_grid_blocks canonicalSeedFree_valid 500 5 16 500 5
    (by norm_num) (by norm_num) allSpecies
    (CF3MarkedKernel.rate_positive canonicalSeedFree_valid) le_rfl
    (cf3Rate seedOff * blockDuration) 300 (sourceResetAll y),
    sourceResetAll_project]

/-- The exact source quotient also preserves the switched nested composition;
no same-parameter `sourceMission` is substituted for the two generators. -/
theorem switchedSourceValue_cap (x : Raw) :
    switchedSourceValue x = switchedCappedValue (capProject 500 5 x) := by
  have hf : offSourceValue = fun y : Raw => offCappedValue (capProject 500 5 y) :=
    funext offSourceValue_cap
  calc
    _ = blocks onKilled (cf3Rate canonicalSeedOnCF3 * blockDuration)
        (sourceOkS 500 oldSpecies) sourceResetQ 300
        (fun y => offCappedValue (capProject 500 5 y)) (sourceResetAll x) :=
      congrArg (fun f : Raw → ℝ => blocks onKilled
        (cf3Rate canonicalSeedOnCF3 * blockDuration) (sourceOkS 500 oldSpecies)
        sourceResetQ 300 f (sourceResetAll x)) hf
    _ = blocks (cf3CappedKilled (p := canonicalSeedOnCF3) seedOn_valid 500 5
        (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl (cappedDead 16 oldSpecies))
        (cf3Rate canonicalSeedOnCF3 * blockDuration) (cappedOkS 500 oldSpecies)
        cappedResetQ 300 offCappedValue (capProject 500 5 (sourceResetAll x)) :=
      cf3_capped_blocks (p := canonicalSeedOnCF3) seedOn_valid 500 5 16 500
        (by norm_num) oldSpecies (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl
        (cf3Rate canonicalSeedOnCF3 * blockDuration) 300 offCappedValue (sourceResetAll x)
    _ = _ := congrArg (fun z : CappedState canonicalSeedOnCF3 500 5 =>
      blocks (cf3CappedKilled (p := canonicalSeedOnCF3) seedOn_valid 500 5
        (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl (cappedDead 16 oldSpecies))
        (cf3Rate canonicalSeedOnCF3 * blockDuration) (cappedOkS 500 oldSpecies)
        cappedResetQ 300 offCappedValue z)
      (sourceResetAll_project (p := canonicalSeedOnCF3) 500 5 x)

private theorem scalar_nonneg {X : Type} (Q : SubMarkov X) {f : X → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : X) : 0 ≤ Q.P f x := by
  have hz : Q.P (fun _ => 0) x = 0 := by simpa using Q.smul 0 (fun _ => 0) x
  rw [← hz]
  exact Q.mono _ _ hf x

private theorem scalar_iter_nonneg {X : Type} (Q : SubMarkov X) {f : X → ℝ}
    (hf : ∀ y, 0 ≤ f y) (n : ℕ) (x : X) : 0 ≤ Q.iter n f x := by
  induction n generalizing f with
  | zero => exact hf x
  | succ n ih => exact ih (f := Q.P f) (fun y => scalar_nonneg Q hf y)

private theorem scalar_blocks_nonneg {X : Type} (Q : SubMarkov X)
    {μ : ℝ} (hμ : 0 ≤ μ) (ok : X → Prop) (reset : X → X)
    (f : X → ℝ) (hf : ∀ y, 0 ≤ f y) (n : ℕ) (x : X) :
    0 ≤ blocks Q μ ok reset n f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      change 0 ≤ ∑' k, pois μ k * Q.iter k
        (fun y => if ok y then blocks Q μ ok reset n f (reset y) else 0) x
      apply tsum_nonneg
      intro k
      exact mul_nonneg (by unfold pois; positivity)
        (scalar_iter_nonneg Q (fun y => by split_ifs; exact ih _; exact le_rfl) k x)

private theorem offCappedValue_nonneg (y : Capped) : 0 ≤ offCappedValue y := by
  unfold offCappedValue
  apply scalar_blocks_nonneg
  · exact mul_nonneg (CF3MarkedKernel.rate_positive canonicalSeedFree_valid).le
      (by norm_num [blockDuration])
  · intro z
    unfold cappedFinalD
    split_ifs <;> norm_num

/-- Weighted one-phase event identity on the already constructed finite capped
ambient law. This supplies arbitrary nonnegative terminal continuation values
for the genuinely switched composition. -/
private theorem capped_phase_good_reward {p : Par} (hp : p.Valid)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty)
    (f : CappedState p 500 5 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (z : CappedState p 500 5) (hinit : ¬ cappedOkS 500 req z) :
    (∫⁻ h, if SourceBlockAmbient.allBlockSuccess blockDuration
        (cappedDead 16 req) (cappedOkS 500 req) h then ENNReal.ofReal (f h.2) else 0
      ∂SourceBlockAmbient.ambientLaw (CF3CappedPathLaw.cappedKernel hp 500 5)
        (CF3MarkedKernel.rate_positive hp) blockDuration cappedResetQ 300 z) =
      ENNReal.ofReal (blocks (cf3CappedKilled hp 500 5
        (CF3MarkedKernel.rate_positive hp) le_rfl (cappedDead 16 req))
        (cf3Rate p * blockDuration) (cappedOkS 500 req) cappedResetQ 300 f z) := by
  let F : SourceBlockProtocol.History (CappedState p 500 5) 300 → ℝ≥0∞ :=
    fun h => ENNReal.ofReal (f h.2)
  let A : Set (SourceBlockProtocol.History (CappedState p 500 5) 300) :=
    {h | SourceBlockAmbient.allBlockSuccess blockDuration
      (cappedDead 16 req) (cappedOkS 500 req) h}
  have hA : MeasurableSet A := SourceBlockAmbient.measurableSet_allBlockSuccess _ _ _ _
  have hreset (y : CappedState p 500 5) : ¬ cappedOkS 500 req (cappedResetQ y) :=
    SourceBlockProtocol.capped_fresh_not_okS hp (by norm_num) hreq _ (fun _ _ => rfl)
  calc
    _ = ∫⁻ h, A.indicator F h
        ∂SourceBlockAmbient.ambientLaw (CF3CappedPathLaw.cappedKernel hp 500 5)
          (CF3MarkedKernel.rate_positive hp) blockDuration cappedResetQ 300 z := by
      apply lintegral_congr
      intro h
      by_cases hh : SourceBlockAmbient.allBlockSuccess blockDuration
          (cappedDead 16 req) (cappedOkS 500 req) h <;>
        simp [A, F, Set.indicator, hh]
    _ = ∫⁻ h, F h ∂SourceBlockProtocol.protocolLaw
        (CF3CappedPathLaw.cappedKernel hp 500 5) (CF3MarkedKernel.rate_positive hp)
        blockDuration (cappedDead 16 req) (cappedOkS 500 req) cappedResetQ 300 z := by
      rw [lintegral_indicator hA, SourceBlockAmbient.ambientLaw_restrict_success]
    _ = _ := SourceBlockProtocol.protocolLaw_endpoint (cappedGen_isGen hp 500 5)
      (CF3MarkedKernel.rate_positive hp) le_rfl (by norm_num [blockDuration])
      (cappedDead 16 req) (cappedOkS 500 req) cappedResetQ hreset f hf 300 z hinit

abbrev PhaseHistory := RawOperated.History seedOff 300
abbrev TwoPhaseHistory := PhaseHistory × PhaseHistory

/-- The actual seed-free phase is conditionally sampled at the bookkeeping
reset of the first phase's raw endpoint, regardless of its success or failure. -/
def afterSwitchKernel : ProbabilityTheory.Kernel PhaseHistory PhaseHistory where
  toFun h := RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll h.2)
  measurable' := (measurable_of_countable
    (fun y : Raw => RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 y)).comp
      ((measurable_of_countable (sourceResetAll (p := seedOff))).comp measurable_snd)

instance afterSwitchKernel_markov : IsMarkovKernel afterSwitchKernel where
  isProbabilityMeasure h := RawOperated.rawLaw_probability
    canonicalSeedFree_valid blockDuration 300 (sourceResetAll h.2)

instance afterSwitchKernel_finite : IsFiniteKernel afterSwitchKernel :=
  @IsZeroOrMarkovKernel.isFiniteKernel PhaseHistory PhaseHistory _ _ afterSwitchKernel
    ⟨Or.inr afterSwitchKernel_markov⟩

instance afterSwitchKernel_sFinite : IsSFiniteKernel afterSwitchKernel :=
  @ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel
    PhaseHistory PhaseHistory _ _ afterSwitchKernel
    afterSwitchKernel_finite

/-- One joint ambient law retains both full phase vectors and the second
phase's final raw state. No success test appears in this probability law. -/
def switchedLaw (x : Raw) : Measure TwoPhaseHistory :=
  (RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)).compProd
    afterSwitchKernel

instance switchedLaw_probability (x : Raw) : IsProbabilityMeasure (switchedLaw x) := by
  let μ : Measure PhaseHistory :=
    RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)
  let : IsMarkovKernel afterSwitchKernel := afterSwitchKernel_markov
  let : IsProbabilityMeasure μ :=
    RawOperated.rawLaw_probability (p := canonicalSeedOnCF3) seedOn_valid
      blockDuration 300 (sourceResetAll x)
  change IsProbabilityMeasure (μ.compProd afterSwitchKernel)
  infer_instance

theorem switchedLaw_lintegral (x : Raw) (F : TwoPhaseHistory → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ h, F h ∂switchedLaw x) =
      ∫⁻ a, ∫⁻ b, F (a, b)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
  let μ : Measure PhaseHistory :=
    RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)
  let : IsProbabilityMeasure μ :=
    RawOperated.rawLaw_probability (p := canonicalSeedOnCF3) seedOn_valid
      blockDuration 300 (sourceResetAll x)
  let : IsSFiniteKernel afterSwitchKernel := afterSwitchKernel_sFinite
  change (∫⁻ h, F h ∂μ.compProd afterSwitchKernel) = _
  calc
    _ = ∫⁻ a, ∫⁻ b, F (a, b) ∂afterSwitchKernel a
        ∂μ :=
      Measure.lintegral_compProd hF
    _ = _ := rfl

def goodPhase {p : Par} (req : Finset (Fin p.c)) (h : RawOperated.History p 300) : Prop :=
  SourceBlockAmbient.allBlockSuccess blockDuration (cappedDead 16 req)
    (cappedOkS 500 req) (RawOperated.capHistory p 500 5 300 h)

theorem measurableSet_goodPhase {p : Par} (req : Finset (Fin p.c)) :
    MeasurableSet {h : RawOperated.History p 300 | goodPhase req h} :=
  (SourceBlockAmbient.measurableSet_allBlockSuccess blockDuration
    (cappedDead 16 req) (cappedOkS 500 req) 300).preimage
      (RawOperated.measurable_capHistory p 500 5 300)

private theorem raw_phase_good_reward {p : Par} (hp : p.Valid)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty)
    (f : CappedState p 500 5 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : SourceState p) (hinit : ¬ cappedOkS 500 req (capProject 500 5 x)) :
    (∫⁻ h, if goodPhase req h then ENNReal.ofReal (f (capProject 500 5 h.2)) else 0
      ∂RawOperated.rawLaw hp blockDuration 300 x) =
      ENNReal.ofReal (blocks (cf3CappedKilled hp 500 5
        (CF3MarkedKernel.rate_positive hp) le_rfl (cappedDead 16 req))
        (cf3Rate p * blockDuration) (cappedOkS 500 req) cappedResetQ 300 f
          (capProject 500 5 x)) := by
  let F : SourceBlockProtocol.History (CappedState p 500 5) 300 → ℝ≥0∞ := fun h =>
    if SourceBlockAmbient.allBlockSuccess blockDuration
      (cappedDead 16 req) (cappedOkS 500 req) h then ENNReal.ofReal (f h.2) else 0
  have hF : Measurable F := by
    have hr : Measurable (fun h : SourceBlockProtocol.History (CappedState p 500 5) 300 =>
        ENNReal.ofReal (f h.2)) := by
      simpa only [Function.comp_def] using
        (measurable_of_countable (fun y => ENNReal.ofReal (f y))).comp
          (measurable_snd : Measurable
            (fun h : SourceBlockProtocol.History (CappedState p 500 5) 300 => h.2))
    exact Measurable.ite (SourceBlockAmbient.measurableSet_allBlockSuccess _ _ _ _)
      hr measurable_const
  calc
    _ = ∫⁻ h, F (RawOperated.capHistory p 500 5 300 h)
        ∂RawOperated.rawLaw hp blockDuration 300 x := rfl
    _ = ∫⁻ h, F h ∂SourceBlockAmbient.ambientLaw (CF3CappedPathLaw.cappedKernel hp 500 5)
        (CF3MarkedKernel.rate_positive hp) blockDuration cappedResetQ 300 (capProject 500 5 x) :=
      RawOperated.rawLaw_capHistory_lintegral hp blockDuration 500 5 300 x F hF
    _ = _ := capped_phase_good_reward hp req hreq f hf _ hinit

private theorem resetAll_not_ok {p : Par} (hp : p.Valid)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty) (y : SourceState p) :
    ¬ cappedOkS 500 req (capProject 500 5 (sourceResetAll y)) := by
  apply SourceBlockProtocol.capped_fresh_not_okS hp (by norm_num) hreq
  intro i j
  simp [capProject, capSite, sourceResetAll]

def goodSwitch (h : TwoPhaseHistory) : Prop :=
  goodPhase (p := canonicalSeedOnCF3) oldSpecies h.1 ∧
    goodPhase (p := seedOff) allSpecies h.2 ∧ ∀ i, 5 ≤ (h.2.2 i).nd

theorem measurableSet_goodSwitch : MeasurableSet {h : TwoPhaseHistory | goodSwitch h} := by
  exact ((measurableSet_goodPhase (p := canonicalSeedOnCF3) oldSpecies).preimage
      measurable_fst).inter
    (((measurableSet_goodPhase (p := seedOff) allSpecies).preimage measurable_snd).inter
      (((Set.to_countable {y : Raw | ∀ i, 5 ≤ (y i).nd}).measurableSet).preimage
        (measurable_snd.comp measurable_snd)))

/-- Exact event probability on the full normalized raw operated history. The
second phase kernel is used before, and independently of, any success test. -/
theorem switchedLaw_good_probability (x : Raw) :
    switchedLaw x {h | goodSwitch h} = ENNReal.ofReal (switchedSourceValue x) := by
  have hoff (y : Raw) :
      (∫⁻ h, if goodPhase allSpecies h then
        ENNReal.ofReal (cappedFinalD 5 (capProject 500 5 h.2)) else 0
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll y)) =
        ENNReal.ofReal (offCappedValue (capProject 500 5 y)) := by
    have hf (z : Capped) : 0 ≤ cappedFinalD 5 z := by
      unfold cappedFinalD
      split_ifs <;> norm_num
    simpa only [offCappedValue, sourceResetAll_project] using
      raw_phase_good_reward canonicalSeedFree_valid allSpecies allSpecies_nonempty
        (cappedFinalD 5) hf (sourceResetAll y)
          (resetAll_not_ok canonicalSeedFree_valid allSpecies allSpecies_nonempty y)
  have hfinal (h : PhaseHistory) :
      ENNReal.ofReal (cappedFinalD 5 (capProject 500 5 h.2)) =
        if ∀ i, 5 ≤ (h.2 i).nd then 1 else 0 := by
    rw [← cap_finalD_eq (p := seedOff) (Q := 500) (D := 5) (d := 5)
      (by norm_num : 5 ≤ 5) h.2]
    by_cases hh : ∀ i, 5 ≤ (h.2 i).nd <;> simp [hh]
  calc
    _ = ∫⁻ h, {h : TwoPhaseHistory | goodSwitch h}.indicator (fun _ => 1) h
        ∂switchedLaw x := (lintegral_indicator_one measurableSet_goodSwitch).symm
    _ = ∫⁻ a, ∫⁻ b,
        {h : TwoPhaseHistory | goodSwitch h}.indicator (fun _ => 1) (a, b)
        ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll a.2)
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) :=
      switchedLaw_lintegral x _ (measurable_const.indicator measurableSet_goodSwitch)
    _ = ∫⁻ a, if goodPhase (p := canonicalSeedOnCF3) oldSpecies a then
        ENNReal.ofReal (offCappedValue (capProject 500 5 a.2)) else 0
        ∂RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x) := by
      apply lintegral_congr
      intro a
      by_cases ha : goodPhase (p := canonicalSeedOnCF3) oldSpecies a
      · simp only [ha, ite_true]
        calc
          _ = ∫⁻ b, if goodPhase allSpecies b then
              ENNReal.ofReal (cappedFinalD 5 (capProject 500 5 b.2)) else 0
              ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
                (sourceResetAll a.2) := by
            apply lintegral_congr
            intro b
            rw [hfinal b]
            by_cases hb : goodPhase allSpecies b <;>
              by_cases hd : ∀ i, 5 ≤ (b.2 i).nd <;>
                simp [Set.indicator, goodSwitch, ha, hb, hd]
          _ = _ := hoff a.2
      · rw [ite_eq_right ha]
        calc
          _ = ∫⁻ _b, (0 : ℝ≥0∞)
              ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
                (sourceResetAll a.2) := by
            apply lintegral_congr
            intro b
            exact Set.indicator_of_notMem (fun hh => ha hh.1) (fun _ => 1)
          _ = 0 := lintegral_zero
    _ = ENNReal.ofReal (switchedCappedValue (capProject 500 5 x)) := by
      have he := raw_phase_good_reward (p := canonicalSeedOnCF3) seedOn_valid
        oldSpecies oldSpecies_nonempty offCappedValue offCappedValue_nonneg
        (sourceResetAll x)
        (resetAll_not_ok seedOn_valid oldSpecies oldSpecies_nonempty x)
      rw [sourceResetAll_project (p := canonicalSeedOnCF3) 500 5 x] at he
      exact he
    _ = _ := congrArg ENNReal.ofReal (switchedSourceValue_cap x).symm

/-- Literal raw source tests on every physical block window. -/
def physicalPhase {p : Par} (req : Finset (Fin p.c))
    (h : RawOperated.History p 300) : Prop :=
  ∀ i, noExit (fun y => ¬ sourceDead 16 req y) blockDuration (h.1 i).2 ∧
    sourceOkS 500 req (timedState blockDuration (h.1 i).2)

private theorem capped_physicalPhase_iff {p : Par} (req : Finset (Fin p.c))
    (h : RawOperated.History p 300) :
    SourceBlockAmbient.allBlockPhysical blockDuration (cappedDead 16 req)
      (cappedOkS 500 req) (RawOperated.capHistory p 500 5 300 h) ↔ physicalPhase req h := by
  have hd (y : SourceState p) :
      sourceDead 16 req y ↔ cappedDead 16 req (capProject 500 5 y) :=
    cap_dead_iff 500 5 16 req y
  have ho (y : SourceState p) :
      sourceOkS 500 req y ↔ cappedOkS 500 req (capProject 500 5 y) :=
    cap_okS_iff (by norm_num : 500 ≤ 500) req y
  change (∀ i, noExit (fun y => ¬ cappedDead 16 req y) blockDuration
      (RawOperated.capPath p 500 5 (h.1 i).2) ∧
      cappedOkS 500 req (timedState blockDuration (RawOperated.capPath p 500 5 (h.1 i).2))) ↔ _
  apply forall_congr'
  intro i
  apply and_congr
  · change (∀ t, 0 ≤ t → t ≤ blockDuration →
        ¬ cappedDead 16 req (capProject 500 5 (timedState t (h.1 i).2))) ↔
      ∀ t, 0 ≤ t → t ≤ blockDuration → ¬ sourceDead 16 req (timedState t (h.1 i).2)
    simp only [← hd]
  · change cappedOkS 500 req (capProject 500 5 (timedState blockDuration (h.1 i).2)) ↔
      sourceOkS 500 req (timedState blockDuration (h.1 i).2)
    exact (ho _).symm

/-- A measurable regularity event is used to transport physical tests through
conditional kernels; no measurability of an uncountable no-exit intersection
is silently assumed. -/
def regularPhase {p : Par} (h : RawOperated.History p 300) : Prop :=
  SourceBlockAmbient.allPaths (SourceBlockAmbient.clockRegular blockDuration)
    (RawOperated.capHistory p 500 5 300 h)

theorem measurableSet_regularPhase (p : Par) :
    MeasurableSet {h : RawOperated.History p 300 | regularPhase h} :=
  (SourceBlockAmbient.measurableSet_allPaths _
    (SourceBlockAmbient.measurableSet_clockRegular blockDuration)).preimage
      (RawOperated.measurable_capHistory p 500 5 300)

private theorem rawLaw_ae_regular {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ h ∂RawOperated.rawLaw hp blockDuration 300 x, regularPhase h := by
  have ha : ∀ᵐ h ∂(RawOperated.rawLaw hp blockDuration 300 x).map
      (RawOperated.capHistory p 500 5 300),
      SourceBlockAmbient.allPaths (SourceBlockAmbient.clockRegular blockDuration) h := by
    rw [RawOperated.rawLaw_capHistory]
    exact SourceBlockAmbient.ambientLaw_ae_allPaths (CF3CappedPathLaw.cappedKernel hp 500 5)
      (CF3MarkedKernel.rate_positive hp) blockDuration cappedResetQ
      (SourceBlockAmbient.clockRegular blockDuration)
      (SourceBlockAmbient.measurableSet_clockRegular blockDuration)
      (SourceBlockAmbient.eventLaw_ae_clockRegular (CF3CappedPathLaw.cappedKernel hp 500 5)
        (CF3MarkedKernel.rate_positive hp) blockDuration) 300 (capProject 500 5 x)
  exact ae_of_ae_map (RawOperated.measurable_capHistory p 500 5 300).aemeasurable ha

private theorem goodPhase_iff_physical_of_regular {p : Par}
    (req : Finset (Fin p.c)) (h : RawOperated.History p 300) (hr : regularPhase h) :
    goodPhase req h ↔ physicalPhase req h := by
  have hc : SourceBlockAmbient.allBlockSuccess blockDuration
        (cappedDead 16 req) (cappedOkS 500 req) (RawOperated.capHistory p 500 5 300 h) ↔
      SourceBlockAmbient.allBlockPhysical blockDuration
        (cappedDead 16 req) (cappedOkS 500 req) (RawOperated.capHistory p 500 5 300 h) := by
    apply forall_congr'
    intro i
    change (¬ exited (fun y => ¬ cappedDead 16 req y)
        (timedHistory blockDuration ((RawOperated.capHistory p 500 5 300 h).1 i)) ∧
        cappedOkS 500 req
          (timedState blockDuration ((RawOperated.capHistory p 500 5 300 h).1 i))) ↔
      noExit (fun y => ¬ cappedDead 16 req y) blockDuration
        ((RawOperated.capHistory p 500 5 300 h).1 i) ∧
        cappedOkS 500 req
          (timedState blockDuration ((RawOperated.capHistory p 500 5 300 h).1 i))
    rw [noExit_iff_not_exited (fun y => ¬ cappedDead 16 req y)
      ((RawOperated.capHistory p 500 5 300 h).1 i) (by norm_num [blockDuration])
      (hr i).1 (hr i).2]
  exact hc.trans (capped_physicalPhase_iff req h)

/-- All source clock regularity is proved jointly under the actual conditional
switch law, including failed histories. -/
theorem switchedLaw_ae_regular (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, regularPhase (p := canonicalSeedOnCF3) h.1 ∧
      regularPhase (p := seedOff) h.2 := by
  unfold switchedLaw
  apply Measure.ae_compProd_of_ae_ae
    (((measurableSet_regularPhase canonicalSeedOnCF3).preimage measurable_fst).inter
      ((measurableSet_regularPhase seedOff).preimage measurable_snd))
  filter_upwards [rawLaw_ae_regular seedOn_valid (sourceResetAll x)] with a ha
  change ∀ᵐ b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2), regularPhase (p := canonicalSeedOnCF3) a ∧
      regularPhase (p := seedOff) b
  exact (rawLaw_ae_regular canonicalSeedFree_valid (sourceResetAll a.2)).mono
    (fun _ hb => ⟨ha, hb⟩)

def physicalSwitch (h : TwoPhaseHistory) : Prop :=
  physicalPhase (p := canonicalSeedOnCF3) oldSpecies h.1 ∧
    physicalPhase (p := seedOff) allSpecies h.2 ∧ ∀ i, 5 ≤ (h.2.2 i).nd

theorem goodSwitch_ae_physical (x : Raw) :
    {h | goodSwitch h} =ᵐ[switchedLaw x] {h | physicalSwitch h} := by
  filter_upwards [switchedLaw_ae_regular x] with h hr
  apply propext
  exact and_congr
    (goodPhase_iff_physical_of_regular (p := canonicalSeedOnCF3) oldSpecies h.1 hr.1)
    (and_congr (goodPhase_iff_physical_of_regular (p := seedOff) allSpecies h.2 hr.2) Iff.rfl)

theorem nullMeasurableSet_physicalSwitch (x : Raw) :
    NullMeasurableSet {h | physicalSwitch h} (switchedLaw x) :=
  measurableSet_goodSwitch.nullMeasurableSet.congr (goodSwitch_ae_physical x)

/-- The actual physical survival/service and final division event has the
explicit two-generator source value. No success lower bound is presumed. -/
theorem switchedLaw_physical_probability (x : Raw) :
    switchedLaw x {h | physicalSwitch h} = ENNReal.ofReal (switchedSourceValue x) := by
  calc
    _ = switchedLaw x {h | goodSwitch h} := measure_congr (goodSwitch_ae_physical x).symm
    _ = _ := switchedLaw_good_probability x

/-- The final source formula is intentionally written as nested seeded and
seed-free blocks, rather than using the historical same-parameter mission. -/
theorem canonical_switched_source_blocks (x : Raw) :
    switchedLaw x {h | physicalSwitch h} =
      ENNReal.ofReal (blocks
        (cf3SourceKilled (p := canonicalSeedOnCF3) seedOn_valid
          (CF3MarkedKernel.rate_positive seedOn_valid) le_rfl
          (sourceDead 16 oldSpecies))
        (cf3Rate canonicalSeedOnCF3 * (1 / 10 : ℝ))
        (sourceOkS 500 oldSpecies) sourceResetQ 300
        (fun y => blocks
          (cf3SourceKilled canonicalSeedFree_valid
            (CF3MarkedKernel.rate_positive canonicalSeedFree_valid) le_rfl
            (sourceDead 16 allSpecies))
          (cf3Rate seedOff * (1 / 10 : ℝ))
          (sourceOkS 500 allSpecies) sourceResetQ 300 (sourceFinalD 5) (sourceResetAll y))
        (sourceResetAll x)) := by
  exact switchedLaw_physical_probability x

/-- Actual block starts, ordinary q-resets, and returned phase endpoints. -/
def jointCompatible (x : Raw) (h : TwoPhaseHistory) : Prop :=
  RawOperated.compatible canonicalSeedOnCF3 blockDuration 300 (sourceResetAll x) h.1 ∧
    RawOperated.compatible seedOff blockDuration 300 (sourceResetAll h.1.2) h.2

theorem measurableSet_jointCompatible (x : Raw) :
    MeasurableSet {h : TwoPhaseHistory | jointCompatible x h} := by
  have hm : Measurable (fun h : TwoPhaseHistory => (sourceResetAll h.1.2, h.2)) := by
    simpa only [Function.comp_def] using
      ((measurable_of_countable (sourceResetAll (p := seedOff))).comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  exact ((RawOperated.measurableSet_compatible canonicalSeedOnCF3 blockDuration 300
      (sourceResetAll x)).preimage measurable_fst).inter
    ((RawOperated.measurableSet_compatible_joint seedOff blockDuration 300).preimage hm)

theorem switchedLaw_ae_compatible (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, jointCompatible x h := by
  unfold switchedLaw
  apply Measure.ae_compProd_of_ae_ae (measurableSet_jointCompatible x)
  filter_upwards [RawOperated.rawLaw_ae_compatible seedOn_valid blockDuration 300
    (sourceResetAll x)] with a ha
  change ∀ᵐ b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2), _
  exact (RawOperated.rawLaw_ae_compatible canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2)).mono (fun _ hb => ⟨ha, hb⟩)

/-- The first raw state after the switch is exactly the prescribed bookkeeping
reset of the first phase's final raw state, before any new physical operation. -/
theorem switchedLaw_ae_switch_start (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, (h.2.1 0).2 0 = (0, sourceResetAll h.1.2) := by
  filter_upwards [switchedLaw_ae_compatible x] with h hh
  exact hh.2.1

theorem switchedLaw_ae_switch_physical_state (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, ∀ i : Fin 4,
      (((h.2.1 0).2 0).2 i).a = (h.1.2 i).a ∧
      (((h.2.1 0).2 0).2 i).R = (h.1.2 i).R := by
  filter_upwards [switchedLaw_ae_switch_start x] with h hh
  intro i
  rw [hh]
  exact resetAll_physical h.1.2 i

/-- The prior phase endpoint is the actual final block's timed endpoint.
This strengthens bookkeeping-state continuity to executed physical continuity. -/
theorem switchedLaw_ae_endpoint_continuity (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, ∀ i : Fin 4,
      (((h.2.1 0).2 0).2 i).a =
        ((timedState blockDuration (h.1.1 (Fin.last 299)).2) i).a ∧
      (((h.2.1 0).2 0).2 i).R =
        ((timedState blockDuration (h.1.1 (Fin.last 299)).2) i).R := by
  filter_upwards [switchedLaw_ae_compatible x] with h hh
  have hs := RawOperated.compatible_first seedOff blockDuration 299
    (sourceResetAll h.1.2) h.2 hh.2
  have he := RawOperated.compatible_final_last canonicalSeedOnCF3 blockDuration 299
    (sourceResetAll x) h.1 hh.1
  intro i
  rw [hs, he]
  exact ⟨rfl, rfl⟩

def jointFaithful (h : TwoPhaseHistory) : Prop :=
  RawOperated.allSegments (RawOperated.faithful canonicalSeedOnCF3) h.1 ∧
    RawOperated.allSegments (RawOperated.faithful seedOff) h.2

/-- Every recorded raw path is the complete source fold of its own actually
sampled marked path. State-null physical labels are retained in that fold. -/
theorem switchedLaw_ae_faithful (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, jointFaithful h := by
  unfold switchedLaw
  apply Measure.ae_compProd_of_ae_ae
    (((RawOperated.measurableSet_allSegments (RawOperated.faithful canonicalSeedOnCF3)
      (RawOperated.measurableSet_faithful canonicalSeedOnCF3) 300).preimage measurable_fst).inter
      ((RawOperated.measurableSet_allSegments (RawOperated.faithful seedOff)
        (RawOperated.measurableSet_faithful seedOff) 300).preimage measurable_snd))
  filter_upwards [RawOperated.rawLaw_ae_faithful seedOn_valid blockDuration 300
    (sourceResetAll x)] with a ha
  change ∀ᵐ b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2), _
  exact (RawOperated.rawLaw_ae_faithful canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2)).mono (fun _ hb => ⟨ha, hb⟩)

def segmentBoundary (p : Par) (s : RawOperated.Segment p) : Prop :=
  NoBoundaryArrival.ClockBoundarySupport {blockDuration} s.1 ∧
    NoBoundaryArrival.ClockBoundarySupport {blockDuration} s.2

theorem measurableSet_segmentBoundary (p : Par) :
    MeasurableSet {s : RawOperated.Segment p | segmentBoundary p s} :=
  ((NoBoundaryArrival.measurableSet_clockBoundarySupport {blockDuration}
    (Set.countable_singleton blockDuration)).preimage measurable_fst).inter
      ((NoBoundaryArrival.measurableSet_clockBoundarySupport {blockDuration}
        (Set.countable_singleton blockDuration)).preimage measurable_snd)

private theorem rawLaw_ae_boundary {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∀ᵐ h ∂RawOperated.rawLaw hp blockDuration 300 x,
      RawOperated.allSegments (segmentBoundary p) h :=
  RawOperated.rawLaw_ae_clocks hp blockDuration 300 x {blockDuration}
    (Set.countable_singleton blockDuration)

def jointClockSupport (h : TwoPhaseHistory) : Prop :=
  RawOperated.allSegments (segmentBoundary canonicalSeedOnCF3) h.1 ∧
    RawOperated.allSegments (segmentBoundary seedOff) h.2

/-- Both actual phase clocks are positive and unbounded, with no positive-index
proposal at a block endpoint. Sentinel coordinate zero is excluded. Thus the
seeded phase has no operation exactly at physical time 30. -/
theorem switchedLaw_ae_clock_support (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, jointClockSupport h := by
  unfold switchedLaw
  apply Measure.ae_compProd_of_ae_ae
    (((RawOperated.measurableSet_allSegments (segmentBoundary canonicalSeedOnCF3)
      (measurableSet_segmentBoundary canonicalSeedOnCF3) 300).preimage measurable_fst).inter
      ((RawOperated.measurableSet_allSegments (segmentBoundary seedOff)
        (measurableSet_segmentBoundary seedOff) 300).preimage measurable_snd))
  filter_upwards [rawLaw_ae_boundary seedOn_valid (sourceResetAll x)] with a ha
  change ∀ᵐ b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2), _
  exact (rawLaw_ae_boundary canonicalSeedFree_valid (sourceResetAll a.2)).mono
    (fun _ hb => ⟨ha, hb⟩)

def seedCoefficient (t : ℝ) : ℝ := if t < 30 then 6 else 0

theorem seedCoefficient_at_switch : seedCoefficient 30 = 0 := by norm_num [seedCoefficient]

theorem on_block_before_switch (i : Fin 300) {u : ℝ} (hu : u < blockDuration) :
    (i.val : ℝ) * blockDuration + u < 30 := by
  have hi : (i.val : ℝ) ≤ 299 := by exact_mod_cast (show i.val ≤ 299 by omega)
  norm_num [blockDuration] at hu ⊢
  nlinarith

theorem off_block_after_switch (i : Fin 300) {u : ℝ} (hu : 0 ≤ u) :
    30 ≤ 30 + (i.val : ℝ) * blockDuration + u := by
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  norm_num [blockDuration]
  nlinarith

theorem seedCoefficient_on_block (i : Fin 300) {u : ℝ} (hu : u < blockDuration) :
    seedCoefficient ((i.val : ℝ) * blockDuration + u) = 6 := by
  simp [seedCoefficient, on_block_before_switch i hu]

theorem seedCoefficient_off_block (i : Fin 300) {u : ℝ} (hu : 0 ≤ u) :
    seedCoefficient (30 + (i.val : ℝ) * blockDuration + u) = 0 := by
  simp [seedCoefficient, not_lt.mpr (off_block_after_switch i hu)]

theorem source_seed_rate_at_on_time (x : Raw) (i : Fin 4) (j : Fin 3)
    (k : Fin 300) {u : ℝ} (hu : u < blockDuration) :
    sourceIntensity canonicalSeedOnCF3 x (Sum.inl (i, Sum.inl (0, j))) =
      seedCoefficient ((k.val : ℝ) * blockDuration + u) * (1 - (x i).u j) := by
  rw [seedCoefficient_on_block k hu]
  exact source_seed_rate_on x i j

theorem source_seed_rate_at_off_time (x : Raw) (i : Fin 4) (j : Fin 3)
    (k : Fin 300) {u : ℝ} (hu : 0 ≤ u) :
    sourceIntensity seedOff x (Sum.inl (i, Sum.inl (0, j))) =
      seedCoefficient (30 + (k.val : ℝ) * blockDuration + u) * (1 - (x i).u j) := by
  rw [seedCoefficient_off_block k hu, zero_mul]
  exact source_seed_rate_off x i j

private theorem raw_timedState_zero_of_pos {p : Par} (w : RawOperated.RawPath p)
    (hH : ∀ n, 0 < (w (n + 1)).1) : timedState 0 w = (w 0).2 := by
  have h1 : 0 < arrivalTime 1 w := by
    simpa [arrivalTime, max_eq_right (hH 0).le] using hH 0
  have hi := clockIndex_eq_of_between w 0 (by simp [arrivalTime]) h1
  simp only [timedState, hi]

/-- Physical counts and fuel are continuous at the phase boundary: the off
window's actual time-zero state agrees with the on window's final endpoint. -/
theorem switchedLaw_ae_timed_boundary_continuity (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, ∀ i : Fin 4,
      ((timedState 0 (h.2.1 0).2) i).a =
        ((timedState blockDuration (h.1.1 (Fin.last 299)).2) i).a ∧
      ((timedState 0 (h.2.1 0).2) i).R =
        ((timedState blockDuration (h.1.1 (Fin.last 299)).2) i).R := by
  filter_upwards [switchedLaw_ae_endpoint_continuity x, switchedLaw_ae_clock_support x]
    with h hc hclock
  have ht := raw_timedState_zero_of_pos (h.2.1 0).2 ((hclock.2 0).2).1
  intro i
  rw [ht]
  exact hc i

/-- Every actually executed positive-index seeded proposal is strictly before
absolute time 30. Actual endpoint atoms have been ruled out, rather than
assigned the on-phase rate at the deterministic switch. -/
theorem switchedLaw_ae_seeded_proposal_before_switch (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, ∀ i : Fin 300, ∀ n : ℕ,
      arrivalTime (n + 1) (h.1.1 i).2 ≤ blockDuration →
      (i.val : ℝ) * blockDuration + arrivalTime (n + 1) (h.1.1 i).2 < 30 := by
  filter_upwards [switchedLaw_ae_clock_support x] with h hc
  intro i n hn
  have hne : arrivalTime (n + 1) (h.1.1 i).2 ≠ blockDuration := by
    intro he
    exact ((hc.1 i).2).2.2 n (Set.mem_singleton_iff.mpr he)
  exact on_block_before_switch i (lt_of_le_of_ne hn hne)

def jointFresh (h : TwoPhaseHistory) : Prop :=
  RawOperated.allSegments (RawOperated.fresh canonicalSeedOnCF3) h.1 ∧
    RawOperated.allSegments (RawOperated.fresh seedOff) h.2

/-- Segment coordinate zero has hold zero and no physical mark. Fresh
sentinels are never counted as executed source operations at an intervention. -/
theorem switchedLaw_ae_fresh (x : Raw) :
    ∀ᵐ h ∂switchedLaw x, jointFresh h := by
  unfold switchedLaw
  apply Measure.ae_compProd_of_ae_ae
    (((RawOperated.measurableSet_allSegments (RawOperated.fresh canonicalSeedOnCF3)
      (RawOperated.measurableSet_fresh canonicalSeedOnCF3) 300).preimage measurable_fst).inter
      ((RawOperated.measurableSet_allSegments (RawOperated.fresh seedOff)
        (RawOperated.measurableSet_fresh seedOff) 300).preimage measurable_snd))
  filter_upwards [RawOperated.rawLaw_ae_fresh seedOn_valid blockDuration 300
    (sourceResetAll x)] with a ha
  change ∀ᵐ b ∂RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2), _
  exact (RawOperated.rawLaw_ae_fresh canonicalSeedFree_valid blockDuration 300
    (sourceResetAll a.2)).mono (fun _ hb => ⟨ha, hb⟩)

end
end CTMCHeredity20261019.V2.SeedSwitch
