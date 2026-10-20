module

public import proofs.CTMCHeredity20261019.SourceBlockProtocol
public import proofs.CTMCHeredity20261019.CanonicalPathLaw

@[expose] public section

/-!
# Ambient operated block probability and the actual success event

The unrestricted instance of `protocolLaw` is a probability law on one finite
vector of physical paths and the final post-reset state. Its conditional next
block is sampled at the reset endpoint of the preceding block. Restricting this
ambient law to the measurable event that every recorded block passes the source
history and service tests gives exactly the existing killed protocol.

The finite-vector event is also proved almost everywhere equivalent to literal
physical no-exit and endpoint service, under this same joint ambient law. The
source block operator is therefore a success-event probability for an explicit
operated process. Each recorded path's unused infinite tail is auxiliary; the
reset protocol is not asserted to be an unchanged homogeneous whole path.

This is one fixed-kinetics service-grid phase. It does not assert the full P161
mission, a seeded/seed-free switch, finite stock, or a numerical certificate.
-/

namespace CTMCHeredity20261019.SourceBlockAmbient

open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CTMCHeredity20261019.SourceBlockProtocol
open scoped BigOperators ENNReal Classical
noncomputable section

section AmbientConstruction

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] theorem goodHistory_unrestricted (T : ℝ) (w : Path S) :
    goodHistory T (fun _ => False) (fun _ => True) w := by
  simp [goodHistory, exited]

@[simp] theorem blockPathLaw_unrestricted (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (x : S) :
    blockPathLaw K hLam T (fun _ => False) (fun _ => True) x =
      K.eventLaw Lam hLam x := by
  simp [blockPathLaw]

/-- The unrestricted instance retains failed as well as successful blocks.
The reset at every boundary is part of this ambient operated process. -/
def ambientLaw (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (reset : S → S) (n : ℕ) (x : S) : Measure (History S n) :=
  protocolLaw K hLam T (fun _ => False) (fun _ => True) reset n x

theorem ambientLaw_mass (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (reset : S → S) (n : ℕ) (x : S) :
    ambientLaw K hLam T reset n x Set.univ = 1 := by
  induction n generalizing x with
  | zero => simp [ambientLaw, protocolLaw]
  | succ n ih =>
      have hi (y : S) : protocolLaw K hLam T (fun _ => False) (fun _ => True)
          reset n y Set.univ = 1 := ih y
      have he := protocolLaw_lintegral_step K hLam T (fun _ => False)
        (fun _ => True) reset n x (fun _ => (1 : ℝ≥0∞)) measurable_const
      simpa only [ambientLaw, lintegral_const, one_mul, hi, blockPathLaw_unrestricted, measure_univ]
        using he

instance ambientLaw_probability (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (reset : S → S) (n : ℕ) (x : S) :
    IsProbabilityMeasure (ambientLaw K hLam T reset n x) where
  measure_univ := ambientLaw_mass K hLam T reset n x

/-- Apply a path test to every actually recorded block. -/
def allPaths {n : ℕ} (P : Path S → Prop) (h : History S n) : Prop :=
  ∀ i : Fin n, P (h.1 i)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurableSet_allPaths {n : ℕ} (P : Path S → Prop)
    (hP : MeasurableSet {w | P w}) : MeasurableSet {h : History S n | allPaths P h} := by
  simp only [allPaths, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun h : History S n => h.1 i) := by
    simpa only [Function.comp_def] using
      ((measurable_pi_apply (X := fun _ : Fin n => Path S) i).comp
        (measurable_fst : Measurable (fun h : History S n => h.1)))
  exact hP.preimage hi

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem allPaths_prepend {n : ℕ} (P : Path S → Prop) (w : Path S) (h : History S n) :
    allPaths P (prependHistory n (w, h)) ↔ P w ∧ allPaths P h := by
  constructor
  · intro ha
    exact ⟨by simpa only [prependHistory, Fin.cons_zero] using ha 0,
      fun i => by simpa only [prependHistory, Fin.cons_succ] using ha i.succ⟩
  · rintro ⟨hw, hh⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [prependHistory, Fin.cons_zero] using hw
    · simpa only [prependHistory, Fin.cons_succ] using hh j

/-- The success event is a measurable test of the sampled finite path vector. -/
def allBlockSuccess (T : ℝ) (dead ok : S → Prop) {n : ℕ} (h : History S n) : Prop :=
  allPaths (goodHistory T dead ok) h

theorem measurableSet_allBlockSuccess (T : ℝ) (dead ok : S → Prop) (n : ℕ) :
    MeasurableSet {h : History S n | allBlockSuccess T dead ok h} :=
  measurableSet_allPaths _ (measurableSet_goodHistory T dead ok)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem allBlockSuccess_prepend (T : ℝ) (dead ok : S → Prop) {n : ℕ}
    (w : Path S) (h : History S n) :
    allBlockSuccess T dead ok (prependHistory n (w, h)) ↔
      goodHistory T dead ok w ∧ allBlockSuccess T dead ok h :=
  allPaths_prepend _ w h

/-- The restriction identity is derived from the actual conditional recursion,
for arbitrary measurable history rewards; it is not a supplied bridge premise. -/
theorem ambientLaw_restrict_success (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) :
    (ambientLaw K hLam T reset n x).restrict {h | allBlockSuccess T dead ok h} =
      protocolLaw K hLam T dead ok reset n x := by
  induction n generalizing x with
  | zero =>
      have hs : {h : History S 0 | allBlockSuccess T dead ok h} = Set.univ := by
        ext h
        simp [allBlockSuccess, allPaths]
      simp [hs, ambientLaw, protocolLaw]
  | succ n ih =>
      apply Measure.ext_of_lintegral
      intro F hF
      rw [← lintegral_indicator (measurableSet_allBlockSuccess T dead ok (n + 1))]
      change (∫⁻ h, {h : History S (n + 1) | allBlockSuccess T dead ok h}.indicator F h
        ∂protocolLaw K hLam T (fun _ => False) (fun _ => True) reset (n + 1) x) = _
      rw [protocolLaw_lintegral_step K hLam T (fun _ => False) (fun _ => True)
        reset n x
          (fun h : History S (n + 1) =>
            {h : History S (n + 1) | allBlockSuccess T dead ok h}.indicator F h)
          (show Measurable (fun h : History S (n + 1) =>
              {h : History S (n + 1) | allBlockSuccess T dead ok h}.indicator F h) from
            hF.indicator (measurableSet_allBlockSuccess T dead ok (n + 1))),
        protocolLaw_lintegral_step K hLam T dead ok reset n x F hF,
        blockPathLaw_unrestricted]
      unfold blockPathLaw
      rw [← lintegral_indicator (measurableSet_goodHistory T dead ok)]
      apply lintegral_congr
      intro w
      simp only [Set.indicator, Set.mem_ofPred_eq, allBlockSuccess_prepend]
      by_cases hw : goodHistory T dead ok w
      · simp only [hw, true_and, ite_true]
        change (∫⁻ h, if allBlockSuccess T dead ok h then
          F (prependHistory n (w, h)) else 0
          ∂ambientLaw K hLam T reset n (reset (timedState T w))) = _
        have he := congrArg
          (fun μ : Measure (History S n) => ∫⁻ h, F (prependHistory n (w, h)) ∂μ)
          (ih (reset (timedState T w)))
        rw [← lintegral_indicator (measurableSet_allBlockSuccess T dead ok n)] at he
        calc
          _ = ∫⁻ h, {h : History S n | allBlockSuccess T dead ok h}.indicator
              (fun h => F (prependHistory n (w, h))) h
              ∂ambientLaw K hLam T reset n (reset (timedState T w)) := by
            apply lintegral_congr
            intro h
            by_cases hh : allBlockSuccess T dead ok h <;> simp [Set.indicator, hh]
          _ = _ := he
      · simp only [hw, false_and, ite_false, lintegral_zero]

/-- Every measurable almost-sure one-block property is propagated through the
actual conditional next-block kernels, for every block in the finite vector. -/
theorem ambientLaw_ae_allPaths (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (reset : S → S) (P : Path S → Prop)
    (hP : MeasurableSet {w | P w})
    (ha : ∀ x, ∀ᵐ w ∂K.eventLaw Lam hLam x, P w) (n : ℕ) (x : S) :
    ∀ᵐ h ∂ambientLaw K hLam T reset n x, allPaths P h := by
  induction n generalizing x with
  | zero => exact Filter.Eventually.of_forall (fun h i => Fin.elim0 i)
  | succ n ih =>
      change ∀ᵐ h ∂((blockPathLaw K hLam T (fun _ => False) (fun _ => True) x).compProd
        (tailKernel T reset
          (protocolLaw K hLam T (fun _ => False) (fun _ => True) reset n))).map
            (prependHistory n), allPaths P h
      apply (ae_map_iff (measurable_prependHistory n).aemeasurable
        (measurableSet_allPaths P hP)).mpr
      apply Measure.ae_compProd_of_ae_ae
        ((measurableSet_allPaths P hP).preimage (measurable_prependHistory n))
      rw [blockPathLaw_unrestricted]
      filter_upwards [ha x] with w hw
      change ∀ᵐ h ∂ambientLaw K hLam T reset n (reset (timedState T w)),
        allPaths P (prependHistory n (w, h))
      exact (ih (reset (timedState T w))).mono fun h hh =>
        (allPaths_prepend P w h).mpr ⟨hw, hh⟩

theorem ambientLaw_success_mass (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) :
    ambientLaw K hLam T reset n x {h | allBlockSuccess T dead ok h} =
      protocolLaw K hLam T dead ok reset n x Set.univ := by
  calc
    _ = (ambientLaw K hLam T reset n x).restrict
        {h | allBlockSuccess T dead ok h} Set.univ :=
      (Measure.restrict_apply_univ _).symm
    _ = _ := congrArg (fun μ : Measure (History S n) => μ Set.univ)
      (ambientLaw_restrict_success K hLam T dead ok reset n x)

theorem ambientLaw_success_terminal (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) (B : S → Prop) :
    ambientLaw K hLam T reset n x {h | allBlockSuccess T dead ok h ∧ B h.2} =
      protocolLaw K hLam T dead ok reset n x {h | B h.2} := by
  have hB : MeasurableSet {h : History S n | B h.2} :=
    (Set.to_countable {y : S | B y}).measurableSet.preimage measurable_snd
  have he := congrArg (fun μ : Measure (History S n) => μ {h | B h.2})
    (ambientLaw_restrict_success K hLam T dead ok reset n x)
  rw [Measure.restrict_apply hB] at he
  have hs : {h : History S n | B h.2} ∩ {h | allBlockSuccess T dead ok h} =
      {h | allBlockSuccess T dead ok h ∧ B h.2} := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
  rwa [hs] at he

/-- Terminal tests, like all-site division counts, are actual event tests too. -/
theorem ambientLaw_success_terminal_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) (B : S → Prop) :
    ambientLaw K hLam T reset n x {h | allBlockSuccess T dead ok h ∧ B h.2} =
      ∫⁻ h, ENNReal.ofReal (if B h.2 then (1 : ℝ) else 0)
        ∂protocolLaw K hLam T dead ok reset n x := by
  rw [ambientLaw_success_terminal K hLam T dead ok reset n x B]
  have hB : MeasurableSet {h : History S n | B h.2} :=
    (Set.to_countable {y : S | B y}).measurableSet.preimage measurable_snd
  rw [← lintegral_indicator_one hB]
  apply lintegral_congr
  intro h
  by_cases hb : B h.2 <;> simp [Set.indicator, hb]

end AmbientConstruction

section PhysicalEvents

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- A measurable source-almost-sure set on which the physical and visited
history survival tests agree. No regularity is assumed of the caller. -/
def clockRegular (T : ℝ) (w : Path S) : Prop :=
  (∃ n, T < arrivalTime n w) ∧ ∀ n, 0 < (w (n + 1)).1

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurableSet_clockRegular (T : ℝ) :
    MeasurableSet {w : Path S | clockRegular T w} := by
  have ha : MeasurableSet (⋃ n : ℕ, {w : Path S | T < arrivalTime n w}) := by
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_lt measurable_const
      ((measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl)
  have hp : MeasurableSet (⋂ n : ℕ, {w : Path S | 0 < (w (n + 1)).1}) := by
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_lt measurable_const
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (n + 1)).fst
  have he : {w : Path S | clockRegular T w} =
      (⋃ n : ℕ, {w : Path S | T < arrivalTime n w}) ∩
        (⋂ n : ℕ, {w : Path S | 0 < (w (n + 1)).1}) := by
    ext w
    simp [clockRegular]
  rw [he]
  exact ha.inter hp

theorem eventLaw_ae_clockRegular (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (x : S) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, clockRegular T w := by
  filter_upwards [K.ae_arrival_crosses hLam x T, K.ae_holding_pos hLam x] with w hw hp
  exact ⟨hw, hp⟩

/-- Literal physical no-exit/service on every executed block window. -/
def allBlockPhysical (T : ℝ) (dead ok : S → Prop) {n : ℕ} (h : History S n) : Prop :=
  allPaths (fun w => noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w)) h

/-- The finite-vector AE equivalence is proved under the ambient conditional
kernels, rather than silently substituting a one-block identity. -/
theorem allBlockSuccess_ae_physical (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) :
    {h : History S n | allBlockSuccess T dead ok h} =ᵐ[ambientLaw K hLam T reset n x]
      {h | allBlockPhysical T dead ok h} := by
  filter_upwards [ambientLaw_ae_allPaths K hLam T reset (clockRegular T)
    (measurableSet_clockRegular T) (eventLaw_ae_clockRegular K hLam T) n x] with h hr
  apply propext
  change (∀ i : Fin n, goodHistory T dead ok (h.1 i)) ↔
    ∀ i : Fin n, noExit (fun y => ¬ dead y) T (h.1 i) ∧ ok (timedState T (h.1 i))
  apply forall_congr'
  intro i
  unfold goodHistory
  rw [noExit_iff_not_exited (fun y => ¬ dead y) (h.1 i) hT (hr i).1 (hr i).2]

theorem nullMeasurableSet_allBlockPhysical (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) :
    NullMeasurableSet {h : History S n | allBlockPhysical T dead ok h}
      (ambientLaw K hLam T reset n x) :=
  (measurableSet_allBlockSuccess T dead ok n).nullMeasurableSet.congr
    (allBlockSuccess_ae_physical K hLam hT dead ok reset n x)

theorem nullMeasurableSet_allBlockPhysical_terminal (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) (B : S → Prop) :
    NullMeasurableSet {h : History S n | allBlockPhysical T dead ok h ∧ B h.2}
      (ambientLaw K hLam T reset n x) := by
  exact (nullMeasurableSet_allBlockPhysical K hLam hT dead ok reset n x).inter
    (((Set.to_countable {y : S | B y}).measurableSet.preimage
      (measurable_snd : Measurable (fun h : History S n => h.2))).nullMeasurableSet)

theorem ambientLaw_restrict_physical (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) :
    (ambientLaw K hLam T reset n x).restrict {h | allBlockPhysical T dead ok h} =
      protocolLaw K hLam T dead ok reset n x := by
  rw [← Measure.restrict_congr_set
    (allBlockSuccess_ae_physical K hLam hT dead ok reset n x)]
  exact ambientLaw_restrict_success K hLam T dead ok reset n x

theorem ambientLaw_physical_terminal (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) (B : S → Prop) :
    ambientLaw K hLam T reset n x {h | allBlockPhysical T dead ok h ∧ B h.2} =
      ambientLaw K hLam T reset n x {h | allBlockSuccess T dead ok h ∧ B h.2} := by
  apply measure_congr
  filter_upwards [allBlockSuccess_ae_physical K hLam hT dead ok reset n x] with h hh
  change allBlockSuccess T dead ok h = allBlockPhysical T dead ok h at hh
  rw [hh]

end PhysicalEvents

section SourceConnection

variable {S : Type} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}

/-- An actual event probability under a normalized ambient operated law equals
the literal source block operator. The zero-tick conditions remain explicit. -/
theorem source_blocks_success_probability (hG : IsGen L G)
    (hLam : 0 < Lam) (hL : L ≤ Lam) {T : ℝ} (hT : 0 ≤ T)
    (dead ok : S → Prop) (reset : S → S) (hreset : ∀ y, ¬ ok (reset y))
    (n : ℕ) (x : S) (hinit : ¬ ok x) :
    ambientLaw (uniformizedKernel hG hLam hL) hLam T reset n x
      {h | allBlockSuccess T dead ok h} =
      ENNReal.ofReal (blocks (generatorKilled hG hLam hL dead) (Lam * T)
        ok reset n (fun _ => 1) x) := by
  rw [ambientLaw_success_mass]
  exact protocolLaw_success_mass hG hLam hL hT dead ok reset hreset n x hinit

theorem source_blocks_physical_probability (hG : IsGen L G)
    (hLam : 0 < Lam) (hL : L ≤ Lam) {T : ℝ} (hT : 0 ≤ T)
    (dead ok : S → Prop) (reset : S → S) (hreset : ∀ y, ¬ ok (reset y))
    (n : ℕ) (x : S) (hinit : ¬ ok x) :
    ambientLaw (uniformizedKernel hG hLam hL) hLam T reset n x
      {h | allBlockPhysical T dead ok h} =
      ENNReal.ofReal (blocks (generatorKilled hG hLam hL dead) (Lam * T)
        ok reset n (fun _ => 1) x) := by
  rw [← measure_congr (allBlockSuccess_ae_physical
    (uniformizedKernel hG hLam hL) hLam hT dead ok reset n x)]
  exact source_blocks_success_probability hG hLam hL hT dead ok reset hreset n x hinit

end SourceConnection

section CF3Phase

variable {p : Par}

/-- The concrete all-site division test at the final post-output-reset state. -/
def finalDivisions {Q D : ℕ} (d : ℕ) (y : CappedState p Q D) : Prop :=
  ∀ i, d ≤ ((y i).nd : ℕ)

/-- Actual finite-vector CF3 service-grid success, including the all-site
terminal division threshold, has exactly the original source `blocks` value.
The ambient law is normalized independently of this event or its probability. -/
theorem cf3_source_service_grid_probability (hp : p.Valid) (Q D K m d : ℕ)
    (hm0 : 0 < m) (hm : m ≤ Q) (hd : d ≤ D)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty)
    {Lam T : ℝ} (hLam : 0 < Lam) (hRate : cf3Rate p ≤ Lam) (hT : 0 ≤ T)
    (n : ℕ) (x : CappedSource p)
    [MeasurableSpace (CappedState p Q D)] [MeasurableSingletonClass (CappedState p Q D)] :
    ambientLaw (uniformizedKernel (cappedGen_isGen hp Q D) hLam hRate)
      hLam T cappedResetQ n (capProject Q D (sourceResetAll x))
        {h | allBlockSuccess T (cappedDead K req) (cappedOkS m req) h ∧
          finalDivisions d h.2} =
      ENNReal.ofReal (blocks (cf3SourceKilled hp hLam hRate (sourceDead K req))
        (Lam * T) (sourceOkS m req) sourceResetQ n (sourceFinalD d) (sourceResetAll x)) := by
  rw [ambientLaw_success_terminal_lintegral]
  calc
    _ = ∫⁻ h, ENNReal.ofReal (cappedFinalD d h.2)
        ∂protocolLaw (uniformizedKernel (cappedGen_isGen hp Q D) hLam hRate)
          hLam T (cappedDead K req) (cappedOkS m req) cappedResetQ n
            (capProject Q D (sourceResetAll x)) := by
      apply lintegral_congr
      intro h
      by_cases hh : ∀ i, d ≤ ((h.2 i).nd : ℕ) <;>
        simp [finalDivisions, cappedFinalD, hh]
    _ = _ := cf3_source_service_grid hp Q D K m d hm0 hm hd req hreq hLam hRate hT n x

/-- Literal physical no-exit and service on every operated block, together with
the final all-site division threshold. This event is null measurable because
it is proved AE equal to the measurable recorded-history event above. -/
theorem cf3_source_service_grid_physical_probability (hp : p.Valid) (Q D K m d : ℕ)
    (hm0 : 0 < m) (hm : m ≤ Q) (hd : d ≤ D)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty)
    {Lam T : ℝ} (hLam : 0 < Lam) (hRate : cf3Rate p ≤ Lam) (hT : 0 ≤ T)
    (n : ℕ) (x : CappedSource p)
    [MeasurableSpace (CappedState p Q D)] [MeasurableSingletonClass (CappedState p Q D)] :
    ambientLaw (uniformizedKernel (cappedGen_isGen hp Q D) hLam hRate)
      hLam T cappedResetQ n (capProject Q D (sourceResetAll x))
        {h | allBlockPhysical T (cappedDead K req) (cappedOkS m req) h ∧
          finalDivisions d h.2} =
      ENNReal.ofReal (blocks (cf3SourceKilled hp hLam hRate (sourceDead K req))
        (Lam * T) (sourceOkS m req) sourceResetQ n (sourceFinalD d) (sourceResetAll x)) := by
  rw [ambientLaw_physical_terminal _ hLam hT (cappedDead K req) (cappedOkS m req)
    cappedResetQ n (capProject Q D (sourceResetAll x)) (finalDivisions d)]
  exact cf3_source_service_grid_probability hp Q D K m d hm0 hm hd req hreq
    hLam hRate hT n x

end CF3Phase

section CanonicalPhase

/-- A fully specified canonical post-withdrawal phase: all three catalysts,
floor 16, service 500 per block, 300 blocks of duration 1/10, and every-site
division count at least 5. This is an identity of an actual event probability
with the source operator, without a claimed numerical success bound. -/
theorem canonical_postwithdrawal_grid_probability
    (x : CappedSource canonicalSeedFreeCF3)
    [MeasurableSpace (CappedState canonicalSeedFreeCF3 500 5)]
    [MeasurableSingletonClass (CappedState canonicalSeedFreeCF3 500 5)] :
    ambientLaw (canonicalCappedKernel 500 5) canonicalSeedFree_clock_pos
      (1 / 10 : ℝ) cappedResetQ 300 (capProject 500 5 (sourceResetAll x))
        {h | allBlockPhysical (1 / 10 : ℝ)
            (cappedDead 16 (Finset.univ : Finset (Fin canonicalSeedFreeCF3.c)))
            (cappedOkS 500 (Finset.univ : Finset (Fin canonicalSeedFreeCF3.c))) h ∧
          finalDivisions 5 h.2} =
      ENNReal.ofReal (blocks
        (cf3SourceKilled canonicalSeedFree_valid canonicalSeedFree_clock_pos
          (show cf3Rate canonicalSeedFreeCF3 ≤ 93515792 by rw [canonicalSeedFree_rate])
          (sourceDead 16 (Finset.univ : Finset (Fin canonicalSeedFreeCF3.c))))
        (93515792 * (1 / 10 : ℝ))
        (sourceOkS 500 (Finset.univ : Finset (Fin canonicalSeedFreeCF3.c)))
        sourceResetQ 300 (sourceFinalD 5) (sourceResetAll x)) := by
  have hr : cf3Rate canonicalSeedFreeCF3 ≤ 93515792 := by rw [canonicalSeedFree_rate]
  have hreq : (Finset.univ : Finset (Fin canonicalSeedFreeCF3.c)).Nonempty :=
    ⟨⟨0, by decide⟩, Finset.mem_univ _⟩
  simpa only [canonicalCappedKernel] using
    cf3_source_service_grid_physical_probability canonicalSeedFree_valid 500 5 16 500 5
      (by norm_num) (by norm_num) (by norm_num) Finset.univ hreq
      canonicalSeedFree_clock_pos hr (by norm_num) 300 x

end CanonicalPhase

end
end CTMCHeredity20261019.SourceBlockAmbient
