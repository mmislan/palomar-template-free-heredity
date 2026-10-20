module

public import proofs.CTMCHeredity20261019.SourcePathExpectation
public import proofs.CTMCHeredity20261019.PhysicalCutGlobalLaw
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# One actual operated service-grid phase and its source block operator

Each block samples the constructed physical event law, checks physical no-exit
and endpoint service, then resets its endpoint before sampling the next block.
The joint subprobability retains a finite vector of sampled paths and the final
reset state. Only each path's window [0,T] is executed; its unused tail is an
auxiliary sample, not the post-reset future of an unchanged homogeneous path.

Survival is represented measurably by the actual visited history and is proved
to agree almost everywhere with physical no-exit. No endpoint-law, path-law,
Markov-law, successful-path, or eventual-hit premise is assumed. This is one
fixed-parameter deterministic-grid phase, not the full P161 mission or a
finite-stock theorem.
-/

namespace CTMCHeredity20261019.SourceBlockProtocol

open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical
noncomputable section

abbrev Path (S : Type) := ℕ → ℝ × S
abbrev History (S : Type) (n : ℕ) := (Fin n → Path S) × S

section Construction

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- A measurable finite-history presentation of the actual block success test. -/
def goodHistory (T : ℝ) (dead ok : S → Prop) (w : Path S) : Prop :=
  ¬ exited (fun y => ¬ dead y) (timedHistory T w) ∧ ok (timedState T w)

theorem measurableSet_goodHistory (T : ℝ) (dead ok : S → Prop) :
    MeasurableSet {w : Path S | goodHistory T dead ok w} := by
  let φ : List S → ℝ := fun xs => if ¬ exited (fun y => ¬ dead y) xs then 1 else 0
  have he : {w : Path S | ¬ exited (fun y => ¬ dead y) (timedHistory T w)} =
      (fun w => φ (timedHistory T w)) ⁻¹' {(1 : ℝ)} := by
    ext w
    by_cases h : ¬ exited (fun y => ¬ dead y) (timedHistory T w) <;> simp [φ, h]
  have hs : MeasurableSet {w : Path S | ¬ exited (fun y => ¬ dead y) (timedHistory T w)} := by
    rw [he]
    exact (measurable_timedHistory_observable T φ) (measurableSet_singleton 1)
  exact hs.inter (((Set.to_countable {y : S | ok y}).measurableSet).preimage
    (measurable_timedState T))

/-- The actual successful physical block, before its boundary reset. -/
def blockPathLaw (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (dead ok : S → Prop) (x : S) : Measure (Path S) :=
  (K.eventLaw Lam hLam x).restrict {w | goodHistory T dead ok w}

instance blockPathLaw_finite (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (dead ok : S → Prop) (x : S) :
    IsFiniteMeasure (blockPathLaw K hLam T dead ok x) := by
  unfold blockPathLaw
  infer_instance

theorem blockPathLaw_mass_le_one (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (x : S) :
    blockPathLaw K hLam T dead ok x Set.univ ≤ 1 := by
  unfold blockPathLaw
  rw [Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ)

/-- Physical no-exit and the measurable history check are equivalent under
the actual clock law, with no regularity premise supplied by the caller. -/
theorem goodHistory_ae_physical (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (x : S) :
    {w : Path S | goodHistory T dead ok w} =ᵐ[K.eventLaw Lam hLam x]
      {w | noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w)} := by
  filter_upwards [K.ae_arrival_crosses hLam x T, K.ae_holding_pos hLam x] with w hw hp
  apply propext
  change (¬ exited (fun y => ¬ dead y) (timedHistory T w) ∧ ok (timedState T w)) ↔ _
  rw [noExit_iff_not_exited (fun y => ¬ dead y) w hT hw hp]

/-- The block measure really is restriction to physical survival and service,
not merely a separately chosen finite-history success law. -/
theorem blockPathLaw_physical (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (x : S) :
    blockPathLaw K hLam T dead ok x =
      (K.eventLaw Lam hLam x).restrict
        {w | noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w)} :=
  Measure.restrict_congr_set (goodHistory_ae_physical K hLam hT dead ok x)

theorem blockPathLaw_lintegral (K : HybridCTMC.Kernel S) {Lam T : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (dead ok : S → Prop) (x : S)
    (F : Path S → ℝ≥0∞) (_hF : Measurable F) :
    (∫⁻ w, F w ∂blockPathLaw K hLam T dead ok x) =
      ∫⁻ w, if noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w)
        then F w else 0 ∂K.eventLaw Lam hLam x := by
  unfold blockPathLaw
  rw [← lintegral_indicator (measurableSet_goodHistory T dead ok)]
  apply lintegral_congr_ae
  filter_upwards [goodHistory_ae_physical K hLam hT dead ok x] with w hw
  simp only [Set.indicator, Set.mem_ofPred_eq] at hw ⊢
  by_cases hg : goodHistory T dead ok w
  · have hp : noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w) := Eq.mp hw hg
    simp [hg, hp]
  · have hp : ¬ (noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w)) :=
      fun hp => hg (Eq.mpr hw hp)
    simp only [hg, hp, ite_false]

/-- Finite input states make the actual successful-path family a measurable
subkernel, without any assumption about a probability of success. -/
def blockPathKernel (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (dead ok : S → Prop) : ProbabilityTheory.Kernel S (Path S) where
  toFun := blockPathLaw K hLam T dead ok
  measurable' := measurable_of_countable _

instance blockPathKernel_finite (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) :
    IsFiniteKernel (blockPathKernel K hLam T dead ok) where
  exists_univ_le := ⟨1, by simp, blockPathLaw_mass_le_one K hLam T dead ok⟩

/-- Prepend the actual sampled path; preserve the tail protocol's final state. -/
def prependHistory (n : ℕ) (p : Path S × History S n) : History S (n + 1) :=
  (Fin.cons p.1 p.2.1, p.2.2)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_prependHistory (n : ℕ) : Measurable (prependHistory (S := S) n) := by
  apply Measurable.prodMk _ (measurable_snd.comp measurable_snd)
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [prependHistory, Fin.cons_zero] using
      (measurable_fst : Measurable (fun p : Path S × History S n => p.1))
  · simpa only [prependHistory, Fin.cons_succ, Function.comp_def] using
      (measurable_pi_apply (X := fun _ : Fin n => Path S) j).comp
        (measurable_fst.comp measurable_snd)

/-- The next operated block begins at the actual reset physical endpoint. -/
def tailKernel {n : ℕ} (T : ℝ) (reset : S → S)
    (ν : S → Measure (History S n)) : ProbabilityTheory.Kernel (Path S) (History S n) where
  toFun w := ν (reset (timedState T w))
  measurable' := (measurable_of_countable ν).comp
    ((measurable_of_countable reset).comp (measurable_timedState T))

private theorem tailKernel_finite {n : ℕ} (T : ℝ) (reset : S → S)
    (ν : S → Measure (History S n)) (hν : ∀ x, ν x Set.univ ≤ 1) :
    IsFiniteKernel (tailKernel T reset ν) where
  exists_univ_le := ⟨1, by simp, fun w => hν (reset (timedState T w))⟩

/-- One joint operated block-history law, not a product of unrelated endpoint
certificates. Its mass counts paths that pass every actual block test. -/
def protocolLaw (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (dead ok : S → Prop) (reset : S → S) :
    (n : ℕ) → S → Measure (History S n)
  | 0, x => Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)
  | n + 1, x =>
      ((blockPathLaw K hLam T dead ok x).compProd
        (tailKernel T reset (protocolLaw K hLam T dead ok reset n))).map (prependHistory n)

theorem protocolLaw_mass_le_one (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S)
    (n : ℕ) (x : S) : protocolLaw K hLam T dead ok reset n x Set.univ ≤ 1 := by
  induction n generalizing x with
  | zero => simp [protocolLaw]
  | succ n ih =>
      let κ := tailKernel T reset (protocolLaw K hLam T dead ok reset n)
      let : IsFiniteKernel κ := tailKernel_finite T reset _ ih
      change (((blockPathLaw K hLam T dead ok x).compProd κ).map
        (prependHistory n)) Set.univ ≤ 1
      rw [Measure.map_apply (measurable_prependHistory n) MeasurableSet.univ]
      simp only [Set.preimage_univ]
      rw [Measure.compProd_apply MeasurableSet.univ]
      simp only [Set.preimage_univ]
      calc
        (∫⁻ w, κ w Set.univ ∂blockPathLaw K hLam T dead ok x) ≤
            ∫⁻ _w, (1 : ℝ≥0∞) ∂blockPathLaw K hLam T dead ok x :=
          lintegral_mono (fun w => ih (reset (timedState T w)))
        _ = blockPathLaw K hLam T dead ok x Set.univ := by simp
        _ ≤ 1 := blockPathLaw_mass_le_one K hLam T dead ok x

def protocolKernel (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (dead ok : S → Prop) (reset : S → S) (n : ℕ) :
    ProbabilityTheory.Kernel S (History S n) where
  toFun := protocolLaw K hLam T dead ok reset n
  measurable' := measurable_of_countable _

instance protocolKernel_finite (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S) (n : ℕ) :
    IsFiniteKernel (protocolKernel K hLam T dead ok reset n) where
  exists_univ_le := ⟨1, by simp, protocolLaw_mass_le_one K hLam T dead ok reset n⟩

/-- Exact joint-law recursion for arbitrary measurable history rewards. -/
theorem protocolLaw_lintegral_step (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) (dead ok : S → Prop) (reset : S → S) (n : ℕ)
    (x : S) (F : History S (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F h ∂protocolLaw K hLam T dead ok reset (n + 1) x) =
      ∫⁻ w, ∫⁻ h, F (prependHistory n (w, h))
        ∂protocolLaw K hLam T dead ok reset n (reset (timedState T w))
        ∂blockPathLaw K hLam T dead ok x := by
  let : IsFiniteKernel (tailKernel T reset (protocolLaw K hLam T dead ok reset n)) :=
    tailKernel_finite T reset _ (protocolLaw_mass_le_one K hLam T dead ok reset n)
  rw [protocolLaw, lintegral_map hF (measurable_prependHistory n)]
  have hcomp : Measurable (fun p : Path S × History S n => F (prependHistory n p)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_prependHistory n)
  calc
    _ = ∫⁻ w, ∫⁻ h, F (prependHistory n (w, h))
        ∂(tailKernel T reset (protocolLaw K hLam T dead ok reset n)) w
        ∂blockPathLaw K hLam T dead ok x :=
      Measure.lintegral_compProd
        (μ := blockPathLaw K hLam T dead ok x)
        (κ := tailKernel T reset (protocolLaw K hLam T dead ok reset n)) hcomp
    _ = _ := rfl

end Construction

section ScalarConnection

variable {S : Type} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem scalarP_nonneg (Q : SubMarkov S) {f : S → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : S) : 0 ≤ Q.P f x := by
  have hz : Q.P (fun _ => 0) x = 0 := by simpa using Q.smul 0 (fun _ => 0) x
  rw [← hz]
  exact Q.mono _ _ hf x

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem scalarIter_nonneg (Q : SubMarkov S) {f : S → ℝ}
    (hf : ∀ y, 0 ≤ f y) (n : ℕ) (x : S) : 0 ≤ Q.iter n f x := by
  induction n generalizing f with
  | zero => exact hf x
  | succ n ih => exact ih (f := Q.P f) (fun y => scalarP_nonneg Q hf y)

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem scalarCT_nonneg (Q : SubMarkov S) {f : S → ℝ}
    (hf : ∀ y, 0 ≤ f y) {μ : ℝ} (hμ : 0 ≤ μ) (x : S) : 0 ≤ Q.ct μ f x := by
  unfold SubMarkov.ct
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by unfold pois; positivity) (scalarIter_nonneg Q hf n x)

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem scalarBlocks_nonneg (Q : SubMarkov S) {μ : ℝ} (hμ : 0 ≤ μ)
    (ok : S → Prop) (reset : S → S) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    (n : ℕ) (x : S) : 0 ≤ blocks Q μ ok reset n f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      apply scalarCT_nonneg Q _ hμ x
      intro y
      by_cases hy : ok y <;> simp [hy, ih (reset y)]

/-- One block is the source CT operator with the actual service/reset reward.
Only its precise zero-tick condition at this initial state is imposed. -/
theorem blockPathLaw_endpoint (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    {T : ℝ} (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (f : S → ℝ) (hf : ∀ y, 0 ≤ f y) (x : S)
    (hzero : dead x → ¬ ok x) :
    (∫⁻ w, ENNReal.ofReal (f (reset (timedState T w)))
      ∂blockPathLaw (uniformizedKernel hG hLam hL) hLam T dead ok x) =
      ENNReal.ofReal (block (generatorKilled hG hLam hL dead) (Lam * T) ok reset f x) := by
  have hF : Measurable (fun w : Path S => ENNReal.ofReal (f (reset (timedState T w)))) :=
    (measurable_of_countable (fun y => ENNReal.ofReal (f (reset y)))).comp
      (measurable_timedState T)
  rw [blockPathLaw_lintegral _ hLam hT dead ok x _ hF]
  have he (w : Path S) :
      (if noExit (fun y => ¬ dead y) T w ∧ ok (timedState T w) then
        ENNReal.ofReal (f (reset (timedState T w))) else 0) =
      (if noExit (fun y => ¬ dead y) T w then
        ENNReal.ofReal (if ok (timedState T w) then f (reset (timedState T w)) else 0) else 0) := by
    by_cases hs : noExit (fun y => ¬ dead y) T w <;>
      by_cases ho : ok (timedState T w) <;> simp [hs, ho]
  simp_rw [he]
  exact uniformized_noExit_endpoint_ct_zero_tick hG hLam hL dead
    (fun y => if ok y then f (reset y) else 0)
    (fun y => by split_ifs; exact hf (reset y); exact le_rfl)
    hT x (fun hx => by simp [hzero hx])

/-- The constructed joint operated path-history law has exactly the literal
source blocks value. Initial and reset states fail the service test, which
discharges the zero-tick boundary at every block without an extra floor premise. -/
theorem protocolLaw_endpoint (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    {T : ℝ} (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (hreset : ∀ y, ¬ ok (reset y)) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    (n : ℕ) (x : S) (hinit : ¬ ok x) :
    (∫⁻ h, ENNReal.ofReal (f h.2)
      ∂protocolLaw (uniformizedKernel hG hLam hL) hLam T dead ok reset n x) =
      ENNReal.ofReal (blocks (generatorKilled hG hLam hL dead) (Lam * T) ok reset n f x) := by
  induction n generalizing x with
  | zero =>
      change (∫⁻ h, ENNReal.ofReal (f h.2)
        ∂Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)) = ENNReal.ofReal (f x)
      exact lintegral_dirac' _ ((measurable_of_countable (fun y => ENNReal.ofReal (f y))).comp
        measurable_snd)
  | succ n ih =>
      have hreward : Measurable (fun h : History S (n + 1) => ENNReal.ofReal (f h.2)) := by
        simpa only [Function.comp_def] using
          (measurable_of_countable (fun y => ENNReal.ofReal (f y))).comp
            (measurable_snd : Measurable (fun h : History S (n + 1) => h.2))
      rw [protocolLaw_lintegral_step _ hLam T dead ok reset n x
        (fun h : History S (n + 1) => ENNReal.ofReal (f h.2)) hreward]
      have he (w : Path S) :
          (∫⁻ h, ENNReal.ofReal (f (prependHistory n (w, h)).2)
            ∂protocolLaw (uniformizedKernel hG hLam hL) hLam T dead ok reset n
              (reset (timedState T w))) =
          ENNReal.ofReal (blocks (generatorKilled hG hLam hL dead) (Lam * T)
            ok reset n f (reset (timedState T w))) := by
        simpa only [prependHistory] using ih (reset (timedState T w)) (hreset _)
      simp_rw [he]
      exact blockPathLaw_endpoint hG hLam hL hT dead ok reset
        (blocks (generatorKilled hG hLam hL dead) (Lam * T) ok reset n f)
        (scalarBlocks_nonneg _ (mul_nonneg hLam.le hT) ok reset f hf n)
        x (fun _ => hinit)

/-- Success mass is the source blocks value with terminal reward one. -/
theorem protocolLaw_success_mass (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    {T : ℝ} (hT : 0 ≤ T) (dead ok : S → Prop) (reset : S → S)
    (hreset : ∀ y, ¬ ok (reset y)) (n : ℕ) (x : S) (hinit : ¬ ok x) :
    protocolLaw (uniformizedKernel hG hLam hL) hLam T dead ok reset n x Set.univ =
      ENNReal.ofReal (blocks (generatorKilled hG hLam hL dead) (Lam * T)
        ok reset n (fun _ => 1) x) := by
  simpa using protocolLaw_endpoint hG hLam hL hT dead ok reset hreset
    (fun _ => 1) (fun _ => zero_le_one) n x hinit

end ScalarConnection

section CF3Phase

variable {p : Par}

/-- Positive service demand cannot be met by freshly zeroed output ledgers. -/
theorem capped_fresh_not_okS (hp : p.Valid) {Q D m : ℕ} (hm : 0 < m)
    {req : Finset (Fin p.c)} (hreq : req.Nonempty) (x : CappedState p Q D)
    (hz : ∀ i j, (x i).q j = 0) : ¬ cappedOkS m req x := by
  obtain ⟨j, hj⟩ := hreq
  let i : Fin p.M := ⟨0, by have := hp.hM; omega⟩
  intro hok
  have h := hok i j hj
  rw [hz i j] at h
  change m ≤ 0 at h
  omega

/-- One actual CF3 service-grid phase. Both ledgers are zeroed initially;
only output ledgers are zeroed after each block, exactly as in the source.
The terminal reward is the actual every-site division threshold. All caps
preserve the specified tests, and no initial floor is assumed. -/
theorem cf3_source_service_grid (hp : p.Valid) (Q D K m d : ℕ)
    (hm0 : 0 < m) (hm : m ≤ Q) (hd : d ≤ D)
    (req : Finset (Fin p.c)) (hreq : req.Nonempty)
    {Lam T : ℝ} (hLam : 0 < Lam) (hRate : cf3Rate p ≤ Lam) (hT : 0 ≤ T)
    (n : ℕ) (x : CappedSource p)
    [MeasurableSpace (CappedState p Q D)] [MeasurableSingletonClass (CappedState p Q D)] :
    (∫⁻ h, ENNReal.ofReal (cappedFinalD d h.2)
      ∂protocolLaw (uniformizedKernel (cappedGen_isGen hp Q D) hLam hRate)
        hLam T (cappedDead K req) (cappedOkS m req) cappedResetQ n
        (capProject Q D (sourceResetAll x))) =
      ENNReal.ofReal (blocks (cf3SourceKilled hp hLam hRate (sourceDead K req))
        (Lam * T) (sourceOkS m req) sourceResetQ n (sourceFinalD d) (sourceResetAll x)) := by
  have hr (y : CappedState p Q D) : ¬ cappedOkS m req (cappedResetQ y) :=
    capped_fresh_not_okS hp hm0 hreq _ (fun _ _ => rfl)
  have hi : ¬ cappedOkS m req (capProject Q D (sourceResetAll x)) := by
    apply capped_fresh_not_okS hp hm0 hreq
    intro i j
    simp [capProject, capSite, sourceResetAll]
  have hf (y : CappedState p Q D) : 0 ≤ cappedFinalD d y := by
    unfold cappedFinalD
    split_ifs <;> norm_num
  calc
    _ = ENNReal.ofReal (blocks (cf3CappedKilled hp Q D hLam hRate (cappedDead K req))
        (Lam * T) (cappedOkS m req) cappedResetQ n (cappedFinalD d)
          (capProject Q D (sourceResetAll x))) :=
      protocolLaw_endpoint (cappedGen_isGen hp Q D) hLam hRate hT
        (cappedDead K req) (cappedOkS m req) cappedResetQ hr (cappedFinalD d) hf n _ hi
    _ = _ := congrArg ENNReal.ofReal
      (cf3_capped_grid_blocks hp Q D K m d hm hd req hLam hRate (Lam * T) n
        (sourceResetAll x)).symm

end CF3Phase

section PhysicalBoundaryInterpretation

variable {S : Type} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]
  {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}

/-- The already proved physical future law explains the fresh-law continuation
at a boundary when no operation changes the state. The operated protocol above
instead explicitly applies its reset before invoking a fresh law; it is not
identified with the unchanged homogeneous future after that intervention. -/
theorem unreset_boundary_future (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (x : S) (T : ℝ) (hT : 0 ≤ T) :
    ((uniformizedKernel hG hLam hL).eventLaw Lam hLam x).map (physicalTimedCut T) =
      (((uniformizedKernel hG hLam hL).eventLaw Lam hLam x).map (timedState T)).bind
        (fun y => (uniformizedKernel hG hLam hL).eventLaw Lam hLam y) :=
  eventLaw_physicalTimedCut_map (uniformizedKernel hG hLam hL) hLam x T hT

end PhysicalBoundaryInterpretation

end
end CTMCHeredity20261019.SourceBlockProtocol
