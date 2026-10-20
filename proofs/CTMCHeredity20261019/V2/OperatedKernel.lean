module

public import proofs.CTMCHeredity20261019.SourceBlockAmbient

@[expose] public section

/-!
# Version 2: actual finite histories of stochastic operated segments

The segment kernel is normalized independently of every success test. A
measurable next-state operation is applied to each sampled segment before
sampling its successor. The carrier retains all segments and the final state.
The projection theorem identifies the entire joint finite-vector measure.
-/

namespace CTMCHeredity20261019.V2.Operated

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section

abbrev History (X W : Type) (n : ℕ) := (Fin n → W) × X

def prepend {X W : Type} (n : ℕ) (z : W × History X W n) : History X W (n + 1) :=
  (Fin.cons z.1 z.2.1, z.2.2)

def tail {X W : Type} {n : ℕ} (h : History X W (n + 1)) : History X W n :=
  (fun i => h.1 i.succ, h.2)

@[simp] theorem tail_prepend {X W : Type} (n : ℕ) (w : W) (h : History X W n) :
    tail (prepend n (w, h)) = h := by
  apply Prod.ext
  · funext i
    simp only [tail, prepend, Fin.cons_succ]
  · rfl

theorem measurable_prepend {X W : Type} [MeasurableSpace X] [MeasurableSpace W] (n : ℕ) :
    Measurable (prepend (X := X) (W := W) n) := by
  apply Measurable.prodMk _ (measurable_snd.comp measurable_snd)
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [prepend, Fin.cons_zero] using
      (measurable_fst : Measurable (fun z : W × History X W n => z.1))
  · simpa only [prepend, Fin.cons_succ, Function.comp_def] using
      (measurable_pi_apply (X := fun _ : Fin n => W) j).comp
        (measurable_fst.comp measurable_snd)

theorem measurable_tail {X W : Type} [MeasurableSpace X] [MeasurableSpace W] (n : ℕ) :
    Measurable (tail (X := X) (W := W) (n := n)) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_iff.mpr
  intro i
  simpa only [tail, Function.comp_def] using
    (measurable_pi_apply (X := fun _ : Fin (n + 1) => W) i.succ).comp measurable_fst

section Construction

variable {X W : Type} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace W]

def tailKernel {n : ℕ} (next : W → X) (hnext : Measurable next)
    (ν : X → Measure (History X W n)) : ProbabilityTheory.Kernel W (History X W n) where
  toFun w := ν (next w)
  measurable' := (measurable_of_countable ν).comp hnext

theorem tailKernel_markov {n : ℕ} (next : W → X) (hnext : Measurable next)
    (ν : X → Measure (History X W n)) (hν : ∀ x, IsProbabilityMeasure (ν x)) :
    IsMarkovKernel (tailKernel next hnext ν) where
  isProbabilityMeasure w := hν (next w)

/-- Actual conditional segment sampling, retaining the whole joint history. -/
def law (κ : ProbabilityTheory.Kernel X W) (next : W → X) (hnext : Measurable next) :
    (n : ℕ) → X → Measure (History X W n)
  | 0, x => Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)
  | n + 1, x =>
      ((κ x).compProd (tailKernel next hnext (law κ next hnext n))).map (prepend n)

theorem law_isProbabilityMeasure (κ : ProbabilityTheory.Kernel X W) [IsMarkovKernel κ]
    (next : W → X) (hnext : Measurable next) (n : ℕ) (x : X) :
    IsProbabilityMeasure (law κ next hnext n x) := by
  induction n generalizing x with
  | zero => dsimp only [law]; infer_instance
  | succ n ih =>
      let : IsMarkovKernel (tailKernel next hnext (law κ next hnext n)) :=
        tailKernel_markov next hnext _ ih
      change IsProbabilityMeasure
        (((κ x).compProd (tailKernel next hnext (law κ next hnext n))).map (prepend n))
      constructor
      rw [Measure.map_apply (measurable_prepend n) MeasurableSet.univ]
      simp

instance law_probability (κ : ProbabilityTheory.Kernel X W) [IsMarkovKernel κ]
    (next : W → X) (hnext : Measurable next) (n : ℕ) (x : X) :
    IsProbabilityMeasure (law κ next hnext n x) :=
  law_isProbabilityMeasure κ next hnext n x

def kernel (κ : ProbabilityTheory.Kernel X W) (next : W → X) (hnext : Measurable next)
    (n : ℕ) : ProbabilityTheory.Kernel X (History X W n) where
  toFun := law κ next hnext n
  measurable' := measurable_of_countable _

instance kernel_markov (κ : ProbabilityTheory.Kernel X W) [IsMarkovKernel κ]
    (next : W → X) (hnext : Measurable next) (n : ℕ) :
    IsMarkovKernel (kernel κ next hnext n) where
  isProbabilityMeasure x := law_probability κ next hnext n x

theorem law_lintegral_step (κ : ProbabilityTheory.Kernel X W) [IsMarkovKernel κ]
    (next : W → X) (hnext : Measurable next) (n : ℕ) (x : X)
    (F : History X W (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F h ∂law κ next hnext (n + 1) x) =
      ∫⁻ w, ∫⁻ h, F (prepend n (w, h)) ∂law κ next hnext n (next w) ∂κ x := by
  let : IsMarkovKernel (tailKernel next hnext (law κ next hnext n)) :=
    tailKernel_markov next hnext _ (fun y => inferInstance)
  rw [law, lintegral_map hF (measurable_prepend n)]
  have hcomp : Measurable (fun z : W × History X W n => F (prepend n z)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_prepend n)
  exact Measure.lintegral_compProd
    (μ := κ x) (κ := tailKernel next hnext (law κ next hnext n)) hcomp

end Construction

def historyMap {X Y W V : Type} (π : X → Y) (ψ : W → V) (n : ℕ)
    (h : History X W n) : History Y V n := (fun i => ψ (h.1 i), π h.2)

theorem measurable_historyMap {X Y W V : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace W] [MeasurableSpace V] {π : X → Y} {ψ : W → V}
    (hπ : Measurable π) (hψ : Measurable ψ) (n : ℕ) :
    Measurable (historyMap π ψ n) := by
  apply Measurable.prodMk _ (hπ.comp measurable_snd)
  apply measurable_pi_iff.mpr
  intro i
  simpa only [historyMap, Function.comp_def] using
    hψ.comp ((measurable_pi_apply (X := fun _ : Fin n => W) i).comp measurable_fst)

theorem historyMap_prepend {X Y W V : Type} (π : X → Y) (ψ : W → V)
    (n : ℕ) (w : W) (h : History X W n) :
    historyMap π ψ (n + 1) (prepend n (w, h)) =
      prepend n (ψ w, historyMap π ψ n h) := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [historyMap, prepend, Fin.cons_zero]
    · simp only [historyMap, prepend, Fin.cons_succ]
  · rfl

/-- Entire joint finite-vector projection. The one-segment map equality is a
concrete input to this generic theorem, discharged by the actual CF3 path law
in V2_RawOperated, rather than a hypothesized source bridge. -/
theorem law_map {X Y W V : Type} [Countable X] [Countable Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace W] [MeasurableSpace V]
    (κ : ProbabilityTheory.Kernel X W) [IsMarkovKernel κ]
    (τ : ProbabilityTheory.Kernel Y V) [IsMarkovKernel τ]
    (next : W → X) (hnext : Measurable next)
    (next' : V → Y) (hnext' : Measurable next')
    (π : X → Y) (hπ : Measurable π) (ψ : W → V) (hψ : Measurable ψ)
    (hκ : ∀ x, (κ x).map ψ = τ (π x))
    (hcomm : ∀ w, π (next w) = next' (ψ w)) (n : ℕ) (x : X) :
    (law κ next hnext n x).map (historyMap π ψ n) = law τ next' hnext' n (π x) := by
  induction n generalizing x with
  | zero =>
      rw [law, law, Measure.map_dirac' (measurable_historyMap hπ hψ 0)]
      apply congrArg Measure.dirac
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · rfl
  | succ n ih =>
      apply Measure.ext_of_lintegral
      intro F hF
      have hmap := measurable_historyMap hπ hψ (n + 1)
      have hFM : Measurable (fun h : History X W (n + 1) =>
          F (historyMap π ψ (n + 1) h)) := by
        simpa only [Function.comp_def] using hF.comp hmap
      let q : V → ℝ≥0∞ := fun v =>
        ∫⁻ h, F (prepend n (v, h)) ∂law τ next' hnext' n (next' v)
      let : IsMarkovKernel (tailKernel next' hnext' (law τ next' hnext' n)) :=
        tailKernel_markov next' hnext' _ (fun y => inferInstance)
      have hq : Measurable q := by
        have hc : Measurable (fun z : V × History Y V n => F (prepend n z)) := by
          simpa only [Function.comp_def] using hF.comp (measurable_prepend n)
        change Measurable (fun v => ∫⁻ h, F (prepend n (v, h))
          ∂(tailKernel next' hnext' (law τ next' hnext' n)) v)
        exact hc.lintegral_kernel_prod_right'
      calc
        _ = ∫⁻ h, F (historyMap π ψ (n + 1) h) ∂law κ next hnext (n + 1) x :=
          lintegral_map hF hmap
        _ = ∫⁻ w, ∫⁻ h, F (historyMap π ψ (n + 1) (prepend n (w, h)))
            ∂law κ next hnext n (next w) ∂κ x :=
          law_lintegral_step κ next hnext n x _ hFM
        _ = ∫⁻ w, ∫⁻ h, F (prepend n (ψ w, h))
            ∂law τ next' hnext' n (π (next w)) ∂κ x := by
          apply lintegral_congr
          intro w
          have hFI : Measurable (fun h : History Y V n => F (prepend n (ψ w, h))) := by
            simpa only [Function.comp_def, id_eq] using
              hF.comp ((measurable_prepend n).comp (measurable_const.prodMk measurable_id))
          calc
            _ = ∫⁻ h, F (prepend n (ψ w, historyMap π ψ n h))
                ∂law κ next hnext n (next w) := by
              apply lintegral_congr
              intro h
              exact congrArg F (historyMap_prepend π ψ n w h)
            _ = ∫⁻ h, F (prepend n (ψ w, h))
                ∂(law κ next hnext n (next w)).map (historyMap π ψ n) :=
              (lintegral_map hFI (measurable_historyMap hπ hψ n)).symm
            _ = _ := by rw [ih (next w)]
        _ = ∫⁻ w, q (ψ w) ∂κ x := by
          apply lintegral_congr
          intro w
          dsimp only [q]
          rw [hcomm w]
        _ = ∫⁻ v, q v ∂(κ x).map ψ := (lintegral_map hq hψ).symm
        _ = ∫⁻ v, q v ∂τ (π x) := by rw [hκ x]
        _ = _ := (law_lintegral_step τ next' hnext' n (π x) F hF).symm

section Ambient

open HybridCTMC.Kernel CTMCHeredity20261019.SourceBlockProtocol

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def eventSegmentKernel (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam) :
    ProbabilityTheory.Kernel S (Path S) where
  toFun x := K.eventLaw Lam hLam x
  measurable' := measurable_of_countable _

instance eventSegmentKernel_markov (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam) :
    IsMarkovKernel (eventSegmentKernel K hLam) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (K.eventLaw Lam hLam x)
    infer_instance

theorem measurable_resetEndpoint (T : ℝ) (reset : S → S) :
    Measurable (fun w : Path S => reset (timedState T w)) := by
  simpa only [Function.comp_def] using
    (measurable_of_countable reset).comp (measurable_timedState T)

/-- The generic normalized segment law is the already sealed ambient operated
event law. In particular, this does not change the meaning of the old wrapper. -/
theorem law_event_eq_ambient (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (T : ℝ) (reset : S → S) (n : ℕ) (x : S) :
    law (eventSegmentKernel K hLam) (fun w => reset (timedState T w))
        (measurable_resetEndpoint T reset) n x =
      SourceBlockAmbient.ambientLaw K hLam T reset n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have ht :
          tailKernel (fun w : Path S => reset (timedState T w)) (measurable_resetEndpoint T reset)
              (law (eventSegmentKernel K hLam) (fun w => reset (timedState T w))
                (measurable_resetEndpoint T reset) n) =
            SourceBlockProtocol.tailKernel T reset
              (SourceBlockProtocol.protocolLaw K hLam T (fun _ => False) (fun _ => True) reset n) := by
        apply ProbabilityTheory.Kernel.ext
        intro w
        exact ih (reset (timedState T w))
      change ((K.eventLaw Lam hLam x).compProd _).map (prepend n) =
        ((SourceBlockProtocol.blockPathLaw K hLam T (fun _ => False) (fun _ => True) x).compProd
          (SourceBlockProtocol.tailKernel T reset
            (SourceBlockProtocol.protocolLaw K hLam T (fun _ => False) (fun _ => True) reset n))).map
              (SourceBlockProtocol.prependHistory n)
      rw [ht, SourceBlockAmbient.blockPathLaw_unrestricted]
      rfl

end Ambient

end
end CTMCHeredity20261019.V2.Operated
