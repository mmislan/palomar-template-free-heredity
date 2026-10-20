module

public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import proofs.CTMCHeredity20261019.EventIndexLaw

@[expose] public section

/-!
# V2: the coordinate-zero marked sentinel does not affect a raw future

The actual marked kernel ignores its old mark when sampling the next complete
proposal. Finite-cylinder recursion and measure uniqueness therefore identify
the law obtained by replacing only the coordinate-zero mark. All holds, the
coordinate-zero physical core, and every positive-index mark are preserved.
The raw source fold never executes coordinate zero, so its entire pushed-forward
law is independent of the initial sentinel. No sentinel-independence premise
or raw Markov property is assumed.
-/

namespace CTMCHeredity20261019.V2.SentinelErasure

noncomputable section
open MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical

section Generic

variable {S R : Type} [Fintype S] [Fintype R]

/-- Replace only the initial old-mark sentinel, retaining its hold and core. -/
def replaceSentinel (old' : Option R) (w : ℕ → ℝ × (S × Option R)) : ℕ → ℝ × (S × Option R)
  | 0 => ((w 0).1, ((w 0).2.1, old'))
  | n + 1 => w (n + 1)

omit [Fintype S] [Fintype R] in
@[simp] theorem replaceSentinel_zero (old' : Option R) (w : ℕ → ℝ × (S × Option R)) :
    replaceSentinel old' w 0 = ((w 0).1, ((w 0).2.1, old')) := rfl

omit [Fintype S] [Fintype R] in
@[simp] theorem replaceSentinel_succ (old' : Option R) (w : ℕ → ℝ × (S × Option R)) (n : ℕ) :
    replaceSentinel old' w (n + 1) = w (n + 1) := rfl

omit [Fintype S] [Fintype R] in
theorem replaceSentinel_hold (old' : Option R) (w : ℕ → ℝ × (S × Option R)) (n : ℕ) :
    (replaceSentinel old' w n).1 = (w n).1 := by
  cases n <;> rfl

omit [Fintype S] [Fintype R] in
theorem futureCylinderWeight_replaceSentinel (old' : Option R)
    (w : ℕ → ℝ × (S × Option R)) (k : ℕ)
    (f : ℕ → ℝ × (S × Option R) → ℝ≥0∞) :
    futureCylinderWeight 0 k f (replaceSentinel old' w) = futureCylinderWeight 0 k f w := rfl

/-- The actual finite marked transition PMF ignores the old mark. -/
theorem marked_pmf_sentinel (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) (old old' : Option R) :
    (MarkedKernel.kernel C hLam bound).pmf (x, old) =
      (MarkedKernel.kernel C hLam bound).pmf (x, old') := by
  apply PMF.ext
  intro y
  rfl

variable [MeasurableSpace (S × Option R)] [MeasurableSingletonClass (S × Option R)]

theorem measurable_replaceSentinel (old' : Option R) :
    Measurable (replaceSentinel (S := S) old') := by
  apply measurable_pi_iff.mpr
  intro n
  cases n with
  | zero =>
      exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × (S × Option R)) 0).fst.prodMk
        ((measurable_of_countable (fun z : S × Option R => (z.1, old'))).comp
          (measurable_pi_apply (X := fun _ : ℕ => ℝ × (S × Option R)) 0).snd)
  | succ n => exact measurable_pi_apply (X := fun _ : ℕ => ℝ × (S × Option R)) (n + 1)

omit [MeasurableSingletonClass (S × Option R)] in
/-- Holding time and the complete next state/mark are jointly independent of
the previous sentinel, by the actual product clock-step construction. -/
theorem marked_clockStep_sentinel (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) (x : S) (old old' : Option R) :
    (MarkedKernel.kernel C hLam bound).clockStep Lam (x, old) =
      (MarkedKernel.kernel C hLam bound).clockStep Lam (x, old') := by
  exact congrArg (fun q : PMF (S × Option R) => (expMeasure Lam).prod q.toMeasure)
    (marked_pmf_sentinel C hLam bound x old old')

omit [MeasurableSingletonClass (S × Option R)] in
/-- Every positive-depth future cylinder value ignores the initial sentinel.
The reward and all sampled future marks may otherwise be arbitrary. -/
theorem marked_futureValue_sentinel (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (f : ℕ → ℝ × (S × Option R) → ℝ≥0∞) (k : ℕ)
    (g : S × Option R → ℝ≥0∞) (x : S) (old old' : Option R) :
    futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam f (k + 1) g (x, old) =
      futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam f (k + 1) g (x, old') := by
  induction k generalizing g with
  | zero =>
      change (∫⁻ z, f 0 z * g z.2 ∂(MarkedKernel.kernel C hLam bound).clockStep Lam (x, old)) =
        ∫⁻ z, f 0 z * g z.2 ∂(MarkedKernel.kernel C hLam bound).clockStep Lam (x, old')
      rw [marked_clockStep_sentinel C hLam bound x old old']
  | succ k ih =>
      exact ih (fun y => ∫⁻ z, f (k + 1) z * g z.2
        ∂(MarkedKernel.kernel C hLam bound).clockStep Lam y)

private theorem marked_fullCylinder_value (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (x : S) (old : Option R) (k : ℕ)
    (b : ℕ → ℝ × (S × Option R) → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) :
    (∫⁻ w, fullCylinderWeight (k + 2) b w
      ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)) =
      b 0 (0, (x, old)) * futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam
        (fun i => b (i + 1)) (k + 1) (fun _ => 1) (x, old) := by
  have hv := eventLaw_futureCylinder_value (MarkedKernel.kernel C hLam bound) hLam (x, old)
    (k + 1) (fun i => b (i + 1)) (fun i => hb (i + 1)) (fun _ => 1)
  simp only [mul_one] at hv
  calc
    _ = ∫⁻ w, b 0 (0, (x, old)) * futureCylinderWeight 0 (k + 1) (fun i => b (i + 1)) w
        ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old) := by
      apply lintegral_congr_ae
      filter_upwards [(MarkedKernel.kernel C hLam bound).ae_event_initial hLam (x, old)] with w hw
      rw [fullCylinderWeight_succ, hw]
    _ = b 0 (0, (x, old)) * (∫⁻ w, futureCylinderWeight 0 (k + 1) (fun i => b (i + 1)) w
        ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)) :=
      lintegral_const_mul _ (measurable_futureCylinderWeight 0 (k + 1)
        (fun i => b (i + 1)) (fun i => hb (i + 1)))
    _ = _ := congrArg (fun t : ℝ≥0∞ => b 0 (0, (x, old)) * t) hv

private theorem marked_replacedCylinder_value (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (x : S) (old old' : Option R) (k : ℕ)
    (b : ℕ → ℝ × (S × Option R) → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) :
    (∫⁻ w, fullCylinderWeight (k + 2) b (replaceSentinel old' w)
      ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)) =
      b 0 (0, (x, old')) * futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam
        (fun i => b (i + 1)) (k + 1) (fun _ => 1) (x, old) := by
  have hv := eventLaw_futureCylinder_value (MarkedKernel.kernel C hLam bound) hLam (x, old)
    (k + 1) (fun i => b (i + 1)) (fun i => hb (i + 1)) (fun _ => 1)
  simp only [mul_one] at hv
  calc
    _ = ∫⁻ w, b 0 (0, (x, old')) * futureCylinderWeight 0 (k + 1) (fun i => b (i + 1)) w
        ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old) := by
      apply lintegral_congr_ae
      filter_upwards [(MarkedKernel.kernel C hLam bound).ae_event_initial hLam (x, old)] with w hw
      rw [fullCylinderWeight_succ, futureCylinderWeight_replaceSentinel]
      change b 0 ((w 0).1, ((w 0).2.1, old')) *
        futureCylinderWeight 0 (k + 1) (fun i => b (i + 1)) w = _
      rw [hw]
    _ = b 0 (0, (x, old')) * (∫⁻ w, futureCylinderWeight 0 (k + 1) (fun i => b (i + 1)) w
        ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)) :=
      lintegral_const_mul _ (measurable_futureCylinderWeight 0 (k + 1)
        (fun i => b (i + 1)) (fun i => hb (i + 1)))
    _ = _ := congrArg (fun t : ℝ≥0∞ => b 0 (0, (x, old')) * t) hv

/-- Replacing only the coordinate-zero mark pushes the actual constructed
event law to the actual event law with the new sentinel. -/
theorem marked_eventLaw_replaceSentinel (C : HybridCTMC.Channels S R) {Lam : ℝ}
    (hLam : 0 < Lam) (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (x : S) (old old' : Option R) :
    ((MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)).map (replaceSentinel old') =
      (MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old') := by
  let μ := ((MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old)).map (replaceSentinel old')
  let ν := (MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old')
  let : IsFiniteMeasure μ := by unfold μ; infer_instance
  have hbox (I : Finset ℕ) (t : ℕ → Set (ℝ × (S × Option R)))
      (ht : ∀ i, MeasurableSet (t i)) : μ ((I : Set ℕ).pi t) = ν ((I : Set ℕ).pi t) := by
    let b : ℕ → ℝ × (S × Option R) → ℝ≥0∞ := fun i z =>
      if i ∈ I then (if z ∈ t i then 1 else 0) else 1
    have hb (i : ℕ) : Measurable (b i) := by
      by_cases hi : i ∈ I
      · simp only [b, hi, ite_true]
        exact Measurable.ite (ht i) measurable_const measurable_const
      · simpa only [b, hi, ite_false] using
          (measurable_const : Measurable (fun _ : ℝ × (S × Option R) => (1 : ℝ≥0∞)))
    have hm := measurable_fullCylinderWeight (I.sup id + 2) b hb
    have hs : MeasurableSet ((I : Set ℕ).pi t) :=
      MeasurableSet.pi I.countable_toSet (fun i _ => ht i)
    have he : fullCylinderWeight (I.sup id + 2) b =
        ((I : Set ℕ).pi t).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext w
      exact paddedBoxWeight_indicator I t w
    calc
      _ = ∫⁻ w, fullCylinderWeight (I.sup id + 2) b w ∂μ := by
        rw [he, lintegral_indicator hs]
        simp
      _ = ∫⁻ w, fullCylinderWeight (I.sup id + 2) b (replaceSentinel old' w)
          ∂(MarkedKernel.kernel C hLam bound).eventLaw Lam hLam (x, old) :=
        lintegral_map hm (measurable_replaceSentinel old')
      _ = b 0 (0, (x, old')) * futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam
          (fun i => b (i + 1)) (I.sup id + 1) (fun _ => 1) (x, old) :=
        marked_replacedCylinder_value C hLam bound x old old' (I.sup id) b hb
      _ = b 0 (0, (x, old')) * futureCylinderValue (MarkedKernel.kernel C hLam bound) Lam
          (fun i => b (i + 1)) (I.sup id + 1) (fun _ => 1) (x, old') :=
        congrArg (fun z : ℝ≥0∞ => b 0 (0, (x, old')) * z)
          (marked_futureValue_sentinel C hLam bound (fun i => b (i + 1))
            (I.sup id) (fun _ => 1) x old old')
      _ = ∫⁻ w, fullCylinderWeight (I.sup id + 2) b w ∂ν :=
        (marked_fullCylinder_value C hLam bound x old' (I.sup id) b hb).symm
      _ = _ := by rw [he, lintegral_indicator hs]; simp
  apply ext_of_generate_finite
    (squareCylinders (fun _ : ℕ => {s : Set (ℝ × (S × Option R)) | MeasurableSet s}))
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (by
        intro i
        change MeasurableSet (Set.univ : Set (ℝ × (S × Option R)))
        exact MeasurableSet.univ))
  · rintro B ⟨I, t, ht, rfl⟩
    exact hbox I t (fun i => ht i (mem_univ i))
  · simp

end Generic

section CF3

open FunctionalCapacity CF3Marked CF3RawPathLift

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

theorem cf3_eventLaw_replaceSentinel {p : Par} (hp : p.Valid) (x : CoreState p)
    (old old' : Option (Mark p)) :
    (CF3MarkedKernel.eventLaw hp x old).map (replaceSentinel old') =
      CF3MarkedKernel.eventLaw hp x old' :=
  marked_eventLaw_replaceSentinel (coreChannels hp) (CF3MarkedKernel.rate_positive hp)
    (CF3MarkedKernel.core_channel_bound hp) x old old'

/-- The raw source fold never interprets the coordinate-zero sentinel. -/
theorem rawAt_replaceSentinel (p : Par) (x : SourceState p) (w : MarkedPath p)
    (old' : Option (Mark p)) (n : ℕ) :
    rawAt p x (replaceSentinel old' w) n = rawAt p x w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change sourceProposalNext p (rawAt p x (replaceSentinel old' w) n) (w (n + 1)).2.2 =
        sourceProposalNext p (rawAt p x w n) (w (n + 1)).2.2
      rw [ih]

theorem rawSequence_replaceSentinel (p : Par) (x : SourceState p) (w : MarkedPath p)
    (old' : Option (Mark p)) :
    rawSequence p x (replaceSentinel old' w) = rawSequence p x w := by
  funext n
  change ((replaceSentinel old' w n).1, rawAt p x (replaceSentinel old' w) n) =
    ((w n).1, rawAt p x w n)
  rw [replaceSentinel_hold, rawAt_replaceSentinel]

/-- Exact whole raw-law sentinel erasure. This identifies physical-restart
last-mark sentinels with operated segments initialized using `none`. -/
theorem rawLiftLaw_sentinel {p : Par} (hp : p.Valid) (x : SourceState p)
    (old old' : Option (Mark p)) : rawLiftLaw hp x old = rawLiftLaw hp x old' := by
  have h := congrArg (fun μ : Measure (MarkedPath p) => μ.map (rawSequence p x))
    (cf3_eventLaw_replaceSentinel hp (coreProject x) old old')
  rw [Measure.map_map (measurable_rawSequence p x) (measurable_replaceSentinel old')] at h
  have he : rawSequence p x ∘ replaceSentinel old' = rawSequence p x := by
    funext w
    exact rawSequence_replaceSentinel p x w old'
  rw [he] at h
  exact h

theorem rawLiftLaw_none {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) : rawLiftLaw hp x old = rawLiftLaw hp x none :=
  rawLiftLaw_sentinel hp x old none

end CF3

end
end CTMCHeredity20261019.V2.SentinelErasure
