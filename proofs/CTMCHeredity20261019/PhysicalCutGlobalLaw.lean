module

public import proofs.CTMCHeredity20261019.PhysicalCutLaw
public import proofs.CTMCHeredity20261019.ArrivalSlicePartition

@[expose] public section

/-!
# Global actual physical-time future law

The proved whole-suffix law on each arrival slice is summed using the proved
arrival partition. The result identifies the actual residual future with the
fresh actual event law from the source state at the physical cut time.

Measurable tests of the past are represented by an arbitrary measurable event
of the complete event prefix on each possible arrival-index slice. No Markov
or future-law premise is assumed: the per-slice identity is imported as a
theorem, and the actual source law supplies almost-sure slice coverage.
-/

namespace CTMCHeredity20261019

noncomputable section
open HybridCTMC.Kernel MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal Classical

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The expectation under a fresh actual source event law, indexed by its
prescribed current state. -/
def freshSuffixValue (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (y : S) : ℝ≥0∞ :=
  ∫⁻ v, F v ∂K.eventLaw Lam hLam y

theorem measurable_freshSuffixValue (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (F : (ℕ → ℝ × S) → ℝ≥0∞) :
    Measurable (freshSuffixValue K hLam F) := measurable_of_countable _

/-- The actual fresh event law has its prescribed coordinate-zero state. -/
theorem eventLaw_initial_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (y : S) (g : S → ℝ≥0∞) :
    (∫⁻ v, g (v 0).2 ∂K.eventLaw Lam hLam y) = g y := by
  calc
    _ = ∫⁻ _v, g y ∂K.eventLaw Lam hLam y := lintegral_congr_ae (by
      filter_upwards [K.ae_event_initial hLam y] with v hv
      simp only [hv])
    _ = _ := by simp

/-- On every physical arrival slice and every measurable complete-prefix
event, the actual whole future reward has the fresh-law conditional value.
The survival-weighted prefix mixture cancels by applying the proved slice law
also to the coordinate-zero reward of a fresh actual path. -/
theorem eventLaw_physicalCut_slice_fresh (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (A : Set (CutPrefix S n)) (hA : MeasurableSet A)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then F (physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x) =
    ∫⁻ w, if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A then
          freshSuffixValue K hLam F (w n).2 else 0 ∂K.eventLaw Lam hLam x := by
  have hr := eventLaw_physicalCut_full_suffix_reward K hLam x n T A hA F hF
  have hg : Measurable (fun v : ℕ → ℝ × S => freshSuffixValue K hLam F (v 0).2) :=
    (measurable_freshSuffixValue K hLam F).comp
      (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) 0).snd
  have hi := eventLaw_physicalCut_full_suffix_reward K hLam x n T A hA
    (fun v => freshSuffixValue K hLam F (v 0).2) hg
  simp only [physicalCut_zero, eventLaw_initial_lintegral] at hi
  exact hr.trans hi.symm

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Normalize the two indicators used by the generic arrival partition into
the precise slice-and-prefix-event form of the proved conditional slice law. -/
theorem arrivalSliceValue_prefix_ite (T : ℝ)
    (A : ∀ n : ℕ, Set (CutPrefix S n))
    (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞) (n : ℕ) (w : ℕ → ℝ × S) :
    arrivalSliceValue T
      (fun n w => if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A n then H n w else 0) n w =
    if (arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w) ∧
      frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A n then H n w else 0 := by
  by_cases hs : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w <;>
    simp [arrivalSliceValue, arrivalSlice, hs]

section Global

variable [StandardBorelSpace S]

/-- Global physical-time conditional future identity against every measurable
prefix-event family. The selected event may inspect the full observed prefix
on each source clock-index slice, including all preceding holds and states. -/
theorem eventLaw_physicalTimedCut_prefix_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) (hT : 0 ≤ T)
    (A : ∀ n : ℕ, Set (CutPrefix S n)) (hA : ∀ n, MeasurableSet (A n))
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × S) (clockIndex T w) w ∈ A (clockIndex T w)
        then F (physicalTimedCut T w) else 0 ∂K.eventLaw Lam hLam x) =
    ∫⁻ w, if frestrictLe (π := fun _ : ℕ => ℝ × S) (clockIndex T w) w ∈ A (clockIndex T w)
        then freshSuffixValue K hLam F (timedState T w) else 0 ∂K.eventLaw Lam hLam x := by
  let Hleft : ℕ → (ℕ → ℝ × S) → ℝ≥0∞ := fun n w =>
    if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A n then F (physicalCut w n T) else 0
  let Hright : ℕ → (ℕ → ℝ × S) → ℝ≥0∞ := fun n w =>
    if frestrictLe (π := fun _ : ℕ => ℝ × S) n w ∈ A n then
      freshSuffixValue K hLam F (w n).2 else 0
  have hleft (n : ℕ) : Measurable (Hleft n) :=
    Measurable.ite ((hA n).preimage (measurable_frestrictLe n))
      (hF.comp (measurable_physicalCut n T)) measurable_const
  have hright (n : ℕ) : Measurable (Hright n) :=
    Measurable.ite ((hA n).preimage (measurable_frestrictLe n))
      ((measurable_freshSuffixValue K hLam F).comp
        (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) n).snd) measurable_const
  calc
    _ = ∑' n : ℕ, ∫⁻ w, arrivalSliceValue T Hleft n w ∂K.eventLaw Lam hLam x :=
      lintegral_arrivalSlice_partition K hLam x T hT Hleft hleft
    _ = ∑' n : ℕ, ∫⁻ w, arrivalSliceValue T Hright n w ∂K.eventLaw Lam hLam x := by
      apply tsum_congr
      intro n
      simpa only [Hleft, Hright, arrivalSliceValue_prefix_ite] using
        eventLaw_physicalCut_slice_fresh K hLam x n T (A n) (hA n) F hF
    _ = _ := (lintegral_arrivalSlice_partition K hLam x T hT Hright hright).symm

/-- The actual entire physical-time future has the expectation of a fresh
actual event law from the actual state at the deterministic cut time. -/
theorem eventLaw_physicalTimedCut_fresh_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) (hT : 0 ≤ T)
    (F : (ℕ → ℝ × S) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (physicalTimedCut T w) ∂K.eventLaw Lam hLam x) =
      ∫⁻ w, freshSuffixValue K hLam F (timedState T w) ∂K.eventLaw Lam hLam x := by
  simpa only [Set.mem_univ, ite_true] using
    eventLaw_physicalTimedCut_prefix_reward K hLam x T hT
      (fun n => (Set.univ : Set (CutPrefix S n))) (fun _ => MeasurableSet.univ) F hF

/-- Equality of the whole actual future-sequence measure and the mixture of
fresh actual event laws indexed by the actual physical-time state. -/
theorem eventLaw_physicalTimedCut_map (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) (hT : 0 ≤ T) :
    (K.eventLaw Lam hLam x).map (physicalTimedCut T) =
      ((K.eventLaw Lam hLam x).map (timedState T)).bind
        (fun y => K.eventLaw Lam hLam y) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_physicalTimedCut T)]
  rw [Measure.lintegral_bind (measurable_of_countable
    (fun y : S => K.eventLaw Lam hLam y)).aemeasurable hF.aemeasurable]
  change (∫⁻ w, F (physicalTimedCut T w) ∂K.eventLaw Lam hLam x) =
    ∫⁻ y, freshSuffixValue K hLam F y ∂((K.eventLaw Lam hLam x).map (timedState T))
  rw [lintegral_map (measurable_freshSuffixValue K hLam F) (measurable_timedState T)]
  exact eventLaw_physicalTimedCut_fresh_reward K hLam x T hT F hF

end Global

end

end CTMCHeredity20261019
