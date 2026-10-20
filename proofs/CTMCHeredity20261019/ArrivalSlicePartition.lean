module

public import proofs.CTMCHeredity20261019.PhysicalTimedCut

@[expose] public section

/-!
# Arrival slices partition the actual physical-time event law

Slices use the source `arrivalTime` and the source `clockIndex`. Their unique
index is obtained from the existing segment characterization. Nonnegative
infinite sums and integrals are then decomposed without a summability premise.
The actual source event law supplies coverage via its proved unbounded arrivals.
-/

namespace CTMCHeredity20261019

noncomputable section
open HybridCTMC.Kernel MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {S : Type*}

def arrivalSlice (T : ℝ) (n : ℕ) (w : ℕ → ℝ × S) : Prop :=
  arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w

/-- Each occupied slice has exactly the source clock index. This reuses the
source characterization instead of introducing a new count/index function. -/
theorem arrivalSlice_index (T : ℝ) (n : ℕ) (w : ℕ → ℝ × S)
    (hn : arrivalSlice T n w) : n = clockIndex T w :=
  (clockIndex_eq_of_between w n hn.1 hn.2).symm

theorem arrivalSlice_unique (T : ℝ) (n m : ℕ) (w : ℕ → ℝ × S)
    (hn : arrivalSlice T n w) (hm : arrivalSlice T m w) : n = m :=
  (arrivalSlice_index T n w hn).trans (arrivalSlice_index T m w hm).symm

/-- Every nonnegative horizon crossed by the source arrivals belongs to the
unique slice indexed by its actual source clock index. -/
theorem arrivalSlice_existsUnique (T : ℝ) (hT : 0 ≤ T) (w : ℕ → ℝ × S)
    (hex : ∃ m : ℕ, T < arrivalTime m w) : ∃! n : ℕ, arrivalSlice T n w := by
  refine ⟨clockIndex T w, clockIndex_segment hT w hex, ?_⟩
  intro n hn
  exact arrivalSlice_index T n w hn

theorem arrivalSlice_iff_clockIndex (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (w : ℕ → ℝ × S) (hex : ∃ m : ℕ, T < arrivalTime m w) :
    arrivalSlice T n w ↔ n = clockIndex T w := by
  constructor
  · exact arrivalSlice_index T n w
  · intro hn
    subst n
    exact clockIndex_segment hT w hex

/-- Slice-weight an arbitrary nonnegative observable. -/
def arrivalSliceValue (T : ℝ) (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞)
    (n : ℕ) (w : ℕ → ℝ × S) : ℝ≥0∞ :=
  if arrivalSlice T n w then H n w else 0

/-- Pointwise exact partition: only the actual source clock-index slice
contributes, even if the arbitrary observable takes the value infinity. -/
theorem tsum_arrivalSliceValue (T : ℝ) (hT : 0 ≤ T)
    (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞) (w : ℕ → ℝ × S)
    (hex : ∃ m : ℕ, T < arrivalTime m w) :
    (∑' n : ℕ, arrivalSliceValue T H n w) = H (clockIndex T w) w := by
  classical
  calc
    _ = arrivalSliceValue T H (clockIndex T w) w :=
      tsum_eq_single (clockIndex T w) (fun n hn => by
        apply ite_eq_right
        intro hs
        exact hn (arrivalSlice_index T n w hs))
    _ = _ := ite_eq_left (clockIndex_segment hT w hex)

section Measurability

variable [MeasurableSpace S]

theorem measurableSet_arrivalSlice (T : ℝ) (n : ℕ) :
    MeasurableSet {w : ℕ → ℝ × S | arrivalSlice T n w} :=
  measurableSet_physicalCut_segment n T

theorem measurable_arrivalSliceValue (T : ℝ)
    (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞) (hH : ∀ n, Measurable (H n)) (n : ℕ) :
    Measurable (arrivalSliceValue T H n) := by
  apply Measurable.ite (measurableSet_arrivalSlice T n) (hH n) measurable_const

/-- The clock-index-selected observable is measurable by countably many
source-index cases. -/
theorem measurable_clockIndex_select (T : ℝ)
    (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞) (hH : ∀ n, Measurable (H n)) :
    Measurable (fun w : ℕ → ℝ × S => H (clockIndex T w) w) := by
  have hm : Measurable (fun z : (ℕ → ℝ × S) × ℕ => H z.2 z.1) :=
    measurable_from_prod_countable_left hH
  exact hm.comp (measurable_id.prodMk (measurable_clockIndex T))

end Measurability

section ActualLaw

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S]

/-- Nonnegative integral decomposition over the disjoint, exhaustive arrival
slices of the actual source event law. Source-law coverage is discharged here
from its proved almost-sure unbounded arrivals. -/
theorem lintegral_arrivalSlice_partition (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (T : ℝ) (hT : 0 ≤ T)
    (H : ℕ → (ℕ → ℝ × S) → ℝ≥0∞) (hH : ∀ n, Measurable (H n)) :
    (∫⁻ w, H (clockIndex T w) w ∂K.eventLaw Λ hΛ x) =
      ∑' n : ℕ, ∫⁻ w, arrivalSliceValue T H n w ∂K.eventLaw Λ hΛ x := by
  calc
    _ = ∫⁻ w, ∑' n : ℕ, arrivalSliceValue T H n w ∂K.eventLaw Λ hΛ x :=
      lintegral_congr_ae (by
        filter_upwards [ae_arrivals_unbounded K hΛ x] with w hw
        exact (tsum_arrivalSliceValue T hT H w (hw T)).symm)
    _ = _ := lintegral_tsum (fun n =>
      (measurable_arrivalSliceValue T H hH n).aemeasurable)

/-- The exact form needed to sum physical-cut slice laws: an arbitrary
measurable observable of the full actual future sequence is the sum of its
deterministic-index residual-cut observables on the corresponding slices. -/
theorem lintegral_physicalTimedCut_partition (K : HybridCTMC.Kernel S) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : S) (T : ℝ) (hT : 0 ≤ T)
    (G : (ℕ → ℝ × S) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ w, G (physicalTimedCut T w) ∂K.eventLaw Λ hΛ x) =
      ∑' n : ℕ, ∫⁻ w,
        (if arrivalSlice T n w then G (physicalCut w n T) else 0)
          ∂K.eventLaw Λ hΛ x := by
  exact lintegral_arrivalSlice_partition K hΛ x T hT
    (fun n w => G (physicalCut w n T))
    (fun n => hG.comp (measurable_physicalCut n T))

end ActualLaw

end

end CTMCHeredity20261019
