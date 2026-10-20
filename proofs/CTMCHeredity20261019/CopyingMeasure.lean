module

public import proofs.CTMCHeredity20261019.CF3Copying
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! Actual probability laws for finite operation marks. No success-law premise. -/
namespace CTMCHeredity20261019
open FunctionalCapacity MeasureTheory
open scoped BigOperators Classical ENNReal
noncomputable section

def weightedPMF {I : Type*} [Fintype I] (w : I → ℝ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i), h1]
    simp)

theorem weightedPMF_event {I : Type*} [Fintype I] (w : I → ℝ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (A : I → Prop) :
    (weightedPMF w h0 h1).toOuterMeasure {i | A i} =
      ENNReal.ofReal (∑ i, w i * if A i then (1 : ℝ) else 0) := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (h0 i) (by split_ifs <;> norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : A i <;> simp [Set.indicator, weightedPMF, hi]

/-- One actual complementary count/fuel mark, with all zero-weight impossible
allocations retained as zero mass. -/
def cf3SplitPMF (p : Par) (s : Site p.c p.N) : PMF (Split p.c p.N) :=
  weightedPMF ((cf3 p).ps s) (cf3_ps_nonneg s) (cf3_ps_sum s)

def divisionCopyingFailure (p : Par) (s : Site p.c p.N)
    (k : Option (Fin p.c)) (o : Split p.c p.N) : Prop :=
  ∃ j, (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
    (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16

/-- Probability under the source mark law, with both outputs on the same draw. -/
theorem cf3_division_failure_probability_le {p : Par} (hc : p.c = 3)
    (s : Site p.c p.N) (k : Option (Fin p.c))
    (hs : ∀ j, 512 ≤ (s.a j : ℕ)) :
    (cf3SplitPMF p ((cf3 p).td s k)).toOuterMeasure
      {o | divisionCopyingFailure p s k o} ≤ ENNReal.ofReal (6 * Real.exp (-225)) := by
  rw [cf3SplitPMF, weightedPMF_event]
  apply ENNReal.ofReal_le_ofReal
  have he : (∑ o, (cf3 p).ps ((cf3 p).td s k) o *
      (if divisionCopyingFailure p s k o then (1 : ℝ) else 0)) =
      (∑ o, (cf3 p).ps ((cf3 p).td s k) o *
        (if ∃ j, (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
          (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16
        then (1 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro o _
    apply congrArg (fun a : ℝ => (cf3 p).ps ((cf3 p).td s k) o * a)
    by_cases h : divisionCopyingFailure p s k o
    · have ha : ∃ j, (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
          (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16 := h
      simp only [ite_eq_left h, ite_eq_left ha]
    · have ha : ¬∃ j, (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
          (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16 := h
      simp only [ite_eq_right h, ite_eq_right ha]
  rw [he]
  exact cf3_actual_division_copying_three hc s k hs

set_option maxHeartbeats 2000000 in
theorem canonical_copying_probability (s : Site 3 2048) (k : Option (Fin 3))
    (hs : ∀ j, 512 ≤ (s.a j : ℕ)) :
    (cf3SplitPMF canonicalSeedFreeCF3 ((cf3 canonicalSeedFreeCF3).td s k)).toOuterMeasure
      {o | divisionCopyingFailure canonicalSeedFreeCF3 s k o} ≤
        ENNReal.ofReal (6 * Real.exp (-225)) :=
  cf3_division_failure_probability_le (p := canonicalSeedFreeCF3) rfl s k hs

end
end CTMCHeredity20261019
