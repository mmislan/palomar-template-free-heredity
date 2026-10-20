module

public import proofs.CompositionalMemory.BinomialAllocationMeasure
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! Exponential concentration for the repository's fair allocation law. -/
namespace TemplateFreeHeredity

open MeasureTheory ProbabilityTheory CompositionalMemory Real
noncomputable section

def fairCenteredMGF (n : ℕ) (t : ℝ) : ℝ :=
  binomialAverage n (fun x => exp (t * x))

theorem fairCenteredMGF_zero (t : ℝ) : fairCenteredMGF 0 t = 1 := by
  simp [fairCenteredMGF, binomialAverage, HeritableCompositions.fairBinomialWeight]

theorem fairCenteredMGF_succ (n : ℕ) (t : ℝ) :
    fairCenteredMGF (n+1) t = fairCenteredMGF n t * cosh (t/2) := by
  rw [fairCenteredMGF, binomialAverage_succ]
  have hm : binomialAverage n (fun x => exp (t * (x-1/2))) =
      exp (-t/2) * fairCenteredMGF n t := by
    have he : (fun x : ℝ => exp (t * (x-1/2))) =
        fun x => exp (-t/2) * exp (t*x) := by
      funext x
      rw [← exp_add]
      congr 1
      ring
    rw [he, binomialAverage_scale]
    rfl
  have hp : binomialAverage n (fun x => exp (t * (x+1/2))) =
      exp (t/2) * fairCenteredMGF n t := by
    have he : (fun x : ℝ => exp (t * (x+1/2))) =
        fun x => exp (t/2) * exp (t*x) := by
      funext x
      rw [← exp_add]
      congr 1
      ring
    rw [he, binomialAverage_scale]
    rfl
  rw [hm, hp, cosh_eq]
  ring

theorem fairCenteredMGF_eq_cosh_pow (n : ℕ) (t : ℝ) :
    fairCenteredMGF n t = cosh (t/2)^n := by
  induction n with
  | zero => simp [fairCenteredMGF_zero]
  | succ n ih => rw [fairCenteredMGF_succ, ih, pow_succ]

theorem fairCenteredMGF_le_exp (n : ℕ) (t : ℝ) :
    fairCenteredMGF n t ≤ exp ((n : ℝ) * t^2 / 8) := by
  rw [fairCenteredMGF_eq_cosh_pow]
  have hc := cosh_le_exp_half_sq (t/2)
  have hp : 0 ≤ cosh (t/2) := (cosh_pos _).le
  calc
    cosh (t/2)^n ≤ (exp ((t/2)^2/2))^n := pow_le_pow_left₀ hp hc n
    _ = exp ((n : ℝ) * t^2 / 8) := by
      rw [← exp_nat_mul]
      congr 1
      ring

theorem fairAllocation_mgf (n : ℕ) (t : ℝ) :
    mgf (fun a : ℕ => (a : ℝ) - (n : ℝ)/2)
      (CompositionalMemory.fairAllocationMeasure n) t = fairCenteredMGF n t := by
  simpa [mgf, fairCenteredMGF] using
    (CompositionalMemory.fairAllocationMeasure_centered_integral n
      (fun x : ℝ => exp (t * x)))

theorem fairAllocation_upper_tail (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (CompositionalMemory.fairAllocationMeasure n).real
      {a : ℕ | δ ≤ (a : ℝ) - (n : ℝ)/2} ≤
        exp (-2 * δ^2 / n) := by
  let t : ℝ := 4 * δ / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hi : Integrable (fun a : ℕ => exp (t * ((a : ℝ) - (n : ℝ)/2)))
      (CompositionalMemory.fairAllocationMeasure n) :=
    CompositionalMemory.fairAllocationMeasure_integrable n _
  have hc := measure_ge_le_exp_mul_mgf δ ht hi
  rw [fairAllocation_mgf] at hc
  calc
    (CompositionalMemory.fairAllocationMeasure n).real
        {a : ℕ | δ ≤ (a : ℝ) - (n : ℝ)/2} ≤
      exp (-t * δ) * fairCenteredMGF n t := hc
    _ ≤ exp (-t * δ) * exp ((n : ℝ) * t^2 / 8) := by
      exact mul_le_mul_of_nonneg_left (fairCenteredMGF_le_exp n t) (exp_pos _).le
    _ = exp (-2 * δ^2 / n) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

theorem fairAllocation_lower_tail (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (CompositionalMemory.fairAllocationMeasure n).real
      {a : ℕ | (a : ℝ) - (n : ℝ)/2 ≤ -δ} ≤
        exp (-2 * δ^2 / n) := by
  let t : ℝ := -(4 * δ / n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have ht : t ≤ 0 := by
    dsimp [t]
    have h : 0 ≤ 4 * δ / (n : ℝ) := by positivity
    linarith
  have hi : Integrable (fun a : ℕ => exp (t * ((a : ℝ) - (n : ℝ)/2)))
      (CompositionalMemory.fairAllocationMeasure n) :=
    CompositionalMemory.fairAllocationMeasure_integrable n _
  have hc := measure_le_le_exp_mul_mgf (-δ) ht hi
  rw [fairAllocation_mgf] at hc
  calc
    (CompositionalMemory.fairAllocationMeasure n).real
        {a : ℕ | (a : ℝ) - (n : ℝ)/2 ≤ -δ} ≤
      exp (-t * -δ) * fairCenteredMGF n t := hc
    _ ≤ exp (-t * -δ) * exp ((n : ℝ) * t^2 / 8) := by
      exact mul_le_mul_of_nonneg_left (fairCenteredMGF_le_exp n t) (exp_pos _).le
    _ = exp (-2 * δ^2 / n) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

theorem fairAllocation_two_sided_tail (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (CompositionalMemory.fairAllocationMeasure n).real
      {a : ℕ | δ ≤ |(a : ℝ) - (n : ℝ)/2|} ≤
        2 * exp (-2 * δ^2 / n) := by
  let μ := CompositionalMemory.fairAllocationMeasure n
  let upper : Set ℕ := {a | δ ≤ (a : ℝ) - (n : ℝ)/2}
  let lower : Set ℕ := {a | (a : ℝ) - (n : ℝ)/2 ≤ -δ}
  have hsub : {a : ℕ | δ ≤ |(a : ℝ) - (n : ℝ)/2|} ⊆ upper ∪ lower := by
    intro a ha
    rcases le_total 0 ((a : ℝ) - (n : ℝ)/2) with h | h
    · left
      simpa only [upper, Set.mem_ofPred_eq, abs_of_nonneg h] using ha
    · right
      change (a : ℝ) - (n : ℝ)/2 ≤ -δ
      change δ ≤ |(a : ℝ) - (n : ℝ)/2| at ha
      rw [abs_of_nonpos h] at ha
      linarith
  calc
    μ.real {a : ℕ | δ ≤ |(a : ℝ) - (n : ℝ)/2|} ≤
        μ.real (upper ∪ lower) := measureReal_mono hsub (by finiteness)
    _ ≤ μ.real upper + μ.real lower := measureReal_union_le upper lower
    _ ≤ 2 * exp (-2 * δ^2 / n) := by
      have hu := fairAllocation_upper_tail n hn δ hδ
      have hl := fairAllocation_lower_tail n hn δ hδ
      change μ.real upper ≤ _ at hu
      change μ.real lower ≤ _ at hl
      linarith

end
end TemplateFreeHeredity
