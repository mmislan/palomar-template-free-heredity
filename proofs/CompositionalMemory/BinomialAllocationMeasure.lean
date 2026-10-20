module

public import proofs.CompositionalMemory.BinomialAllocationMoments
public import Mathlib.Probability.Distributions.Poisson.Basic

@[expose] public section

namespace CompositionalMemory
open MeasureTheory HeritableCompositions

noncomputable def fairAllocationMeasure (n : ℕ) : Measure ℕ :=
  Measure.sum (fun k : Fin (n+1) => ENNReal.ofReal (fairBinomialWeight n k.val) • Measure.dirac k.val)

instance fairAllocationMeasure_probability (n : ℕ) : IsProbabilityMeasure (fairAllocationMeasure n) := by
  have hs : (∑ k : Fin (n+1),fairBinomialWeight n k.val)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => fairBinomialWeight n k)]
    exact fair_binomial_sum n
  have hh : HasSum (fun k : Fin (n+1) => fairBinomialWeight n k.val) 1 := by
    simpa only [hs] using hasSum_fintype (fun k : Fin (n+1) => fairBinomialWeight n k.val)
  exact hh.isProbabilityMeasure_sum_dirac (fun k => fairBinomialWeight_nonneg n k.val)

theorem fairAllocationMeasure_integrable (n : ℕ) (f : ℕ → ℝ) :
    Integrable f (fairAllocationMeasure n) := by
  unfold fairAllocationMeasure
  apply (integrable_sum_dirac_iff (by simp)).mpr
  exact (hasSum_fintype _).summable

theorem fairAllocationMeasure_integral (n : ℕ) (f : ℕ → ℝ) :
    (∫ k,f k ∂fairAllocationMeasure n)=
      ∑ k ∈ Finset.range (n+1),fairBinomialWeight n k*f k := by
  rw [fairAllocationMeasure,integral_sum_dirac (by simp),tsum_fintype]
  simp only [ENNReal.toReal_ofReal (fairBinomialWeight_nonneg n _),smul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun k => fairBinomialWeight n k*f k) (n+1)

theorem fairAllocationMeasure_centered_integral (n : ℕ) (f : ℝ → ℝ) :
    (∫ k,f ((k : ℝ)-(n : ℝ)/2) ∂fairAllocationMeasure n)=binomialAverage n f := by
  exact fairAllocationMeasure_integral n _

theorem binomial_actual_centered_moments (n : ℕ) :
    (∫ k,((k : ℝ)-(n : ℝ)/2) ∂fairAllocationMeasure n)=0 ∧
    (∫ k,((k : ℝ)-(n : ℝ)/2)^2 ∂fairAllocationMeasure n)=(n : ℝ)/4 ∧
    (∫ k,((k : ℝ)-(n : ℝ)/2)^3 ∂fairAllocationMeasure n)=0 ∧
    (∫ k,((k : ℝ)-(n : ℝ)/2)^4 ∂fairAllocationMeasure n)=(3*(n : ℝ)^2-2*n)/16 := by
  simpa only [binomialAverage,fairAllocationMeasure_integral] using binomial_centered_moments n

end CompositionalMemory
