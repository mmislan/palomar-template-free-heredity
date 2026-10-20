module

public import P161Formal.Contract
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Uniform bounds on the explicit rates in the independent physical contract.
These bounds count actual channels, including state-null division marks.
Normalization of the complete split kernel and the path adapter are separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem copies_bounds (x : Population) (i : SiteId) (j : SpeciesId) :
    0 ≤ copies x i j ∧ copies x i j ≤ 2048 := by
  have hn : (x.count i j).val ≤ 2048 := by have h := (x.count i j).isLt; omega
  unfold copies
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast hn⟩

theorem fuel_weight_bounds (x : Population) (i : SiteId) :
    0 ≤ fueled x i ∧ fueled x i ≤ 1 := by
  unfold fueled
  split <;> norm_num

theorem triggered_division_rate_bounds (x : Population) (i : SiteId) (j : SpeciesId) :
    0 ≤ divisionRate x i (some j) ∧ divisionRate x i (some j) ≤ 1 := by
  obtain ⟨ha0,ha1⟩ := copies_bounds x i j
  obtain ⟨hf0,hf1⟩ := fuel_weight_bounds x i
  change 0 ≤ fueled x i * copies x i j / 2048 ∧ fueled x i * copies x i j / 2048 ≤ 1
  have hmul := mul_le_mul hf1 ha1 ha0 (by norm_num : (0 : ℝ) ≤ 1)
  constructor
  · positivity
  · nlinarith

def siteDivisionIntensity (x : Population) (i : SiteId) : ℝ :=
  divisionRate x i none + ∑ j : SpeciesId, divisionRate x i (some j)

theorem site_division_intensity_bounds (x : Population) (i : SiteId) :
    1 ≤ siteDivisionIntensity x i ∧ siteDivisionIntensity x i ≤ 4 := by
  have h0 : (0 : ℝ) ≤ ∑ j : SpeciesId, divisionRate x i (some j) :=
    Finset.sum_nonneg (fun j _ => (triggered_division_rate_bounds x i j).1)
  have h1 := Finset.sum_le_sum (fun (j : SpeciesId) (_ : j ∈ Finset.univ) =>
    (triggered_division_rate_bounds x i j).2)
  norm_num at h1
  change 1 ≤ 1 + (∑ j : SpeciesId, divisionRate x i (some j)) ∧
    1 + (∑ j : SpeciesId, divisionRate x i (some j)) ≤ 4
  constructor <;> linarith

theorem total_division_intensity_bounds (x : Population) :
    4 ≤ ∑ i : SiteId, siteDivisionIntensity x i ∧
    (∑ i : SiteId, siteDivisionIntensity x i) ≤ 16 := by
  constructor
  · have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) =>
      (site_division_intensity_bounds x i).1)
    norm_num at h
    exact h
  · have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) =>
      (site_division_intensity_bounds x i).2)
    norm_num at h
    exact h

theorem accepted_feed_intensity_bounds (t : ℝ) (x : Population) :
    0 ≤ ∑ i : SiteId, chemicalRate t x (.recharge i) ∧
    (∑ i : SiteId, chemicalRate t x (.recharge i)) ≤ 16000000 := by
  have hrow (i : SiteId) : 0 ≤ chemicalRate t x (.recharge i) ∧
      chemicalRate t x (.recharge i) ≤ 4000000 := by
    obtain ⟨hf0,hf1⟩ := fuel_weight_bounds x i
    change 0 ≤ 4000000 * (1 - fueled x i) ∧ 4000000 * (1 - fueled x i) ≤ 4000000
    constructor <;> linarith
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hrow i).1)
  · have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) => (hrow i).2)
    norm_num at h
    exact h

theorem seed_coefficient_bounds (t : ℝ) :
    0 ≤ seedCoefficient t ∧ seedCoefficient t ≤ 6 := by
  unfold seedCoefficient
  split <;> norm_num

theorem accepted_seed_intensity_bounds (t : ℝ) (x : Population) :
    0 ≤ ∑ i : SiteId, ∑ j : SpeciesId, chemicalRate t x (.seed i j) ∧
    (∑ i : SiteId, ∑ j : SpeciesId, chemicalRate t x (.seed i j)) ≤ 72 := by
  have hrow (i : SiteId) (j : SpeciesId) : 0 ≤ chemicalRate t x (.seed i j) ∧
      chemicalRate t x (.seed i j) ≤ 6 := by
    obtain ⟨ha0,ha1⟩ := copies_bounds x i j
    obtain ⟨hs0,hs1⟩ := seed_coefficient_bounds t
    have hq0 : 0 ≤ 1 - copies x i j / 2048 := by linarith
    have hq1 : 1 - copies x i j / 2048 ≤ 1 := by linarith
    change 0 ≤ seedCoefficient t * (1 - copies x i j / 2048) ∧
      seedCoefficient t * (1 - copies x i j / 2048) ≤ 6
    constructor
    · exact mul_nonneg hs0 hq0
    · simpa only [mul_one] using mul_le_mul hs1 hq1 hq0 (by norm_num : (0 : ℝ) ≤ 6)
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hrow i j).1))
  · have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun (j : SpeciesId) (_ : j ∈ Finset.univ) => (hrow i j).2))
    norm_num at h
    exact h

end
end P161Formal
