module

public import P161Formal.StrongPopulationWitness
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Push

/-! The seed-free chemical rate envelope, including all foreign-species fuel
consumption, and its comparison with the checked recovery rows. The expression
below spells out the coordinate chemistry. Equality with the source channel
sum is a separate operation-expansion lemma; no stochastic law is assumed. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def foreignChemicalRate (counts : SpeciesId → Fin 2049) (j : SpeciesId) : ℝ :=
  ∑ k ∈ Finset.univ.erase j,
    (4000000*((counts k).val : ℝ)/2048 +
      800*(counts k).val*(1-((counts k).val : ℝ)/2048) + 400*(counts k).val)

theorem single_foreign_chemical_rate_bound (a : Fin 2049) :
    4000000*(a.val : ℝ)/2048 +
      800*a.val*(1-(a.val : ℝ)/2048) + 400*a.val ≤ 4819200 := by
  have ha : (a.val : ℝ) ≤ 2048 := by
    have h : a.val ≤ 2048 := by have h := a.isLt; omega
    exact_mod_cast h
  have ha0 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
  have hfactor : 0 ≤ (1-(a.val : ℝ)/2048)*
      (4000000+1638400*(1/2-(a.val : ℝ)/2048)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hfactor]

theorem foreign_chemical_rate_bound (counts : SpeciesId → Fin 2049) (j : SpeciesId) :
    foreignChemicalRate counts j ≤ 9638400 := by
  have h := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun k _ => single_foreign_chemical_rate_bound (counts k))
  have hcard : (Finset.univ.erase j).card = 2 := by simp
  norm_num only [foreignChemicalRate,Finset.sum_const,hcard,nsmul_eq_mul,
    Nat.cast_ofNat] at h ⊢
  exact h

def chemicalReferenceReal (H : ℕ → Bool → ℝ) (a : ℕ) (fuel : Bool) : ℝ :=
  if fuel then
    (a : ℝ)*(H (a-1) true-H a true) +
    800*a*(1-(a : ℝ)/2048)*(H (a+1) false-H a true) +
    400*a*(H (a-1) false-H a true) +
    (4000000*(3+(a : ℝ)/2048)+800*2048)*(H a false-H a true)
  else (a : ℝ)*(H (a-1) false-H a false) +
    4000000*(H a true-H a false)

def chemicalCoordinateExpression (H : ℕ → Bool → ℝ)
    (counts : SpeciesId → Fin 2049) (j : SpeciesId) (fuel : Bool) : ℝ :=
  let a := (counts j).val
  if fuel then
    (a : ℝ)*(H (a-1) true-H a true) +
    800*a*(1-(a : ℝ)/2048)*(H (a+1) false-H a true) +
    400*a*(H (a-1) false-H a true) +
    (4000000*(1+(a : ℝ)/2048)+foreignChemicalRate counts j)*(H a false-H a true)
  else (a : ℝ)*(H (a-1) false-H a false) +
    4000000*(H a true-H a false)

theorem chemical_coordinate_le_reference (H : ℕ → Bool → ℝ)
    (counts : SpeciesId → Fin 2049) (j : SpeciesId) (fuel : Bool)
    (hgap : H (counts j).val true ≤ H (counts j).val false) :
    chemicalCoordinateExpression H counts j fuel ≤
      chemicalReferenceReal H (counts j).val fuel := by
  cases fuel
  · rfl
  · have hforeign := foreign_chemical_rate_bound counts j
    dsimp [chemicalCoordinateExpression,chemicalReferenceReal]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgap)
      (sub_nonneg.mpr hforeign)]

abbrev strongRecoveryWitness (a : ℕ) (fuel : Bool) : ℝ := strongRecoveryWitnessQ a fuel

theorem chemical_reference_cast (H : ℕ → Bool → ℚ) (a : ℕ) (fuel : Bool) :
    (chemicalReferenceForQ H a fuel : ℝ) =
      chemicalReferenceReal (fun a fuel => (H a fuel : ℝ)) a fuel := by
  cases fuel <;> simp [chemicalReferenceForQ,chemicalReferenceReal]

theorem selected_chemical_expression_bound
    (counts : SpeciesId → Fin 2049) (j : SpeciesId) (fuel : Bool)
    (hfloor : 16 ≤ (counts j).val) :
    chemicalCoordinateExpression strongRecoveryWitness counts j fuel +
      220*strongRecoveryWitness (counts j).val fuel ≤
        if (counts j).val < 512 then 0 else 1/4700 := by
  have hb : (counts j).val ≤ 2048 := by have h := (counts j).isLt; omega
  have hshape := strong_witness_shape (counts j).val hfloor hb
  have hgap : strongRecoveryWitness (counts j).val true ≤
      strongRecoveryWitness (counts j).val false := by
    exact_mod_cast hshape.2.1
  have hrefQ := strong_reference_chemical_bound (counts j).val fuel hfloor hb
  have href : chemicalReferenceReal strongRecoveryWitness (counts j).val fuel +
      220*strongRecoveryWitness (counts j).val fuel ≤
        if (counts j).val < 512 then 0 else 1/4700 := by
    have hcast : (chemicalReferenceForQ strongRecoveryWitnessQ (counts j).val fuel : ℝ) +
        220*(strongRecoveryWitnessQ (counts j).val fuel : ℝ) ≤
          if (counts j).val < 512 then 0 else 1/4700 := by
      have hreal := (Rat.cast_le (K := ℝ)).mpr hrefQ
      simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_zero,
        Rat.cast_one,Rat.cast_div,apply_ite] using hreal
    simpa only [chemical_reference_cast,strongRecoveryWitness] using hcast
  have hcompare := chemical_coordinate_le_reference strongRecoveryWitness counts j fuel hgap
  linarith

end
end P161Formal
