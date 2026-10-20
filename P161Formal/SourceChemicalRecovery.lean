module

public import P161Formal.SourceContractBridge
public import P161Formal.ChemicalDriftBounds

/-! Exact expansion of the literal seed-free chemical channel sum and the
checked selected-witness drift bound. Natural q/nd ledgers are arbitrary.
Division gain and the stopped probability estimate are separate obligations. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def sourceChemicalCoordinateDrift (H : ℕ → Bool → ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℝ :=
  ∑ k, (FunctionalCapacity.cf3 (literalSourcePar 0)).rc s k *
    (H (((FunctionalCapacity.cf3 (literalSourcePar 0)).tc s k).a j).val
      ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc s k).R - H (s.a j).val s.R)

theorem capped_birth_difference (H : ℕ → Bool → ℝ) (a : Fin 2049) (b : Bool) (z : ℝ) :
    800*(a.val : ℝ)*(1-(a.val : ℝ)/2048)*
        (H (min (a.val+1) 2048) b-z) =
      800*(a.val : ℝ)*(1-(a.val : ℝ)/2048)*(H (a.val+1) b-z) := by
  by_cases h : a.val = 2048
  · norm_num [h]
  · have hle : a.val+1 ≤ 2048 := by have hlt := a.isLt; omega
    rw [Nat.min_eq_left hle]

theorem source_chemical_coordinate_expansion (H : ℕ → Bool → ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    sourceChemicalCoordinateDrift H s j =
      chemicalCoordinateExpression H s.a j s.R := by
  unfold sourceChemicalCoordinateDrift
  rw [FunctionalCapacity.cf3_chem_sum (literalSourcePar 0) s
    (fun z => H (z.a j).val z.R-H (s.a j).val s.R)]
  fin_cases j <;> cases hR : s.R <;>
    simp [chemicalCoordinateExpression,foreignChemicalRate,
      Finset.sum_erase_eq_sub (Finset.mem_univ _),
      literalSourcePar,FunctionalCapacity.Site.u,FunctionalCapacity.Site.r,hR,
      FunctionalCapacity.Site.inc,FunctionalCapacity.Site.dec,
      Function.update_apply,Fin.sum_univ_three]
  all_goals try rw [capped_birth_difference]
  all_goals ring

theorem source_recovery_chemical_bound (s : FunctionalCapacity.Site 3 2048)
    (j : SpeciesId) (hfloor : 16 ≤ (s.a j).val) :
    sourceChemicalCoordinateDrift strongRecoveryWitness s j +
      220*strongRecoveryWitness (s.a j).val s.R ≤
        if (s.a j).val < 512 then 0 else 1/4700 := by
  rw [source_chemical_coordinate_expansion]
  exact selected_chemical_expression_bound s.a j s.R hfloor

end
end P161Formal
