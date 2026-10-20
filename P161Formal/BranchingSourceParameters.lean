module

public import P161Formal.SourceContractBridge
public import P161Formal.BranchingFueled
public import proofs.FunctionalCapacity.SiteCF3b

/-! Exact rational representation of the foreign loads of the literal beta4m
source. The full binomial moment and site operator are transported by casts;
no density, monotonicity or parameter-transfer premise is introduced. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def branchingForeignUQ (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℚ :=
  ∑ k : SpeciesId, if k = j then 0 else ((s.a k).val : ℚ)/2048

def branchingForeignHQ (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℚ :=
  ∑ k : SpeciesId, if k = j then 0 else
    4000000*((s.a k).val : ℚ)/2048+
      800*((s.a k).val : ℚ)*(3/2-((s.a k).val : ℚ)/2048)

def branchingForeignVQ (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℚ :=
  branchingForeignHQ s j-4000000*branchingForeignUQ s j

def branchingWitness (a : ℕ) (fuel : Bool) : ℝ := (branchingWitnessQ a fuel : ℝ)

theorem branching_foreign_U_cast (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    (branchingForeignUQ s j : ℝ) = FunctionalCapacity.Uf s j := by
  unfold branchingForeignUQ FunctionalCapacity.Uf FunctionalCapacity.Site.u
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> push_cast <;> rfl

theorem branching_foreign_H_cast (seed : ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    (branchingForeignHQ s j : ℝ) = FunctionalCapacity.Hf (literalSourcePar seed) s j := by
  simp [branchingForeignHQ,FunctionalCapacity.Hf,FunctionalCapacity.Site.u,literalSourcePar]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> push_cast <;> ring

theorem branching_foreign_load_bounds (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    0 ≤ branchingForeignUQ s j ∧ branchingForeignUQ s j ≤ 2 ∧
      0 ≤ branchingForeignVQ s j ∧ branchingForeignVQ s j ≤ 1843200 := by
  have hU0 := FunctionalCapacity.Uf_nonneg s j
  have hU1 := FunctionalCapacity.Uf_le s j
  have hH0 := FunctionalCapacity.Hf_ge (literal_source_valid 0 le_rfl) s j
  have hH1 := FunctionalCapacity.Hf_le (literal_source_valid 0 le_rfl) s j
  rw [←branching_foreign_U_cast s j] at hU0 hU1 hH0 hH1
  rw [←branching_foreign_H_cast 0 s j] at hH0 hH1
  norm_num only [literalSourcePar,Nat.cast_ofNat] at hU1 hH0 hH1
  have hV : (branchingForeignVQ s j : ℝ) =
      (branchingForeignHQ s j : ℝ)-4000000*(branchingForeignUQ s j : ℝ) := by
    simp [branchingForeignVQ]
  constructor
  · exact_mod_cast hU0
  constructor
  · exact_mod_cast hU1
  constructor
  · have h : (0 : ℝ) ≤ (branchingForeignVQ s j : ℝ) := by
      rw [hV]
      linarith
    exact_mod_cast h
  · have h : (branchingForeignVQ s j : ℝ) ≤ (1843200 : ℝ) := by
      rw [hV]
      linarith
    exact_mod_cast h

theorem branching_moment_cast (a : ℕ) (fuel : Bool) :
    (branchingMomentQ a fuel : ℝ) =
      FunctionalCapacity.binE (fun k => branchingWitness k fuel) a := by
  simp [branchingMomentQ,FunctionalCapacity.binE,branchingWitness]

theorem branching_site_operator_cast (a : ℕ) (fuel : Bool) (U v seed : ℚ) :
    (branchingSiteOperatorQ a fuel U v seed : ℝ) =
      FunctionalCapacity.siteOp (literalSourcePar (seed : ℝ)) branchingWitness a fuel
        (4000000*(U : ℝ)+(v : ℝ)) (U : ℝ) := by
  cases fuel <;>
    simp [branchingSiteOperatorQ,FunctionalCapacity.siteOp,
      branching_moment_cast,branchingWitness] <;> ring

end
end P161Formal
