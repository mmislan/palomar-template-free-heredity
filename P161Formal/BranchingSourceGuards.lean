module

public import P161Formal.BranchingPopulationSource
public import proofs.CTMCHeredity20261019.MissionQuotient

/-! Bounded guard potentials, source floor predicates and ledger resets used
by the literal switched block event. No probability premise is introduced. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

def branchingOldRequired : Finset SpeciesId := {0,1}

theorem branching_source_required_floor (req : Finset SpeciesId) (x : BranchingSource)
    (hx : ¬sourceDead 16 req x) (i : SiteId) (j : SpeciesId) (hj : j ∈ req) :
    16 ≤ ((x i).a j).val := by
  by_contra hn
  exact hx ⟨i,j,hj,by omega⟩

theorem branching_old_max (x : BranchingSource) : branchingOldPotential x ≤ 640 := by
  have h0 := branching_species_max x 0
  have h1 := branching_species_max x 1
  unfold branchingOldPotential
  linarith

theorem branching_all_split (x : BranchingSource) :
    branchingAllPotential x = branchingOldPotential x+branchingSpeciesPotential 2 x := by
  simp only [branchingAllPotential,Fin.sum_univ_three,branchingOldPotential]

theorem branching_all_max (x : BranchingSource) : branchingAllPotential x ≤ 960 := by
  rw [branching_all_split]
  linarith [branching_old_max x,branching_species_max x 2]

theorem branching_raw_all_floor_barrier (x : BranchingSource)
    (hx : sourceDead 16 Finset.univ x) : 1 ≤ branchingAllPotential x := by
  obtain ⟨i,j,_hj,h⟩ := hx
  exact branching_all_underfloor_barrier x i j h

theorem branching_raw_old_floor_barrier (x : BranchingSource)
    (hx : sourceDead 16 branchingOldRequired x) : 1 ≤ branchingOldPotential x := by
  obtain ⟨i,j,hj,h⟩ := hx
  have hq := branching_underfloor_barrier ((x i).a j).val h (x i).R
  have hr : (1 : ℝ) ≤ branchingWitness ((x i).a j).val (x i).R := by
    unfold branchingWitness
    exact_mod_cast hq
  have hs := hr.trans (branching_witness_le_species x i j)
  have h0 := branching_species_nonnegative x 0
  have h1 := branching_species_nonnegative x 1
  simp only [branchingOldRequired,Finset.mem_insert,Finset.mem_singleton] at hj
  unfold branchingOldPotential
  rcases hj with hj | hj <;> subst j <;> linarith

theorem branching_old_reset_q (seed : ℝ) (x : BranchingSource) :
    branchingOldPotential (sourceResetQ (p := literalSourcePar seed) x) =
      branchingOldPotential x := rfl

theorem branching_all_reset_q (seed : ℝ) (x : BranchingSource) :
    branchingAllPotential (sourceResetQ (p := literalSourcePar seed) x) =
      branchingAllPotential x := rfl

theorem branching_species_reset_q (seed : ℝ) (x : BranchingSource) (j : SpeciesId) :
    branchingSpeciesPotential j (sourceResetQ (p := literalSourcePar seed) x) =
      branchingSpeciesPotential j x := rfl

theorem branching_old_reset_all (seed : ℝ) (x : BranchingSource) :
    branchingOldPotential (sourceResetAll (p := literalSourcePar seed) x) =
      branchingOldPotential x := rfl

theorem branching_all_reset_all (seed : ℝ) (x : BranchingSource) :
    branchingAllPotential (sourceResetAll (p := literalSourcePar seed) x) =
      branchingAllPotential x := rfl

theorem branching_species_reset_all (seed : ℝ) (x : BranchingSource) (j : SpeciesId) :
    branchingSpeciesPotential j (sourceResetAll (p := literalSourcePar seed) x) =
      branchingSpeciesPotential j x := rfl

end
end P161Formal
