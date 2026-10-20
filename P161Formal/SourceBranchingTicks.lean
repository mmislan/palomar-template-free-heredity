module

public import P161Formal.SourceTickBridge

/-! Concrete guard and acquisition tick inequalities for the two literal
seed phases, supplying the parameter-generic block induction. -/

@[expose] public section
namespace P161Formal
open FunctionalCapacity CTMCHeredity20261019
open scoped Classical
noncomputable section

theorem source_pre_guard_tick (x : BranchingSource) :
    (1-branchingOldPotential x)-8*(13/10000000)/cf3Rate (literalSourcePar 6) ≤
      (literalSourceKilled 6 (by norm_num) (sourceDead 16 branchingOldRequired)).P
        (fun y => 1-branchingOldPotential y) x := by
  apply source_killed_tick_guard 6 (by norm_num) (sourceDead 16 branchingOldRequired)
    branchingOldPotential (8*(13/10000000)) (by norm_num) branching_raw_old_floor_barrier
  intro y _hy
  have h := branching_source_old_seeded y
  have hn := branching_old_nonnegative y
  linarith

theorem source_post_guard_tick (x : BranchingSource) :
    (1-branchingAllPotential x)-12*(13/10000000)/cf3Rate (literalSourcePar 0) ≤
      (literalSourceKilled 0 le_rfl (sourceDead 16 Finset.univ)).P
        (fun y => 1-branchingAllPotential y) x := by
  apply source_killed_tick_guard 0 le_rfl (sourceDead 16 Finset.univ)
    branchingAllPotential (12*(13/10000000)) (by norm_num) branching_raw_all_floor_barrier
  intro y hy
  have h := branching_source_all_seed_free y
    (fun i j => branching_source_required_floor Finset.univ y hy i j (Finset.mem_univ j))
  have hn := branching_all_nonnegative y
  linarith

theorem source_candidate_tick (x : BranchingSource) :
    (literalSourceKilled 6 (by norm_num) (sourceDead 16 branchingOldRequired)).P
      (branchingSpeciesPotential 2) x ≤
        (1-(1/2)/cf3Rate (literalSourcePar 6))*branchingSpeciesPotential 2 x+
          4*(13/10000000)/cf3Rate (literalSourcePar 6) := by
  apply source_killed_tick_super 6 (by norm_num) (sourceDead 16 branchingOldRequired)
    (branchingSpeciesPotential 2) (1/2) (4*(13/10000000))
    (fun y => branching_species_nonnegative y 2)
    (by rw [source_common_clock.1]; norm_num) (by norm_num)
  intro y _hy
  have h := branching_source_species_seeded y 2
  nlinarith

theorem branching_old_potential_bdd : Bdd branchingOldPotential :=
  Bdd.of_le branching_old_nonnegative branching_old_max

theorem branching_all_potential_bdd : Bdd branchingAllPotential :=
  Bdd.of_le branching_all_nonnegative branching_all_max

theorem branching_candidate_potential_bdd : Bdd (branchingSpeciesPotential 2) :=
  Bdd.of_le (fun y => branching_species_nonnegative y 2) (fun y => branching_species_max y 2)

end
end P161Formal
