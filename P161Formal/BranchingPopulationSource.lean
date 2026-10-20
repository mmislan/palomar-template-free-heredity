module

public import P161Formal.BranchingSourceDrift

/-! Population forms and witness barriers for acquisition and retention. The
seeded bound is global; the seed-free bound is imposed only on the applicable
current floor. These are generator statements, before physical-time transfer. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def branchingAllPotential (x : BranchingSource) : ℝ :=
  ∑ j : SpeciesId, branchingSpeciesPotential j x

def branchingOldPotential (x : BranchingSource) : ℝ :=
  branchingSpeciesPotential 0 x+branchingSpeciesPotential 1 x

theorem branching_species_nonnegative (x : BranchingSource) (j : SpeciesId) :
    0 ≤ branchingSpeciesPotential j x :=
  Finset.sum_nonneg (fun i _ => branching_witness_nonnegative ((x i).a j).val (x i).R)

theorem branching_all_nonnegative (x : BranchingSource) : 0 ≤ branchingAllPotential x :=
  Finset.sum_nonneg (fun j _ => branching_species_nonnegative x j)

theorem branching_old_nonnegative (x : BranchingSource) : 0 ≤ branchingOldPotential x :=
  add_nonneg (branching_species_nonnegative x 0) (branching_species_nonnegative x 1)

theorem branching_source_gen_add (seed : ℝ) (f g : BranchingSource → ℝ)
    (x : BranchingSource) :
    FunctionalCapacity.cf3Gen (literalSourcePar seed) (fun z => f z+g z) x =
      FunctionalCapacity.cf3Gen (literalSourcePar seed) f x+
        FunctionalCapacity.cf3Gen (literalSourcePar seed) g x :=
  FunctionalCapacity.popGen_add _ _ f g x

theorem branching_source_gen_all (seed : ℝ) (x : BranchingSource) :
    FunctionalCapacity.cf3Gen (literalSourcePar seed) branchingAllPotential x =
      ∑ j : SpeciesId,
        FunctionalCapacity.cf3Gen (literalSourcePar seed) (branchingSpeciesPotential j) x := by
  change FunctionalCapacity.cf3Gen (literalSourcePar seed)
    (fun z => ∑ j : SpeciesId, branchingSpeciesPotential j z) x = _
  simp only [Fin.sum_univ_three]
  rw [branching_source_gen_add,branching_source_gen_add]

theorem branching_source_all_seeded (x : BranchingSource) :
    FunctionalCapacity.cf3Gen (literalSourcePar 6) branchingAllPotential x ≤
      -branchingAllPotential x/2+12*(13/10000000) := by
  rw [branching_source_gen_all]
  calc
    _ ≤ ∑ j : SpeciesId, (-branchingSpeciesPotential j x/2+4*(13/10000000)) :=
      Finset.sum_le_sum (fun j _ => branching_source_species_seeded x j)
    _ = _ := by
      simp only [branchingAllPotential,Fin.sum_univ_three]
      ring

theorem branching_source_all_seed_free (x : BranchingSource)
    (hf : ∀ i : SiteId, ∀ j : SpeciesId, 16 ≤ ((x i).a j).val) :
    FunctionalCapacity.cf3Gen (literalSourcePar 0) branchingAllPotential x ≤
      -branchingAllPotential x/2+12*(13/10000000) := by
  rw [branching_source_gen_all]
  calc
    _ ≤ ∑ j : SpeciesId, (-branchingSpeciesPotential j x/2+4*(13/10000000)) :=
      Finset.sum_le_sum (fun j _ => branching_source_species_seed_free x j (fun i => hf i j))
    _ = _ := by
      simp only [branchingAllPotential,Fin.sum_univ_three]
      ring

theorem branching_source_old_seeded (x : BranchingSource) :
    FunctionalCapacity.cf3Gen (literalSourcePar 6) branchingOldPotential x ≤
      -branchingOldPotential x/2+8*(13/10000000) := by
  have h0 := branching_source_species_seeded x 0
  have h1 := branching_source_species_seeded x 1
  unfold branchingOldPotential
  rw [branching_source_gen_add]
  linarith

theorem branching_source_old_seed_free (x : BranchingSource)
    (hf : ∀ i : SiteId, 16 ≤ ((x i).a 0).val ∧ 16 ≤ ((x i).a 1).val) :
    FunctionalCapacity.cf3Gen (literalSourcePar 0) branchingOldPotential x ≤
      -branchingOldPotential x/2+8*(13/10000000) := by
  have h0 := branching_source_species_seed_free x 0 (fun i => (hf i).1)
  have h1 := branching_source_species_seed_free x 1 (fun i => (hf i).2)
  unfold branchingOldPotential
  rw [branching_source_gen_add]
  linarith

theorem branching_witness_le_species (x : BranchingSource) (i : SiteId) (j : SpeciesId) :
    branchingWitness ((x i).a j).val (x i).R ≤ branchingSpeciesPotential j x :=
  Finset.single_le_sum (f := fun k : SiteId => branchingWitness ((x k).a j).val (x k).R)
    (fun k _ => branching_witness_nonnegative ((x k).a j).val (x k).R) (Finset.mem_univ i)

theorem branching_species_le_all (x : BranchingSource) (j : SpeciesId) :
    branchingSpeciesPotential j x ≤ branchingAllPotential x :=
  Finset.single_le_sum (fun k _ => branching_species_nonnegative x k) (Finset.mem_univ j)

theorem branching_all_underfloor_barrier (x : BranchingSource)
    (i : SiteId) (j : SpeciesId) (hf : ((x i).a j).val < 16) :
    1 ≤ branchingAllPotential x := by
  have hq := branching_underfloor_barrier ((x i).a j).val hf (x i).R
  have h : (1 : ℝ) ≤ branchingWitness ((x i).a j).val (x i).R := by
    unfold branchingWitness
    exact_mod_cast hq
  exact h.trans ((branching_witness_le_species x i j).trans (branching_species_le_all x j))

theorem branching_species_max (x : BranchingSource) (j : SpeciesId) :
    branchingSpeciesPotential j x ≤ 320 := by
  have h (i : SiteId) : branchingWitness ((x i).a j).val (x i).R ≤ 80 := by
    unfold branchingWitness
    exact_mod_cast branching_witness_max ((x i).a j).val (x i).R
  calc
    _ ≤ ∑ _i : SiteId, (80 : ℝ) := Finset.sum_le_sum (fun i _ => h i)
    _ = 320 := by norm_num

-- As in the site cast, unfold the real-order instance diamond for elaboration.
set_option backward.isDefEq.respectTransparency false in
theorem branching_species_prepared (x : BranchingSource) (j : SpeciesId)
    (hf : ∀ i : SiteId, 512 ≤ ((x i).a j).val) :
    branchingSpeciesPotential j x ≤ 24/100000000 := by
  have h (i : SiteId) : branchingWitness ((x i).a j).val (x i).R ≤ 6/100000000 := by
    unfold branchingWitness
    have hq := (Rat.cast_le (K := ℝ)).mpr (branching_prepared_upper _ (hf i) (x i).R)
    push_cast at hq
    exact hq
  calc
    _ ≤ ∑ _i : SiteId, (6/100000000 : ℝ) := Finset.sum_le_sum (fun i _ => h i)
    _ = 24/100000000 := by norm_num

theorem branching_initial_old_bound (x : BranchingSource)
    (hf : ∀ i : SiteId, 512 ≤ ((x i).a 0).val ∧ 512 ≤ ((x i).a 1).val) :
    branchingOldPotential x ≤ 48/100000000 := by
  have h0 := branching_species_prepared x 0 (fun i => (hf i).1)
  have h1 := branching_species_prepared x 1 (fun i => (hf i).2)
  unfold branchingOldPotential
  linarith

end
end P161Formal
