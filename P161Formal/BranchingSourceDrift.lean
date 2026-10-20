module

public import P161Formal.BranchingSourceParameters
public import P161Formal.BranchingBoundary

/-! The beta4m scalar certificate instantiated at the actual chemical and
division generator, with arbitrary natural ledgers and both daughter slots. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev BranchingSource := CTMCHeredity20261019.SourceState (literalSourcePar 0)

def branchingSpeciesPotential (j : SpeciesId) (x : BranchingSource) : ℝ :=
  ∑ i : SiteId, branchingWitness ((x i).a j).val (x i).R

theorem branching_witness_nonnegative (a : ℕ) (fuel : Bool) :
    0 ≤ branchingWitness a fuel :=
  Rat.cast_nonneg.mpr (branching_witness_positive a fuel).le

theorem branching_source_H_decomposition (seed : ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    4000000*(branchingForeignUQ s j : ℝ)+(branchingForeignVQ s j : ℝ) =
      FunctionalCapacity.Hf (literalSourcePar seed) s j := by
  rw [←branching_foreign_H_cast seed s j]
  simp [branchingForeignVQ]

-- Permit the imported real-order instance diamond to unfold during elaboration.
-- This only affects definitional unification; the resulting term is kernel checked.
set_option backward.isDefEq.respectTransparency false in
theorem branching_source_site_seeded (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    FunctionalCapacity.siteOp (literalSourcePar 6) branchingWitness (s.a j).val s.R
      (FunctionalCapacity.Hf (literalSourcePar 6) s j) (FunctionalCapacity.Uf s j) ≤
        -branchingWitness (s.a j).val s.R/2+13/10000000 := by
  obtain ⟨hU0,hU1,hv0,hv1⟩ := branching_foreign_load_bounds s j
  have h := branching_seeded_scalar_drift (s.a j).val (by have := (s.a j).isLt; omega)
    s.R (branchingForeignUQ s j) (branchingForeignVQ s j) hU0 hU1 hv0 hv1
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  rw [branching_site_operator_cast,branching_source_H_decomposition 6,
    branching_foreign_U_cast] at hr
  simpa [branchingWitness] using hr

set_option backward.isDefEq.respectTransparency false in
theorem branching_source_site_seed_free (s : FunctionalCapacity.Site 3 2048)
    (j : SpeciesId) (hf : 16 ≤ (s.a j).val) :
    FunctionalCapacity.siteOp (literalSourcePar 0) branchingWitness (s.a j).val s.R
      (FunctionalCapacity.Hf (literalSourcePar 0) s j) (FunctionalCapacity.Uf s j) ≤
        -branchingWitness (s.a j).val s.R/2+13/10000000 := by
  obtain ⟨hU0,hU1,_hv0,hv1⟩ := branching_foreign_load_bounds s j
  have h := branching_seed_free_live_scalar_drift (s.a j).val hf
    (by have := (s.a j).isLt; omega) s.R (branchingForeignUQ s j)
      (branchingForeignVQ s j) hU0 hU1 hv1
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  rw [branching_site_operator_cast,branching_source_H_decomposition 0,
    branching_foreign_U_cast] at hr
  simpa [branchingWitness] using hr

theorem branching_source_species_drift (seed : ℝ) (hs : 0 ≤ seed)
    (x : BranchingSource) (j : SpeciesId)
    (hsite : ∀ i : SiteId,
      FunctionalCapacity.siteOp (literalSourcePar seed) branchingWitness ((x i).a j).val (x i).R
        (FunctionalCapacity.Hf (literalSourcePar seed) (x i) j)
        (FunctionalCapacity.Uf (x i) j) ≤ -branchingWitness ((x i).a j).val (x i).R/2+13/10000000) :
    FunctionalCapacity.cf3Gen (literalSourcePar seed) (branchingSpeciesPotential j) x ≤
      -branchingSpeciesPotential j x/2+4*(13/10000000) := by
  have h := FunctionalCapacity.cf3Gen_species_le (literal_source_valid seed hs) j
    branchingWitness branching_witness_nonnegative x
  refine h.trans ((Finset.sum_le_sum (fun i _ => hsite i)).trans_eq ?_)
  simp only [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    branchingSpeciesPotential]
  norm_num

theorem branching_source_species_seeded (x : BranchingSource) (j : SpeciesId) :
    FunctionalCapacity.cf3Gen (literalSourcePar 6) (branchingSpeciesPotential j) x ≤
      -branchingSpeciesPotential j x/2+4*(13/10000000) :=
  branching_source_species_drift 6 (by norm_num) x j
    (fun i => branching_source_site_seeded (x i) j)

theorem branching_source_species_seed_free (x : BranchingSource) (j : SpeciesId)
    (hf : ∀ i : SiteId, 16 ≤ ((x i).a j).val) :
    FunctionalCapacity.cf3Gen (literalSourcePar 0) (branchingSpeciesPotential j) x ≤
      -branchingSpeciesPotential j x/2+4*(13/10000000) :=
  branching_source_species_drift 0 le_rfl x j
    (fun i => branching_source_site_seed_free (x i) j (hf i))

end
end P161Formal
