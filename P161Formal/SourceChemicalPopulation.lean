module

public import P161Formal.SourceChemicalRecovery
public import P161Formal.SourceIntensity

/-! Population chemical drift and the killed nonreset recovery bound, on the
literal source with arbitrary natural service/division ledgers. Actual resets
are excluded here by their full intensity; their positive gain is separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev RecoverySource := CTMCHeredity20261019.SourceState (literalSourcePar 0)

def sourcePotential (H : ℕ → Bool → ℝ) (x : RecoverySource) : ℝ :=
  ∑ i : SiteId, ∑ j : SpeciesId, H ((x i).a j).val (x i).R

def sourceChemicalGenerator (F : RecoverySource → ℝ) (x : RecoverySource) : ℝ :=
  ∑ i : SiteId, ∑ k,
    (FunctionalCapacity.cf3 (literalSourcePar 0)).rc (x i) k *
      (F (Function.update x i ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k))-F x)

theorem source_chemical_generator_potential (H : ℕ → Bool → ℝ) (x : RecoverySource) :
    sourceChemicalGenerator (sourcePotential H) x =
      ∑ i : SiteId, ∑ j : SpeciesId, sourceChemicalCoordinateDrift H (x i) j := by
  have hupdate (i : SiteId) (k : FunctionalCapacity.Chem 3) :
      sourcePotential H (Function.update x i
        ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k))-sourcePotential H x =
      ∑ j : SpeciesId,
        (H (((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k).a j).val
          ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k).R -
            H ((x i).a j).val (x i).R) := by
    unfold sourcePotential
    rw [FunctionalCapacity.sum_update_apply
      (fun s => ∑ j : SpeciesId, H (s.a j).val s.R) x i
        ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k),
      add_sub_cancel_left,Finset.sum_sub_distrib]
  unfold sourceChemicalGenerator
  simp_rw [hupdate,Finset.mul_sum]
  unfold sourceChemicalCoordinateDrift
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem source_selected_potential_eq (x : RecoverySource) :
    sourcePotential strongRecoveryWitness x =
      (strongPopulationPotentialQ (sourcePopulation x) : ℝ) := by
  simp [sourcePotential,strongPopulationPotentialQ,strongRecoveryWitness]

theorem source_selected_potential_nonnegative (x : RecoverySource) :
    0 ≤ sourcePotential strongRecoveryWitness x := by
  rw [source_selected_potential_eq]
  exact Rat.cast_nonneg.mpr (strong_population_nonnegative (sourcePopulation x))

theorem source_recovery_chemical_population_bound (x : RecoverySource)
    (hfloor : floorFor (sourcePopulation x) (fun _ => True)) :
    sourceChemicalGenerator (sourcePotential strongRecoveryWitness) x +
      220*sourcePotential strongRecoveryWitness x ≤ 12/4700 := by
  have hcell (i : SiteId) (j : SpeciesId) :
      sourceChemicalCoordinateDrift strongRecoveryWitness (x i) j +
        220*strongRecoveryWitness ((x i).a j).val (x i).R ≤ 1/4700 := by
    have h := source_recovery_chemical_bound (x i) j (hfloor i j True.intro)
    split_ifs at h <;> linarith
  calc
    _ = ∑ i : SiteId, ∑ j : SpeciesId,
        (sourceChemicalCoordinateDrift strongRecoveryWitness (x i) j +
          220*strongRecoveryWitness ((x i).a j).val (x i).R) := by
      rw [source_chemical_generator_potential,sourcePotential]
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ∑ _i : SiteId, ∑ _j : SpeciesId, (1/4700 : ℝ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcell i j))
    _ = 12/4700 := by norm_num

def recoverySourceLive (x : RecoverySource) : Prop :=
  floorFor (sourcePopulation x) (fun _ => True) ∧ ¬ready512 (sourcePopulation x)

def killedRecoveryPotential (x : RecoverySource) : ℝ := by
  classical
  exact if recoverySourceLive x then sourcePotential strongRecoveryWitness x else 0

theorem killed_recovery_potential_le (x : RecoverySource) :
    killedRecoveryPotential x ≤ sourcePotential strongRecoveryWitness x := by
  unfold killedRecoveryPotential
  split_ifs
  · exact le_rfl
  · exact source_selected_potential_nonnegative x

theorem source_killed_chemical_le (x : RecoverySource) (hlive : recoverySourceLive x) :
    sourceChemicalGenerator killedRecoveryPotential x ≤
      sourceChemicalGenerator (sourcePotential strongRecoveryWitness) x := by
  have hcurrent : killedRecoveryPotential x = sourcePotential strongRecoveryWitness x := by
    simp only [killedRecoveryPotential,ite_eq_left hlive]
  unfold sourceChemicalGenerator
  rw [hcurrent]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left
  · linarith [killed_recovery_potential_le
      (Function.update x i ((FunctionalCapacity.cf3 (literalSourcePar 0)).tc (x i) k))]
  · exact FunctionalCapacity.cf3_rc_nonneg (literal_source_valid 0 (by norm_num)) (x i) k

def sourceActualDivisionIntensity (x : RecoverySource) : ℝ :=
  ∑ i : SiteId, siteDivisionIntensity (sourcePopulation x) i

theorem source_actual_division_intensity_eq (x : RecoverySource) :
    sourceActualDivisionIntensity x =
      ∑ i : SiteId, ((FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) none +
        ∑ j : SpeciesId, (FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) (some j)) := by
  simp only [sourceActualDivisionIntensity,siteDivisionIntensity,contract_division_rate_is_source]

def sourceKilledNonresetDrift (x : RecoverySource) : ℝ :=
  sourceChemicalGenerator killedRecoveryPotential x -
    sourceActualDivisionIntensity x*sourcePotential strongRecoveryWitness x

theorem source_killed_nonreset_recovery_bound (x : RecoverySource)
    (hlive : recoverySourceLive x) :
    sourceKilledNonresetDrift x ≤
      -(263197/1175 : ℝ)*sourcePotential strongRecoveryWitness x := by
  have hchem := source_recovery_chemical_population_bound x hlive.1
  have hkill := source_killed_chemical_le x hlive
  have hnu : 4 ≤ sourceActualDivisionIntensity x :=
    (total_division_intensity_bounds (sourcePopulation x)).1
  have hpos := source_selected_potential_nonnegative x
  have hbarrier : 1 ≤ sourcePotential strongRecoveryWitness x := by
    rw [source_selected_potential_eq]
    exact_mod_cast strong_nonready_barrier (sourcePopulation x) hlive.1 hlive.2
  have hmul := mul_le_mul_of_nonneg_right hnu hpos
  unfold sourceKilledNonresetDrift
  nlinarith

end
end P161Formal
