module

public import P161Formal.SourceResetPointwise

/-! Average of the actual complete-division bound. Split, trigger and victim
weights are the literal source weights. The postmark floor test is retained
in the daughter estimate before averaging. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem paired_table_moment_nonnegative (a : ℕ) : 0 ≤ pairedTableMoment a := by
  change 0 ≤ (pairedTableMomentQ a : ℝ)
  rw [paired_table_moment_real_sum a]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · positivity
  · exact profile_entry_nonnegative _ false

def sourceDivisionChannelGain (x : RecoverySource) (i : SiteId) (k : Option SpeciesId) : ℝ :=
  ∑ o : FunctionalCapacity.Split 3 2048,
    (FunctionalCapacity.cf3 (literalSourcePar 0)).ps
      ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) o *
      ∑ v : SiteId, CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v *
        killedRecoveryPotential
          (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v)

def sourceChannelUntouched (x : RecoverySource) (i : SiteId) : ℝ :=
  ∑ v : SiteId, CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v *
    sourceUntouchedFor x i v

theorem source_division_channel_gain_bound (x : RecoverySource) (i : SiteId)
    (k : Option SpeciesId) :
    sourceDivisionChannelGain x i k ≤
      sourceChannelUntouched x i + ∑ j : SpeciesId, 2*pairedTableMoment ((x i).a j).val := by
  let s := (FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k
  have hconst (c : ℝ) :
      (∑ v : SiteId, CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v*c) = c := by
    rw [←Finset.sum_mul,CTMCHeredity20261019.CF3Marked.victimWeight_sum
      (literal_source_valid 0 (by norm_num))]
    exact one_mul c
  have hvsum (o : FunctionalCapacity.Split 3 2048) :
      (∑ v : SiteId, CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v*
        killedRecoveryPotential
          (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v)) ≤
        sourceChannelUntouched x i+∑ j : SpeciesId, sourcePairedDaughterTable s j o := by
    have hp (v : SiteId) :
        CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v*
          killedRecoveryPotential
            (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v) ≤
        CTMCHeredity20261019.CF3Marked.victimWeight (literalSourcePar 0) i v*
          (sourceUntouchedFor x i v+∑ j : SpeciesId, sourcePairedDaughterTable s j o) := by
      by_cases hv : v = i
      · simp [CTMCHeredity20261019.CF3Marked.victimWeight,hv]
      · exact mul_le_mul_of_nonneg_left (source_killed_division_pointwise x i v k o hv)
          (CTMCHeredity20261019.CF3Marked.victimWeight_nonneg
            (literal_source_valid 0 (by norm_num)) i v)
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hp v)
    simp only [mul_add,Finset.sum_add_distrib] at h
    rw [hconst] at h
    exact h
  have houter := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hvsum o) (FunctionalCapacity.cf3_ps_nonneg s o))
  have hcounts : s.a = (x i).a := by cases k <;> rfl
  have havg : (∑ o : FunctionalCapacity.Split 3 2048,
      (FunctionalCapacity.cf3 (literalSourcePar 0)).ps s o*
        ∑ j : SpeciesId, sourcePairedDaughterTable s j o) =
      ∑ j : SpeciesId, 2*pairedTableMoment ((x i).a j).val := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [source_paired_daughter_average,hcounts]
  have hfixed : (∑ o : FunctionalCapacity.Split 3 2048,
      (FunctionalCapacity.cf3 (literalSourcePar 0)).ps s o*sourceChannelUntouched x i) =
      sourceChannelUntouched x i := by
    rw [←Finset.sum_mul,FunctionalCapacity.cf3_ps_sum (p := literalSourcePar 0) s,one_mul]
  simp only [mul_add,Finset.sum_add_distrib] at houter
  rw [hfixed,havg] at houter
  exact houter

def sourceResetGain (x : RecoverySource) : ℝ :=
  ∑ i : SiteId, ∑ k : Option SpeciesId,
    (FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) k*sourceDivisionChannelGain x i k

theorem source_reset_gain_table_bound (x : RecoverySource) :
    sourceResetGain x ≤ 8*sourcePotential strongRecoveryWitness x +
      ∑ i : SiteId, ∑ j : SpeciesId, resetTableGain ((x i).a j).val (x i).R := by
  have hrd (i : SiteId) :
      (∑ k : Option SpeciesId, (FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) k) =
        siteDivisionIntensity (sourcePopulation x) i := by
    simp only [Fintype.sum_option,siteDivisionIntensity,contract_division_rate_is_source]
  have hparent (i : SiteId) :
      (∑ k : Option SpeciesId, (FunctionalCapacity.cf3 (literalSourcePar 0)).rd (x i) k*
        sourceDivisionChannelGain x i k) ≤
      siteDivisionIntensity (sourcePopulation x) i*sourceChannelUntouched x i +
        ∑ j : SpeciesId, resetTableGain ((x i).a j).val (x i).R := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (source_division_channel_gain_bound x i k)
        (FunctionalCapacity.cf3_rd_nonneg (x i) k))
    rw [←Finset.sum_mul,hrd,mul_add,Finset.mul_sum] at h
    refine le_trans h (add_le_add le_rfl ?_)
    apply Finset.sum_le_sum
    intro j _
    have hm := mul_le_mul_of_nonneg_right (source_parent_rate_selected_bound x i j)
      (paired_table_moment_nonnegative ((x i).a j).val)
    unfold resetTableGain
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hparent i)
  rw [Finset.sum_add_distrib] at hsum
  have huntouched : (∑ i : SiteId,
      siteDivisionIntensity (sourcePopulation x) i*sourceChannelUntouched x i) =
        sourceUntouchedResetGain x := by
    norm_num [sourceChannelUntouched,sourceUntouchedFor,sourceUntouchedResetGain,
      CTMCHeredity20261019.CF3Marked.victimWeight,literalSourcePar,ite_mul]
  rw [huntouched] at hsum
  have h8 := source_untouched_reset_gain_bound x
  exact le_trans hsum (add_le_add h8 le_rfl)

end
end P161Formal
