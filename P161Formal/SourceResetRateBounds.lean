module

public import P161Formal.SourceChemicalPopulation
public import P161Formal.ResetTableResidual

/-! Exact source division-rate bounds and the uniform distinct-victim
contribution of untouched sites. The full postmark-floor reset operator is
still a separate bound. State-null actual division marks retain their rates. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem source_parent_rate_selected_bound (x : RecoverySource) (i : SiteId) (j : SpeciesId) :
    siteDivisionIntensity (sourcePopulation x) i ≤
      resetParentRateBound ((x i).a j).val (x i).R := by
  have hrest : (∑ k ∈ Finset.univ.erase j, copies (sourcePopulation x) i k/2048) ≤ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ.erase j)
      (fun k _ => show copies (sourcePopulation x) i k/2048 ≤ 1 by
        have hh := (copies_bounds (sourcePopulation x) i k).2
        linarith)
    have hcard : (Finset.univ.erase j).card = 2 := by simp
    norm_num only [Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_ofNat,mul_one] at h
    exact h
  have heq := Finset.sum_erase_eq_sub (s := Finset.univ)
    (f := fun k => copies (sourcePopulation x) i k/2048) (Finset.mem_univ j)
  have hfull : (∑ k : SpeciesId, copies (sourcePopulation x) i k/2048) ≤
      copies (sourcePopulation x) i j/2048+2 := by linarith
  cases hR : (x i).R
  · simp [siteDivisionIntensity,divisionRate,fueled,resetParentRateBound,hR]
  · simp [siteDivisionIntensity,divisionRate,fueled,resetParentRateBound,copies,hR]
    dsimp [copies] at hfull
    linarith

theorem uniform_untouched_identity (nu u : SiteId → ℝ) :
    (∑ i : SiteId, nu i * ∑ v : SiteId,
      if v = i then 0 else (1/3 : ℝ)*
        ∑ k : SiteId, if k = i ∨ k = v then 0 else u k) =
      (2/3 : ℝ)*∑ i : SiteId, ((∑ k : SiteId, nu k)-nu i)*u i := by
  simp [Fin.sum_univ_four]
  ring

def sourceSitePotential (x : RecoverySource) (i : SiteId) : ℝ :=
  ∑ j : SpeciesId, strongRecoveryWitness ((x i).a j).val (x i).R

theorem source_site_potential_nonnegative (x : RecoverySource) (i : SiteId) :
    0 ≤ sourceSitePotential x i := by
  apply Finset.sum_nonneg
  intro j _
  exact Rat.cast_nonneg.mpr (strong_coordinate_nonnegative ((x i).a j).val (x i).R
    (by have h : ((x i).a j).val < 2049 := ((x i).a j).isLt; omega))

def sourceUntouchedResetGain (x : RecoverySource) : ℝ :=
  ∑ i : SiteId, siteDivisionIntensity (sourcePopulation x) i *
    ∑ v : SiteId, if v = i then 0 else (1/3 : ℝ)*
      ∑ k : SiteId, if k = i ∨ k = v then 0 else sourceSitePotential x k

theorem source_untouched_reset_gain_bound (x : RecoverySource) :
    sourceUntouchedResetGain x ≤ 8*sourcePotential strongRecoveryWitness x := by
  have hother (i : SiteId) : sourceActualDivisionIntensity x-
      siteDivisionIntensity (sourcePopulation x) i ≤ 12 := by
    have h := Finset.sum_le_sum (s := Finset.univ.erase i)
      (fun k _ => (site_division_intensity_bounds (sourcePopulation x) k).2)
    have hcard : (Finset.univ.erase i).card = 3 := by simp
    norm_num only [Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_ofNat] at h
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h
    exact h
  unfold sourceUntouchedResetGain
  rw [uniform_untouched_identity]
  calc
    _ ≤ (2/3 : ℝ)*∑ i : SiteId, 12*sourceSitePotential x i := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hother i) (source_site_potential_nonnegative x i)
    _ = 8*sourcePotential strongRecoveryWitness x := by
      rw [←Finset.mul_sum]
      unfold sourcePotential sourceSitePotential
      ring

end
end P161Formal
