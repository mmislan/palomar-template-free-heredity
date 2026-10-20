module

public import P161Formal.SourceResetAverage
public import Mathlib.Logic.Equiv.Fin.Basic

/-! The signed C11 certificate closes the actual complete-mark reset gain
on every current floor16, nonready source state. It is a generator bound;
the stopped physical-time probability and full mission remain separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev sourceCoordinateEquiv : (SiteId × SpeciesId) ≃ Fin 12 := finProdFinEquiv

theorem source_coordinate_sum (f : SiteId × SpeciesId → ℝ) :
    (∑ n : Fin 12, f (sourceCoordinateEquiv.symm n)) =
      ∑ i : SiteId, ∑ j : SpeciesId, f (i,j) := by
  rw [sourceCoordinateEquiv.symm.sum_comp,Fintype.sum_prod_type]

theorem source_direct_reset_gain_bound (x : RecoverySource) (hlive : recoverySourceLive x) :
    sourceResetGain x ≤ strongResetDirect*sourcePotential strongRecoveryWitness x ∧
      sourceResetGain x < 478*sourcePotential strongRecoveryWitness x := by
  classical
  let loc : Fin 12 → SiteId × SpeciesId := sourceCoordinateEquiv.symm
  let a (n : Fin 12) := ((x (loc n).1).a (loc n).2).val
  let fuel (n : Fin 12) := (x (loc n).1).R
  let X (n : Fin 12) := resetTableLower (a n) (fuel n)
  let H (n : Fin 12) := strongRecoveryWitness (a n) (fuel n)
  let Y (n : Fin 12) := resetTableGain (a n) (fuel n)
  have ha (n : Fin 12) : 16 ≤ a n := hlive.1 (loc n).1 (loc n).2 True.intro
  have hb (n : Fin 12) : a n ≤ 2048 := by
    have h : a n < 2049 := ((x (loc n).1).a (loc n).2).isLt
    omega
  have hH : (∑ n : Fin 12, H n) = sourcePotential strongRecoveryWitness x := by
    exact source_coordinate_sum (fun ij => strongRecoveryWitness ((x ij.1).a ij.2).val (x ij.1).R)
  have hY : (∑ n : Fin 12, Y n) =
      ∑ i : SiteId, ∑ j : SpeciesId, resetTableGain ((x i).a j).val (x i).R := by
    exact source_coordinate_sum (fun ij => resetTableGain ((x ij.1).a ij.2).val (x ij.1).R)
  have hX (n : Fin 12) : strongResetEll*X n ≤ H n := by
    simpa only [strongResetEll,X,H] using (strong_table_comparison (a n) (fuel n) (ha n) (hb n)).1
  have hpos : 0 < ∑ n : Fin 12, H n := by
    rw [hH,source_selected_potential_eq]
    have h := strong_nonready_barrier (sourcePopulation x) hlive.1 hlive.2
    have hr : (1 : ℝ) ≤ (strongPopulationPotentialQ (sourcePopulation x) : ℝ) := by exact_mod_cast h
    linarith
  have hex : ∃ i j, ((x i).a j).val < 512 := by
    by_contra hn
    apply hlive.2
    intro i j
    by_contra hsmall
    change ¬512 ≤ ((x i).a j).val at hsmall
    exact hn ⟨i,j,by omega⟩
  obtain ⟨i0,j0,hsmall⟩ := hex
  let n0 : Fin 12 := sourceCoordinateEquiv (i0,j0)
  have ha0 : a n0 = ((x i0).a j0).val := by
    simp only [a,loc,n0,Equiv.symm_apply_apply]
  have hlow : Y n0-strongResetD*X n0 ≤ resetLow := by
    exact deficient_reset_table_residual (a n0) (fuel n0) (ha n0) (by rw [ha0]; exact hsmall)
  have hall (n : Fin 12) : Y n-strongResetD*X n ≤ resetAll :=
    global_reset_table_residual (a n) (fuel n) (ha n) (hb n)
  have hsource : sourceResetGain x ≤ 8*(∑ n : Fin 12, H n)+∑ n : Fin 12, Y n := by
    rw [hH,hY]
    exact source_reset_gain_table_bound x
  have h := strong_direct_reset_bound X H Y (sourceResetGain x) n0 hX hpos hlow hall hsource
  rwa [hH] at h

end
end P161Formal
