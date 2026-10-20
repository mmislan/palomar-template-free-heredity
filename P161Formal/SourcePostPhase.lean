module

public import P161Formal.SourceBranchingTicks
public import P161Formal.SourceDivisionWitness
public import P161Formal.ServiceSourceBarrier

/-! The seed-free300-block source lower bound, with the literal floor,
500-credit quotas and five initiating divisions per spatial site. This is
an operator predecessor; the switched path-event identity is docked later. -/

@[expose] public section
namespace P161Formal
open FunctionalCapacity CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

def literalPostSourceValue (x : BranchingSource) : ℝ :=
  blocks (literalSourceKilled 0 le_rfl (sourceDead 16 Finset.univ))
    (cf3Rate (literalSourcePar 0)*(1/10)) (sourceOkS 500 Finset.univ)
    (sourceResetQ (p := literalSourcePar 0)) 300 (sourceFinalD 5)
    (sourceResetAll (p := literalSourcePar 0) x)

theorem source_final_division_bdd : Bdd (sourceFinalD (p := literalSourcePar 0) 5) := by
  apply Bdd.of_le (c := 1)
  · intro x
    unfold sourceFinalD
    split_ifs <;> norm_num
  · intro x
    unfold sourceFinalD
    split_ifs <;> norm_num

theorem source_post_division_tick (x : BranchingSource) :
    (literalSourceKilled 0 le_rfl (sourceDead 16 Finset.univ)).P sourceDivisionPotential x ≤
      (1-(5/6)/cf3Rate (literalSourcePar 0))*sourceDivisionPotential x := by
  have h := source_killed_tick_super 0 le_rfl (sourceDead 16 Finset.univ)
    sourceDivisionPotential (5/6) 0 (fun y => (source_division_potential_bounds y).1)
    (by rw [source_common_clock.2]; norm_num) le_rfl
    (by
      intro y _hy
      simpa only [add_zero] using source_division_potential_drift 0 le_rfl y) x
  simpa only [zero_div,add_zero] using h

theorem literal_post_value_bdd : Bdd literalPostSourceValue := by
  have hmu : 0 ≤ cf3Rate (literalSourcePar 0)*(1/10) :=
    mul_nonneg (literal_source_clock_positive 0 le_rfl).le (by norm_num)
  exact Bdd.comp (blocks_bdd
    (literalSourceKilled 0 le_rfl (sourceDead 16 Finset.univ)) hmu
    (sourceOkS 500 Finset.univ) (sourceResetQ (p := literalSourcePar 0))
    source_final_division_bdd 300) (sourceResetAll (p := literalSourcePar 0))

theorem source_post_phase_lower (x : BranchingSource) :
    1-branchingAllPotential x-5184*Real.exp (-25)-
      300*((6/5 : ℝ)*(13/10000000)+1/100000000) ≤ literalPostSourceValue x := by
  let L : ℝ := cf3Rate (literalSourcePar 0)
  let K := literalSourceKilled 0 le_rfl (sourceDead 16 Finset.univ)
  let s : Finset (SiteId × SpeciesId) := Finset.univ ×ˢ Finset.univ
  have hL : 0 < L := literal_source_clock_positive 0 le_rfl
  have hmu : 0 ≤ L*(1/10) := mul_nonneg hL.le (by norm_num)
  have hND : (5/6 : ℝ) ≤ L := by
    dsimp only [L]
    rw [source_common_clock.2]
    norm_num
  have hS : serviceTheta ≤ L := literal_source_clock_large 0 le_rfl
  have h := blocks_lower K hmu (sourceOkS 500 Finset.univ)
    (sourceResetQ (p := literalSourcePar 0)) s
    (fun k => sourceServicePotential k.1 k.2)
    (Φ := branchingAllPotential)
    (V := sourceDivisionPotential) (F := sourceFinalD 5)
    (BΦ := 960) (BV := 4) (bΦ := 12*(13/10000000)/L) (bV := 0)
    (θV := (5/6)/L) (θs := serviceTheta/L) (cV := 1296)
    (A := serviceBarrierScale) (E0 := 0)
    branching_all_nonnegative branching_all_max (branching_all_reset_q 0)
    (div_nonneg (by norm_num) hL.le) source_post_guard_tick
    (fun y => (source_division_potential_bounds y).1)
    (fun y => (source_division_potential_bounds y).2) (source_division_reset_q 0)
    (div_nonneg (by norm_num) hL.le) ((div_le_one hL).mpr hND) le_rfl
    (by intro y; simpa only [add_zero] using source_post_division_tick y)
    (fun k _hk y => (source_service_potential_bounds k.1 k.2 y).1.le)
    (fun k _hk y => (source_service_potential_bounds k.1 k.2 y).2.1)
    (div_nonneg (by norm_num [serviceTheta]) hL.le) ((div_le_one hL).mpr hS)
    (fun k _hk y => source_killed_service_tick 0 le_rfl Finset.univ k.1 k.2
      (Finset.mem_univ _) y)
    service_barrier_scale_nonnegative (source_service_quota_detector Finset.univ)
    (by norm_num) le_rfl source_final_division_bdd
    (by intro y; simpa only [sub_zero] using source_division_terminal_lower y)
    300 (sourceResetAll (p := literalSourcePar 0) x)
  have hc : s.card = 12 := by simp [s]
  have hV : (5/6 : ℝ)/L*(L*(1/10))*300 = 25 := by
    norm_num [L,cf3Rate,literalSourcePar]
  have hY : serviceTheta/L*(L*(1/10)) = 165 := by
    norm_num [L,cf3Rate,literalSourcePar,serviceTheta]
  have hb : (12*(13/10000000) : ℝ)/L*(L*(1/10)) = (6/5)*(13/10000000) := by
    norm_num [L,cf3Rate,literalSourcePar]
  simp only [Nat.cast_ofNat,branching_all_reset_all,source_division_reset_all,
    hc,hV,hY,hb,zero_mul,mul_zero,add_zero,sub_zero] at h
  have hsrv : serviceBarrierScale*(12*Real.exp (-165)) ≤ 1/100000000 := by
    have ht := service_block_error_twelve
    rw [show serviceTheta*(1/10) = (165 : ℝ) by norm_num [serviceTheta]] at ht
    exact ht
  change 1-branchingAllPotential x-1296*(Real.exp (-25)*4)-
    300*((6/5 : ℝ)*(13/10000000)+serviceBarrierScale*(12*Real.exp (-165))) ≤
      literalPostSourceValue x at h
  linarith

end
end P161Formal
